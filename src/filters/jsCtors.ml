(*
	The Haxe Compiler
	Copyright (C) 2005-2019  Haxe Foundation

	This program is free software; you can redistribute it and/or
	modify it under the terms of the GNU General Public License
	as published by the Free Software Foundation; either version 2
	of the License, or (at your option) any later version.

	This program is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with this program; if not, write to the Free Software
	Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
*)
open Common
open Type
open Globals

let has_this_before_super e = 
	let accessed_this = ref false in
	let called_super = ref false in
	let rec loop e =
		match e.eexpr with 
		| TCall ({ eexpr = TConst TSuper },_) ->
			called_super := true;
			raise Exit
		| TConst TThis ->
			accessed_this := true;
			raise Exit
		| _ ->
			Type.iter loop e
	in
	try begin
		loop e;
		false
	end with Exit ->
		!accessed_this && not !called_super

let mk_static_ctor_name (pack,name) = 
	let n = match pack with
		| [] -> name
		| _ -> (String.concat "_" pack) ^ "_" ^ name
	in
	"_hx_ctor_" ^ n

let make_filters com =
	let msize = List.length com.types in
	let calls_parent_static_ctor = Hashtbl.create msize in
	let needs_static_ctor = Hashtbl.create msize in

	let mark t =
		match t with
		| TClassDecl ({ cl_constructor = Some { cf_expr = Some ctor_expr }; cl_super = Some (cl_super,_) } as cl) ->
			if has_this_before_super ctor_expr then begin
				Hashtbl.add calls_parent_static_ctor cl.cl_path true;
				Hashtbl.add needs_static_ctor cl_super.cl_path true
			end
		| _ ->
			()
	in

	let change ctx t =
		match t with
		| TClassDecl ({ cl_constructor = Some ({ cf_expr = Some ({ eexpr = TFunction ctor_tf } as ctor_expr) } as ctor) } as cl) ->
			let needs_static_ctor = Hashtbl.mem needs_static_ctor cl.cl_path in
			let calls_parent_static_ctor = Hashtbl.mem calls_parent_static_ctor cl.cl_path in

			if calls_parent_static_ctor then begin
				let cl_super,cl_super_params = Option.get cl.cl_super in
				let parent_static_ctor_name = mk_static_ctor_name cl_super.cl_path in

				let p = ctor_expr.epos in

				let static_ctor_expr =
					let e = mk (TTypeExpr (TClassDecl cl_super)) t_dynamic p in
					let e = mk (TField (e, FDynamic parent_static_ctor_name)) t_dynamic p in
					e
				in
				
				let rec loop e =
					match e.eexpr with 
					| TCall ({ eexpr = TConst TSuper }, args) -> 
						{ e with eexpr = TCall (static_ctor_expr, args) }
					| _ -> Type.map_expr loop e 
				in
				let expr = loop ctor_tf.tf_expr in


				let eemptysuper =
					let esuper = mk (TConst TSuper) t_dynamic p in
					let eempty = mk (TIdent "EMPTY") t_dynamic p in
					mk (TCall (esuper, [eempty])) com.basic.tvoid p
				in
				
				let expr = Type.concat eemptysuper expr in

				ctor.cf_expr <- Some { ctor_expr with
					eexpr = TFunction { ctor_tf with tf_expr = expr }
				}
			end;

			if needs_static_ctor then begin
				let static_ctor_name = mk_static_ctor_name cl.cl_path in
				let static_ctor_t = ctor.cf_type in

				let static_ctor = mk_field static_ctor_name static_ctor_t ctor.cf_pos ctor.cf_name_pos in 
				static_ctor.cf_kind <- Method MethNormal;
				static_ctor.cf_expr <- Some ctor_expr;

				cl.cl_ordered_statics <- static_ctor :: cl.cl_ordered_statics;
				cl.cl_statics <- PMap.add static_ctor_name static_ctor cl.cl_statics;

				let p = ctor_expr.epos in

				let static_ctor_apply_expr =
					let e = mk (TTypeExpr t) t_dynamic p in
					let e = mk (TField (e, FStatic (cl, static_ctor))) t_dynamic p in
					let e = mk (TField (e, FDynamic "apply")) t_dynamic p in
					e
				in
				let static_ctor_expr_apply_args = 
					[mk (TConst TThis) t_dynamic p]
				in
				
				ctor.cf_expr <- Some { ctor_expr with
					eexpr = TFunction { ctor_tf with
						tf_expr = { ctor_tf.tf_expr with
							eexpr = TBlock [
								mk (TIdent "__empty_ctor_check__") t_dynamic p;
								mk (TCall (static_ctor_apply_expr, static_ctor_expr_apply_args)) com.basic.tvoid p
							]
						}
					}
				};

				Common.add_feature com "js.empty"
			end;

			if needs_static_ctor || calls_parent_static_ctor then begin
				Printf.printf "%s %b %b\n" (s_type_path cl.cl_path) needs_static_ctor calls_parent_static_ctor
			end
		| _ -> ()
	in

	mark, change


import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSection

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier

namespace GlobalTheory.FlagChi

variable {Z : Scheme.{0}} [IsIntegral Z] {N : ℕ}

def genVec {V : Z.Opens} (h : genericPoint Z ∈ V) (v : Fin N → Γ(Z, V)) :
    Fin N → Z.functionField :=
  fun a => fnOf V h (v a)

theorem genVec_res {V W : Z.Opens} (e : W ≤ V) (h : genericPoint Z ∈ W) (v : Fin N → Γ(Z, V)) :
    genVec h (fun a => resG Z e (v a)) = genVec (e h) v :=
  funext fun a => fnOf_resG e h (v a)

theorem genVec_add {V : Z.Opens} (h : genericPoint Z ∈ V) (v w : Fin N → Γ(Z, V)) :
    genVec h (v + w) = genVec h v + genVec h w :=
  funext fun a => map_add _ _ _

theorem genVec_zero {V : Z.Opens} (h : genericPoint Z ∈ V) :
    genVec h (0 : Fin N → Γ(Z, V)) = 0 :=
  funext fun _ => map_zero _

theorem genVec_smul {V : Z.Opens} (h : genericPoint Z ∈ V) (c : Γ(Z, V)) (v : Fin N → Γ(Z, V)) :
    genVec h (c • v) = fnOf V h c • genVec h v :=
  funext fun a => by simp only [genVec, Pi.smul_apply, smul_eq_mul, map_mul]

theorem genVec_smul_germ {V : Z.Opens} (h : genericPoint Z ∈ V) {x : Z} (hx : x ∈ V) (c : Γ(Z, V))
    (v : Fin N → Γ(Z, V)) : genVec h (c • v) = Z.presheaf.germ V x hx c • genVec h v := by
  rw [genVec_smul, ← algebraMap_germ hx c, algebraMap_smul]

theorem eq_zero_of_genVec {V : Z.Opens} {v : Fin N → Γ(Z, V)}
    (hv : ∀ h : genericPoint Z ∈ V, genVec h v = 0) : v = 0 :=
  funext fun a => fn_ext fun h => (congrFun (hv h) a).trans (map_zero _).symm

variable (C : ∀ x : Z, Submodule (Z.presheaf.stalk x) (Fin N → Z.functionField))

def vsec (V : Z.Opens) : Submodule Γ(Z, V) (Fin N → Γ(Z, V)) where
  carrier := {v | ∀ (h : genericPoint Z ∈ V) (x : Z) (hx : x ∈ V), genVec h v ∈ C x}
  add_mem' {v w} hv hw h x hx := by
    rw [genVec_add]; exact add_mem (hv h x hx) (hw h x hx)
  zero_mem' h x hx := by
    rw [genVec_zero]; exact zero_mem _
  smul_mem' c v hv h x hx := by
    rw [genVec_smul_germ h hx]; exact (C x).smul_mem _ (hv h x hx)

theorem res_mem_vsec {V W : Z.Opens} (e : W ≤ V) {v : Fin N → Γ(Z, V)} (hv : v ∈ vsec C V) :
    (fun a => resG Z e (v a)) ∈ vsec C W := fun h x hx => by
  rw [genVec_res e h]; exact hv (e h) x (e hx)

def vres {V W : Z.Opens} (e : W ≤ V) : vsec C V →+ vsec C W where
  toFun s := ⟨fun a => resG Z e (s.1 a), res_mem_vsec C e s.2⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)

theorem vres_smul {V W : Z.Opens} (e : W ≤ V) (c : Γ(Z, V)) (m : vsec C V) :
    vres C e (c • m) = resG Z e c • vres C e m :=
  Subtype.ext (funext fun _ => map_mul _ _ _)

def presheaf : TopCat.Presheaf Ab.{0} Z where
  obj V := AddCommGrpCat.of (vsec C V.unop)
  map f := AddCommGrpCat.ofHom (vres C (leOfHom f.unop))
  map_id V := by
    ext s a
    exact LB.resG_self _ _
  map_comp f g := by
    ext s a
    exact (LB.resG_resG _ _ _).symm

theorem isSheaf_presheaf : (presheaf C).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  have H (a : Fin N) : ∃ b : Γ(Z, iSup W), ∀ k, resG Z (le_iSup W k) b = (sf k).1 a :=
    LB.exists_fun_of_cover W (le_iSup W) le_rfl (fun k => (sf k).1 a) fun k l =>
      congrFun (congrArg Subtype.val (hsf k l)) a
  choose b hb using H
  refine ⟨⟨b, fun h x hx => ?_⟩, fun k => Subtype.ext (funext fun a => hb a k), fun t ht =>
    Subtype.ext (funext fun a => LB.fun_ext_of_cover W (le_iSup W) le_rfl fun k => ?_)⟩
  · obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hx
    have hg : genericPoint Z ∈ W k := gen_mem hk
    have e : (sf k).1 = fun a => resG Z (le_iSup W k) (b a) := funext fun a => (hb a k).symm
    have := (sf k).2 hg x hk
    rwa [e, genVec_res] at this
  · exact (congrFun (congrArg Subtype.val (ht k)) a).trans (hb a k).symm

def vmod : Z.Modules :=
  letI : ∀ V, Module (Z.ringCatSheaf.obj.obj V) ((presheaf C).obj V) :=
    fun V => inferInstanceAs (Module Γ(Z, V.unop) (vsec C V.unop))
  { val := PresheafOfModules.ofPresheaf (presheaf C) fun _ _ f r m =>
      vres_smul C (leOfHom f.unop) r m
    isSheaf := isSheaf_presheaf C }

variable {C}

def vec {V : Z.Opens} (s : Γ(vmod C, V)) : Fin N → Γ(Z, V) := (show vsec C V from s).1

theorem vec_mem {V : Z.Opens} (s : Γ(vmod C, V)) : vec s ∈ vsec C V := (show vsec C V from s).2

def mk {V : Z.Opens} (v : Fin N → Γ(Z, V)) (hv : v ∈ vsec C V) : Γ(vmod C, V) :=
  (⟨v, hv⟩ : vsec C V)

@[simp] theorem vec_mk {V : Z.Opens} (v : Fin N → Γ(Z, V)) (hv : v ∈ vsec C V) :
    vec (mk v hv) = v := rfl

theorem sec_ext {V : Z.Opens} {s t : Γ(vmod C, V)} (h : vec s = vec t) : s = t := Subtype.ext h

@[simp] theorem vec_add {V : Z.Opens} (s t : Γ(vmod C, V)) : vec (s + t) = vec s + vec t := rfl

@[simp] theorem vec_smul {V : Z.Opens} (c : Γ(Z, V)) (s : Γ(vmod C, V)) : vec (c • s) = c • vec s := rfl

@[simp] theorem vec_map {V W : Z.Opens} (e : W ≤ V) (s : Γ(vmod C, V)) :
    vec ((vmod C).presheaf.map (homOfLE e).op s) = fun a => resG Z e (vec s a) := rfl

@[simp] theorem vec_zero {V : Z.Opens} : vec (0 : Γ(vmod C, V)) = 0 := rfl

variable {C' : ∀ x : Z, Submodule (Z.presheaf.stalk x) (Fin N → Z.functionField)}

def vmap (hC : ∀ x, C x ≤ C' x) : vmod C ⟶ vmod C' :=
  LB.homOfLinear (F := vmod C) (G := vmod C')
    (fun V => Submodule.inclusion (fun v hv h x hx => hC x (hv h x hx) : vsec C V ≤ vsec C' V))
    fun _ _ => rfl

@[simp] theorem vec_vmap_app (hC : ∀ x, C x ≤ C' x) {V : Z.Opens} (s : Γ(vmod C, V)) :
    vec ((vmap hC).app V s) = vec s := rfl

def vmapOf (h : ∀ V, vsec C V ≤ vsec C' V) : vmod C ⟶ vmod C' :=
  LB.homOfLinear (F := vmod C) (G := vmod C') (fun V => Submodule.inclusion (h V)) fun _ _ => rfl

def viso (h : ∀ V, vsec C V = vsec C' V) : vmod C ≅ vmod C' :=
  LB.isoOfLinear (F := vmod C) (G := vmod C') (fun V => LinearEquiv.ofEq _ _ (h V)) fun _ _ => rfl

open Classical in

def ofRat (U : Z.Opens) (f : Z.functionField) (hf : ∀ x ∈ U, RegAt x f) : Γ(Z, U) :=
  if h : genericPoint Z ∈ U then (exists_fnOf_eq h hf).choose else 0

theorem fnOf_ofRat {U : Z.Opens} {f : Z.functionField} (hf : ∀ x ∈ U, RegAt x f)
    (h : genericPoint Z ∈ U) : fnOf U h (ofRat U f hf) = f := by
  classical
  rw [ofRat, dif_pos h]; exact (exists_fnOf_eq h hf).choose_spec

open Classical in

def genVal {V : Z.Opens} (v : Fin N → Γ(Z, V)) : Fin N → Z.functionField :=
  if h : genericPoint Z ∈ V then genVec h v else 0

theorem genVal_eq {V : Z.Opens} (h : genericPoint Z ∈ V) (v : Fin N → Γ(Z, V)) :
    genVal v = genVec h v := by
  classical
  exact dif_pos h

variable (L : LB Z) (r : L.ι → Z.functionFieldˣ)
  (φ : (Fin N → Z.functionField) →ₗ[Z.functionField] Z.functionField)

theorem regAt_proj (hC : ∀ x w, w ∈ C x → ∀ c, x ∈ L.U c → RegAt x (φ w * r c)) {V : Z.Opens}
    (s : Γ(vmod C, V)) (c : L.ι) : ∀ x ∈ V ⊓ L.U c, RegAt x (φ (genVal (vec s)) * r c) :=
  fun x hx => by
    rw [genVal_eq (gen_mem hx.1)]
    exact hC x _ (vec_mem s (gen_mem hx.1) x hx.1) c hx.2

def projCoord (hC : ∀ x w, w ∈ C x → ∀ c, x ∈ L.U c → RegAt x (φ w * r c)) {V : Z.Opens}
    (s : Γ(vmod C, V)) (c : L.ι) : Γ(Z, V ⊓ L.U c) :=
  ofRat _ _ (regAt_proj L r φ hC s c)

theorem fnOf_projCoord (hC : ∀ x w, w ∈ C x → ∀ c, x ∈ L.U c → RegAt x (φ w * r c))
    {V : Z.Opens} (s : Γ(vmod C, V)) (c : L.ι) (h : genericPoint Z ∈ V ⊓ L.U c) :
    fnOf _ h (projCoord L r φ hC s c) = φ (genVec h.1 (vec s)) * r c := by
  rw [projCoord, fnOf_ofRat, genVal_eq h.1]

theorem projCoord_mem (hr : IsRatSec L r)
    (hC : ∀ x w, w ∈ C x → ∀ c, x ∈ L.U c → RegAt x (φ w * r c)) {V : Z.Opens}
    (s : Γ(vmod C, V)) : (fun c => projCoord L r φ hC s c) ∈ secOn L V := by
  intro c c'
  refine Cartier.fn_ext fun h => ?_
  rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, fnOf_projCoord, fnOf_projCoord,
    hr c c' ⟨h.1.2, h.2⟩]
  ring

def projLin (hr : IsRatSec L r) (hC : ∀ x w, w ∈ C x → ∀ c, x ∈ L.U c → RegAt x (φ w * r c))
    (V : Z.Opens) : Γ(vmod C, V) →ₗ[Γ(Z, V)] Γ(LB.toMod L, V) where
  toFun s := LB.mkSec (fun c => projCoord L r φ hC s c) (projCoord_mem L r φ hr hC s)
  map_add' s t := LB.sec_ext fun c => Cartier.fn_ext fun h => by
    simp only [LB.coord_add, LB.coord_mkSec, map_add, fnOf_projCoord, vec_add, genVec_add, add_mul]
  map_smul' a s := LB.sec_ext fun c => Cartier.fn_ext fun h => by
    simp only [LB.coord_smul, LB.coord_mkSec, RingHom.id_apply, map_mul, fnOf_resG,
      fnOf_projCoord, vec_smul, genVec_smul, map_smul, smul_eq_mul, mul_assoc]

theorem coord_projLin (hr : IsRatSec L r)
    (hC : ∀ x w, w ∈ C x → ∀ c, x ∈ L.U c → RegAt x (φ w * r c)) {V : Z.Opens}
    (s : Γ(vmod C, V)) (c : L.ι) : LB.coord (projLin L r φ hr hC V s) c = projCoord L r φ hC s c :=
  rfl

def vproj (hr : IsRatSec L r) (hC : ∀ x w, w ∈ C x → ∀ c, x ∈ L.U c → RegAt x (φ w * r c)) :
    vmod C ⟶ LB.toMod L :=
  LB.homOfLinear (F := vmod C) (G := LB.toMod L) (projLin L r φ hr hC) fun {V W} e s =>
    LB.sec_ext fun c => Cartier.fn_ext fun h => by
      simp only [LB.coord_map, coord_projLin, fnOf_resG, fnOf_projCoord, vec_map, genVec_res]

theorem fnOf_coord_vproj (hr : IsRatSec L r)
    (hC : ∀ x w, w ∈ C x → ∀ c, x ∈ L.U c → RegAt x (φ w * r c)) {V : Z.Opens}
    (s : Γ(vmod C, V)) (c : L.ι) (h : genericPoint Z ∈ V ⊓ L.U c) :
    fnOf _ h (LB.coord ((vproj L r φ hr hC).app V s) c) = φ (genVec h.1 (vec s)) * r c :=
  fnOf_projCoord L r φ hC s c h

open Matrix

def stepSub (M : Matrix (Fin N) (Fin N) Z.functionField) (l : ℕ) :
    Submodule Z.functionField (Fin N → Z.functionField) where
  carrier := {v | ∀ k : Fin N, l ≤ (k : ℕ) → (M *ᵥ v) k = 0}
  add_mem' {v w} hv hw k hk := by rw [Matrix.mulVec_add, Pi.add_apply, hv k hk, hw k hk, add_zero]
  zero_mem' k _ := by rw [Matrix.mulVec_zero, Pi.zero_apply]
  smul_mem' a v hv k hk := by rw [Matrix.mulVec_smul, Pi.smul_apply, hv k hk, smul_zero]

def stepC (M : Matrix (Fin N) (Fin N) Z.functionField) (l : ℕ) (x : Z) :
    Submodule (Z.presheaf.stalk x) (Fin N → Z.functionField) :=
  (stepSub M l).restrictScalars _

def quotC (M : Matrix (Fin N) (Fin N) Z.functionField) (l : Fin N) (L : LB Z)
    (r : L.ι → Z.functionFieldˣ) (x : Z) : Submodule (Z.presheaf.stalk x) (Fin N → Z.functionField) where
  carrier := {v | v ∈ stepSub M ((l : ℕ) + 1) ∧ ∀ c, x ∈ L.U c → RegAt x ((M *ᵥ v) l * r c)}
  add_mem' {v w} hv hw := ⟨add_mem hv.1 hw.1, fun c hc => by
    rw [Matrix.mulVec_add, Pi.add_apply, add_mul]; exact (hv.2 c hc).add (hw.2 c hc)⟩
  zero_mem' := ⟨zero_mem _, fun c _ => by
    rw [Matrix.mulVec_zero, Pi.zero_apply, zero_mul]; exact regAt_zero x⟩
  smul_mem' a v hv := ⟨(stepSub M ((l : ℕ) + 1)).smul_of_tower_mem a hv.1, fun c hc => by
    rw [← algebraMap_smul Z.functionField a v, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
      mul_assoc]
    exact RegAt.mul ⟨a, rfl⟩ (hv.2 c hc)⟩

abbrev stepMod (M : Matrix (Fin N) (Fin N) Z.functionField) (l : ℕ) : Z.Modules := vmod (stepC M l)

abbrev quotMod (M : Matrix (Fin N) (Fin N) Z.functionField) (l : Fin N) (L : LB Z)
    (r : L.ι → Z.functionFieldˣ) : Z.Modules := vmod (quotC M l L r)

def coordFn (M : Matrix (Fin N) (Fin N) Z.functionField) (l : Fin N) :
    (Fin N → Z.functionField) →ₗ[Z.functionField] Z.functionField :=
  (LinearMap.proj l).comp (Matrix.mulVecLin M)

@[simp] theorem coordFn_apply (M : Matrix (Fin N) (Fin N) Z.functionField) (l : Fin N)
    (v : Fin N → Z.functionField) : coordFn M l v = (M *ᵥ v) l := rfl

theorem stepC_le_quotC (M : Matrix (Fin N) (Fin N) Z.functionField) (l : Fin N) (L : LB Z)
    (r : L.ι → Z.functionFieldˣ) (x : Z) : stepC M l x ≤ quotC M l L r x := fun v hv =>
  ⟨fun k hk => hv k (by omega), fun c _ => by
    rw [hv l le_rfl, zero_mul]; exact regAt_zero x⟩

theorem quotC_le_stepC (M : Matrix (Fin N) (Fin N) Z.functionField) (l : Fin N) (L : LB Z)
    (r : L.ι → Z.functionFieldˣ) (x : Z) : quotC M l L r x ≤ stepC M ((l : ℕ) + 1) x :=
  fun _ hv => hv.1

def stepIncl (M : Matrix (Fin N) (Fin N) Z.functionField) (l : Fin N) (L : LB Z)
    (r : L.ι → Z.functionFieldˣ) : stepMod M l ⟶ quotMod M l L r :=
  vmap (stepC_le_quotC M l L r)

def quotIncl (M : Matrix (Fin N) (Fin N) Z.functionField) (l : Fin N) (L : LB Z)
    (r : L.ι → Z.functionFieldˣ) : quotMod M l L r ⟶ stepMod M ((l : ℕ) + 1) :=
  vmap (quotC_le_stepC M l L r)

def stepProj (M : Matrix (Fin N) (Fin N) Z.functionField) (l : Fin N) {L : LB Z}
    {r : L.ι → Z.functionFieldˣ} (hr : IsRatSec L r) : quotMod M l L r ⟶ LB.toMod L :=
  vproj L r (coordFn M l) hr fun x w hw c hc =>
    (show RegAt x (coordFn M l w * r c) from hw.2 c hc)

theorem stepIncl_stepProj (M : Matrix (Fin N) (Fin N) Z.functionField) (l : Fin N) {L : LB Z}
    {r : L.ι → Z.functionFieldˣ} (hr : IsRatSec L r) : stepIncl M l L r ≫ stepProj M l hr = 0 := by
  ext V s : 3
  refine LB.sec_ext fun c => Cartier.fn_ext fun h => ?_
  change fnOf _ h (LB.coord ((stepProj M l hr).app V ((stepIncl M l L r).app V s)) c) =
    fnOf _ h (LB.coord (0 : Γ(LB.toMod L, V)) c)
  rw [stepProj, fnOf_coord_vproj, LB.coord_zero, map_zero, coordFn_apply]
  show (M *ᵥ genVec h.1 (vec s)) l * _ = 0
  rw [(vec_mem s h.1 _ h.1 : genVec h.1 (vec s) ∈ stepSub M l) l le_rfl, zero_mul]

def stepSeq (M : Matrix (Fin N) (Fin N) Z.functionField) (l : Fin N) {L : LB Z}
    {r : L.ι → Z.functionFieldˣ} (hr : IsRatSec L r) : ShortComplex Z.Modules :=
  ShortComplex.mk (stepIncl M l L r) (stepProj M l hr) (stepIncl_stepProj M l hr)

end GlobalTheory.FlagChi

import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TopForm Formalism.BasicNotions
open scoped ComplexOrder

namespace GlobalTheory.TrueGeo

namespace Res

section Val

variable {K K' : Type} [Field K] [Field K'] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) {f g : Z.functionField}

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h, IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec]

variable {y}

theorem valAt_add (hf : RegAt (below y) f) (hg : RegAt (below y) g) : valAt y (f + g) = valAt y f + valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_add, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_add]

theorem valAt_mul (hf : RegAt (below y) f) (hg : RegAt (below y) g) : valAt y (f * g) = valAt y f * valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

theorem valAt_pow (hf : RegAt (below y) f) (m : ℕ) : valAt y (f ^ m) = valAt y f ^ m := by
  obtain ⟨a, rfl⟩ := hf
  rw [← map_pow, valAt_algebraMap, valAt_algebraMap, map_pow]

theorem regAt_pow {x : Z} (hf : RegAt x f) (m : ℕ) : RegAt x (f ^ m) :=
  have ⟨a, ha⟩ := hf; ⟨a ^ m, by rw [map_pow, ha]⟩

theorem valAt_ne_zero (hf : UnitAt (below y) f) : valAt y f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [valAt_algebraMap]
  exact (ha.map _).ne_zero

variable (y)

theorem valAt_zero : valAt y 0 = 0 := by
  rw [← map_zero (algebraMap (Z.presheaf.stalk (below y)) Z.functionField), valAt_algebraMap, map_zero]

theorem valAt_one : valAt y 1 = 1 := by
  rw [← map_one (algebraMap (Z.presheaf.stalk (below y)) Z.functionField), valAt_algebraMap, map_one]

omit [IsIntegral Z] in

theorem below_comp (φ : K →+* K') : below (spMap φ ≫ y) = below y := by
  exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg y (Subsingleton.elim (α := PrimeSpectrum K) _ _))

theorem valAt_comp (φ : K →+* K') (f : Z.functionField) : valAt (spMap φ ≫ y) f = φ (valAt y f) := by
  by_cases h : RegAt (below y) f
  · obtain ⟨U, hU, a, rfl⟩ := h.exists_fnOf
    have hU' : below (spMap φ ≫ y) ∈ U := (below_comp y φ).symm ▸ hU
    have e : spMap φ ≫ y =
        Spec.map (Scheme.stalkClosedPointTo y ≫ CommRingCat.ofHom φ) ≫ Z.fromSpecStalk (below y) := by
      rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    have : IsLocalHom (Scheme.stalkClosedPointTo y ≫ CommRingCat.ofHom φ).hom := by
      rw [CommRingCat.hom_comp]
      exact RingHom.isLocalHom_comp φ _
    conv_rhs => rw [← algebraMap_germ hU a, valAt_algebraMap]
    rw [← algebraMap_germ hU' a, valAt_algebraMap]
    revert hU'
    rw [e]
    intro hU'
    exact congrArg (fun q => q.hom a) (Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
      (Scheme.stalkClosedPointTo y ≫ CommRingCat.ofHom φ) U hU')
  · rw [valAt, valAt, dif_neg h, dif_neg ((below_comp y φ).symm ▸ h), map_zero]

variable {y} in

theorem valAt_fnOf {U : Z.Opens} (hy : below y ∈ U) (h : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    valAt y (fnOf U h a) = TangentOrigin.evalPt y U ((Points.le_preimage_iff _ _).2 hy) a := by
  rw [← algebraMap_germ hy a, valAt_algebraMap]
  exact congrArg (fun q => q.hom a) (Scheme.germ_stalkClosedPointTo y U hy)

theorem ratVal_eq_valAt {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ} (z : CxPts q σ)
    (hf : RegAt (under z) f) : ratVal f z = valAt z.1 f := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  rw [ratVal_fnOf (CxPts.mem_ptsIn.2 hU), valAt_fnOf hU, CxPts.ev_eq (CxPts.mem_ptsIn.2 hU)]
  rfl

theorem valAt_const {k : Type} [Field k] {Y : Var k} {y : Sp K ⟶ Y.X} {φ : k →+* K} (h : y ≫ Y.str = spMap φ) (a : k) :
    valAt y (algebraMap k Y.Fn a) = φ a := by
  rw [IsScalarTower.algebraMap_apply k Γ(Y.X, ⊤) Y.Fn]
  refine (valAt_fnOf (U := ⊤) trivial trivial _).trans ?_
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have e' : (y.appTop).hom (algebraMap k Γ(Y.X, ⊤) a) = (Scheme.ΓSpecIso (.of K)).inv.hom (φ a) := by
    refine Eq.trans ?_ e.symm
    change ((y ≫ Y.str).appTop).hom _ = ((spMap φ).appTop).hom _
    rw [h]
  refine Eq.trans (congrArg (Scheme.ΓSpecIso (.of K)).hom.hom (Eq.trans ?_ e')) (Iso.inv_hom_id_apply _ _)
  exact congrArg (fun q => q.hom (algebraMap k Γ(Y.X, ⊤) a)) (Scheme.Hom.appLE_eq_app y (U := ⊤))

end Val

end Res

open Res

variable {F : Type} [Field F] [NumberField F] (Y : Var F)

def jacRat (u : Fin Y.dim → Y.Fn) : Y.Fn :=
  (isFreeGen_baseForm Y.str Y.dim).repr (dForm (Cartier.constFn Y.str) u)

variable (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ} (w : Fin n → Y.Fn)
  (c : Fin Y.dim → Fin n → 𝓞 E)

instance galAction : MulAction (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) (GeomPt Y E) where
  smul σ y := ⟨spMap (σ : AlgebraicClosure E →+* AlgebraicClosure E) ≫ y.1, by
    rw [Category.assoc, y.2, ← spMap_comp]
    exact congrArg spMap (RingHom.ext fun a => σ.commutes _)⟩
  one_smul y := Subtype.ext ((congrArg (· ≫ y.1) (Spec.map_id _)).trans (Category.id_comp _))
  mul_smul σ τ y := Subtype.ext (by
    change spMap _ ≫ y.1 = spMap _ ≫ spMap _ ≫ y.1
    rw [← Category.assoc, ← spMap_comp]
    rfl)

section Gal

variable {Y E} (σ : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) (y : GeomPt Y E)

omit [NumberField F] [NumberField E] in

theorem below_smul : below (σ • y).1 = below y.1 := below_comp _ _

omit [NumberField F] [NumberField E] in

theorem valAt_smul (f : Y.Fn) : valAt (σ • y).1 f = σ (valAt y.1 f) := valAt_comp _ _ _

omit [NumberField F] [NumberField E] [Algebra F E] in

theorem map_coef (i : Fin Y.dim) (l : Fin n) : σ (coef Y E c i l) = coef Y E c i l := σ.commutes _

omit [NumberField F] [NumberField E] in
variable {w c y} in

theorem smul_mem_cutSet (hy : y ∈ cutSet Y E w c) : σ • y ∈ cutSet Y E w c := fun k hk i => by
  have := congrArg σ (hy k (below_smul σ y ▸ hk) i)
  simpa only [map_sum, map_mul, map_coef, map_zero, valAt_smul] using this

end Gal

instance galActionCut : MulAction (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) (cutSet Y E w c) where
  smul σ y := ⟨σ • y.1, smul_mem_cutSet σ y.2⟩
  one_smul y := Subtype.ext (one_smul _ y.1)
  mul_smul σ τ y := Subtype.ext (mul_smul σ τ y.1)

def cutSec : Submodule E (cutSet Y E w c → AlgebraicClosure E) where
  carrier := {g | ∀ (σ : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) y, g (σ • y) = σ (g y)}
  zero_mem' _ _ := (map_zero _).symm
  add_mem' hf hg σ y := by rw [Pi.add_apply, Pi.add_apply, hf, hg, map_add]
  smul_mem' a g hg σ y := by rw [Pi.smul_apply, Pi.smul_apply, hg, Algebra.smul_def, Algebra.smul_def, map_mul, σ.commutes]

def dsVal (y : GeomPt Y E) (k : Fin n) (g : Y.Fn) : AlgebraicClosure E :=
  ∑ l : Fin Y.dim → Fin n, (∏ i, coef Y E c i (l i)) * valAt y.1 (jacRat Y (fun i => w (l i) / w k) * g)

def resAt (f : Y.Fn) (y : GeomPt Y E) (k : Fin n) (g e : Y.Fn) : AlgebraicClosure E :=
  valAt y.1 (f * e * g / w k ^ Y.dim) / dsVal Y E w c y k g

open Classical in

def genIdx (x : Y.X) : Option (Fin n) := if h : ∃ k, GenAt Y w x k then some h.choose else none

def resVal (Δ : Y.Dv) (f : Y.Fn) (y : GeomPt Y E) : AlgebraicClosure E :=
  (genIdx Y w (below y.1)).elim 0 fun k => resAt Y E w c f y k (eqn Y.KY (below y.1)) (eqn Δ (below y.1))

def ResReg (Δ : Y.Dv) (f : Y.Fn) (x : Y.X) : Prop :=
  ∃ k, GenAt Y w x k ∧ (Δ + Y.KY).RegularAt x (f / w k ^ Y.dim)

section Indep

variable {Y E w c} {x : Y.X} {y : GeomPt Y E} {k k' : Fin n} {g g' e : Y.Fnˣ} {Δ : Y.Dv} {f f' : Y.Fn}

omit [NumberField F] in

theorem GenAt.unitAt (h : GenAt Y w x k) (h' : GenAt Y w x k') : UnitAt x (w k / w k') :=
  (unitAt_iff (div_ne_zero h.1 h'.1)).2 ⟨h'.2 k, by rw [inv_div]; exact h.2 k'⟩

omit [NumberField F] in

theorem isEqn_eqn (Δ : Y.Dv) (x : Y.X) : Δ.IsEqn x (eqn Δ x) := (Δ.exists_isEqn x).choose_spec

omit [NumberField F] in

theorem ResReg.regAt (h : ResReg Y w Δ f x) (hk : GenAt Y w x k) (hg : Y.KY.IsEqn x g) (he : Δ.IsEqn x e) :
    RegAt x (f * e * g / w k ^ Y.dim) := by
  obtain ⟨k', hk', h⟩ := h
  have := ((he.add hg).regularAt_iff.1 h).mul (regAt_pow (hk.2 k') Y.dim)
  convert this using 1
  have := hk'.1
  rw [Units.val_mul, div_pow]
  field_simp

omit [NumberField F] [NumberField E] in

theorem dsVal_pick {l : Fin Y.dim → Fin n} (hc : ∀ i j, c i j = if j = l i then 1 else 0) (g : Y.Fn) :
    dsVal Y E w c y k g = valAt y.1 (jacRat Y (fun i => w (l i) / w k) * g) := by
  rw [dsVal, Finset.sum_eq_single l _ (by simp)]
  · simp [coef, hc]
  · intro l' _ hl
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hl
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [coef, hc, hi]), zero_mul]

omit [NumberField F] [NumberField E] in

example {l : Fin Y.dim → Fin n} (hc : ∀ i j, c i j = if j = l i then 1 else 0) (hk : GenAt Y w (below y.1) k)
    (hd : dsVal Y E w c y k g ≠ 0) :
    resAt Y E w c (w k ^ Y.dim * jacRat Y (fun i => w (l i) / w k) / e) y k g e = 1 := by
  have h0 := hk.1
  rw [resAt, div_eq_one_iff_eq hd, dsVal_pick hc]
  congr 1
  field_simp

omit [NumberField F] [NumberField E] in

theorem resVal_smul (σ : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) (Δ : Y.Dv) (f : Y.Fn) (y : GeomPt Y E) :
    resVal Y E w c Δ f (σ • y) = σ (resVal Y E w c Δ f y) := by
  rw [resVal, resVal, below_smul]
  cases genIdx Y w (below y.1) with
  | none => exact (map_zero σ).symm
  | some k => simp only [Option.elim, resAt, dsVal, valAt_smul, map_div₀, map_sum, map_mul, map_prod, map_coef]

end Indep

def resSec (Δ : Y.Dv) (f : Y.Fn) : cutSec Y E w c :=
  ⟨fun y => resVal Y E w c Δ f y.1, fun σ y => resVal_smul σ Δ f y.1⟩

section Herm

variable {Y E}

def cxPt {τ : E →+* ℂ} {τ' : AlgebraicClosure E →+* ℂ} (h : τ'.comp (algebraMap E _) = τ) (y : GeomPt Y E) :
    Pts Y (τ.comp (algebraMap F E)) :=
  ⟨spMap τ' ≫ y.1, by rw [Category.assoc, y.2, ← spMap_comp, ← RingHom.comp_assoc, h]⟩

variable {C : CxSt F} (A : Adl C Y)

def Adl.frameSq (σ : F →+* ℂ) (z : Pts Y σ) : ℝ :=
  Real.exp (-(2 * (A.n : ℕ) * A.ci (InfinitePlace.mk σ))) *
    C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D (under z))⁻¹ : Y.Fnˣ)) z

def cutFormAt {τ : E →+* ℂ} {τ' : AlgebraicClosure E →+* ℂ} (h : τ'.comp (algebraMap E _) = τ)
    (g g' : cutSec Y E w c) : ℂ :=
  ∑ᶠ y : cutSet Y E w c, τ' (g.1 y) * starRingEnd ℂ (τ' (g'.1 y)) * (A.frameSq _ (cxPt h y.1) : ℝ)

def cutForm (τ : E →+* ℂ) (g g' : cutSec Y E w c) : ℂ :=
  cutFormAt w c A (ComplexEmbedding.lift_comp_algebraMap (AlgebraicClosure E) τ) g g'

def IsCutHerm (H : ReciprocityTheory.GeometryOfNumbersTheory.HermFam E (cutSec Y E w c)) : Prop := ∀ τ g g', H.form τ g g' = cutForm w c A τ g' g

variable {w c A} in

theorem IsCutHerm.unique {H H' : ReciprocityTheory.GeometryOfNumbersTheory.HermFam E (cutSec Y E w c)} (h : IsCutHerm w c A H)
    (h' : IsCutHerm w c A H') : H = H' := by
  have e : H.form = H'.form := funext fun τ => funext fun g => funext fun g' => (h τ g g').trans (h' τ g g').symm
  cases H
  cases H'
  congr

open Classical in

def cutDeg (Λ : Submodule (𝓞 E) (cutSec Y E w c)) : ℝ :=
  if h : ∃ H, IsCutHerm w c A H then ReciprocityTheory.GeometryOfNumbersTheory.deg h.choose Λ else 0

end Herm

variable [StarRing F] (M0 : HLat F) (ι₀ : M0.V →ₗ[F] Y.Fn)

def resLat (Δ : Y.Dv) : Submodule (𝓞 E) (cutSec Y E w c) :=
  Submodule.span (𝓞 E) ((fun m => resSec Y E w c Δ (ι₀ m)) '' (M0.L : Set M0.V))

variable {C : CxSt F} (A : Adl C Y)

def resFull : Prop :=
  (∀ m ∈ M0.L, ∀ y ∈ cutSet Y E w c, ResReg Y w A.D (ι₀ m) (below y.1)) ∧ (resLat Y E w c M0 ι₀ A.D).FG ∧
    Submodule.span E (resLat Y E w c M0 ι₀ A.D : Set (cutSec Y E w c)) = ⊤

def resDeg : ℝ := cutDeg w c A (resLat Y E w c M0 ι₀ A.D)

def resSt (C : CxSt F) : ResSt C where
  resFull := fun Y E _ _ _ _ w c M0 ι₀ A => resFull Y E w c M0 ι₀ A
  resDeg := fun Y E _ _ _ _ w c M0 ι₀ A => resDeg Y E w c M0 ι₀ A

section OnePoint

variable {Y E w c} [Unique (cutSet Y E w c)]

end OnePoint

end GlobalTheory.TrueGeo

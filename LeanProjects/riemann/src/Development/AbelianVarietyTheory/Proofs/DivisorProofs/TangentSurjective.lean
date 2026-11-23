import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomOfDerivation

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open GlobalTheory.VB GlobalTheory.Conormal
open GlobalTheory.KS.DerMorK (deformHom hom_ext_appLE)

namespace GlobalTheory.LieVB.TangentSurj

section General

variable {S X T : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (p : T ⟶ S) (ε : Γ(T, ⊤)) (hε : ε * ε = 0)
  (D : Der π e (structureModule S))

def val {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) : Γ(X, W) →+ Γ(S, V) := D.app h

theorem val_mul {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) (f g : Γ(X, W)) :
    val D h (f * g) = e.appLE W V h f * val D h g + e.appLE W V h g * val D h f :=
  D.app_mul h f g

theorem val_base {W : X.Opens} {V U : S.Opens} (h : V ≤ e ⁻¹ᵁ W) (k : W ≤ π ⁻¹ᵁ U) (a : Γ(S, U)) :
    val D h (π.appLE U W k a) = 0 := D.app_base h k a

theorem val_one {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) : val D h 1 = 0 := by
  simpa using val_base D (U := ⊤) h le_top 1

theorem val_res {W W' : X.Opens} (k : W' ≤ W) (f : Γ(X, W)) :
    val D (le_refl (e ⁻¹ᵁ W')) (resG X k f) = resG S (e.preimage_mono k) (val D le_rfl f) :=
  (D.app_res _ k f).trans (D.res_app le_rfl (e.preimage_mono k) f).symm

include hε in

theorem res_sq (U : T.Opens) : resG T (le_top : U ≤ ⊤) ε * resG T (le_top : U ≤ ⊤) ε = 0 := by
  rw [← map_mul, hε, map_zero]

def psi (W : X.Opens) : Γ(X, W) →+* Γ(T, p ⁻¹ᵁ e ⁻¹ᵁ W) where
  toFun f := p.appLE _ _ le_rfl (e.appLE W _ le_rfl f) +
    p.appLE _ _ le_rfl (val D le_rfl f) * resG T le_top ε
  map_one' := by simp only [val_one, map_one, map_zero, zero_mul, add_zero]
  map_mul' f g := by
    simp only [val_mul, map_mul, map_add]
    linear_combination -(p.appLE _ _ le_rfl (val D le_rfl f) * p.appLE _ _ le_rfl (val D le_rfl g)) *
      res_sq ε hε (p ⁻¹ᵁ e ⁻¹ᵁ W)
  map_zero' := by simp only [map_zero, zero_mul, add_zero]
  map_add' f g := by
    simp only [map_add]
    ring

theorem psi_apply (W : X.Opens) (f : Γ(X, W)) : psi p ε hε D W f =
    p.appLE _ _ le_rfl (e.appLE W _ le_rfl f) +
      p.appLE _ _ le_rfl (val D le_rfl f) * resG T le_top ε := rfl

theorem psi_nat (W W' : X.Opens) (h : W' ≤ W) (f : Γ(X, W)) :
    psi p ε hε D W' (resG X h f) =
      resG T (p.preimage_mono (e.preimage_mono h)) (psi p ε hε D W f) := by
  rw [psi_apply, psi_apply, val_res, map_add, map_mul, resG_resG, resG_appLE, resG_appLE,
    appLE_resG e, appLE_resG p, ← resG_appLE e (e.preimage_mono h) le_rfl, appLE_resG p]

theorem psi_nil (W : X.Opens) (f : Γ(X, W)) :
    IsNilpotent (psi p ε hε D W f - p.appLE _ _ le_rfl (e.appLE W _ le_rfl f)) := by
  refine ⟨2, ?_⟩
  rw [psi_apply]
  linear_combination (p.appLE _ _ le_rfl (val D le_rfl f)) ^ 2 * res_sq ε hε (p ⁻¹ᵁ e ⁻¹ᵁ W)

def deform : T ⟶ X :=
  deformHom (p ≫ e) (psi p ε hε D) (psi_nat p ε hε D) fun W f => by
    have h : ((p ≫ e).app W).hom f = p.appLE _ _ le_rfl (e.appLE W _ le_rfl f) := by
      rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app]; rfl
    rw [h]
    exact psi_nil p ε hε D W f

theorem deform_appLE (W : X.Opens) {U : T.Opens} (k : U ≤ p ⁻¹ᵁ e ⁻¹ᵁ W) (f : Γ(X, W)) :
    (deform p ε hε D).appLE W U k f = resG T k (psi p ε hε D W f) := rfl

theorem deform_comp (he : e ≫ π = 𝟙 S) : deform p ε hε D ≫ π = p := by
  have h₀ : p ≫ e ≫ π = p := by rw [he, Category.comp_id]
  refine hom_ext_appLE (congr(($h₀).base)) fun U k => ?_
  ext a
  have k' : p ⁻¹ᵁ U ≤ p ⁻¹ᵁ e ⁻¹ᵁ π ⁻¹ᵁ U := k
  refine (appLE_appLE (f := deform p ε hε D) rfl le_rfl k' k a).symm.trans ?_
  rw [deform_appLE, psi_apply, val_base, map_zero, zero_mul, add_zero,
    appLE_base he _ _ ((le_preimage_iff he).1 le_rfl), appLE_resG, resG_appLE,
    Scheme.Hom.appLE_eq_app]

theorem comp_deform {z : S ⟶ T} (hz : z ≫ p = 𝟙 S) (h0 : z.appLE ⊤ ⊤ le_top ε = 0) :
    z ≫ deform p ε hε D = e := by
  have h₀ : z ≫ p ≫ e = e := by rw [reassoc_of% hz]
  refine hom_ext_appLE (congr(($h₀).base)) fun W k => ?_
  ext f
  have k' : e ⁻¹ᵁ W ≤ z ⁻¹ᵁ p ⁻¹ᵁ e ⁻¹ᵁ W := k
  refine (appLE_appLE (f := z) (g := deform p ε hε D) (V := p ⁻¹ᵁ e ⁻¹ᵁ W)
    rfl le_rfl k' k f).symm.trans ?_
  rw [deform_appLE, resG_self, psi_apply, map_add, map_mul, appLE_resG,
    ← resG_appLE z le_top le_top ε, h0, map_zero, mul_zero, add_zero,
    appLE_base hz _ _ le_rfl, resG_self, Scheme.Hom.appLE_eq_app]

end General

variable (O : Type) [CommRing O]

theorem epsFn_sq : epsFn O * epsFn O = 0 := by
  have h := map_mul (Scheme.ΓSpecIso (.of (DualNumber O))).inv.hom DualNumber.eps DualNumber.eps
  rw [DualNumber.eps_mul_eps, map_zero] at h
  exact h.symm

theorem epsZero_epsFn : (sec (epsZero O)).appLE ⊤ ⊤ le_top (epsFn O) = 0 := by
  refine congr($(Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom O O O).toRingHom)) DualNumber.eps).symm.trans ?_
  exact (congrArg (Scheme.ΓSpecIso (.of O)).inv.hom (DualNumber.fst_eps (R := O))).trans
    (map_zero _)

theorem tangent_surjective (O : Type) [CommRing O] (G : Over (Sp O)) [GrpObj G] :
    Function.Surjective (tangent : LieG G → Γ(Lie G, ⊤)) := by
  intro l
  let D := lieEquivDer G l
  let x : specO O (DualNumber O) ⟶ G :=
    Over.homMk (deform (specO O (DualNumber O)).hom (epsFn O) (epsFn_sq O) D)
      (deform_comp _ _ _ D (sec_hom η[G]))
  have hx : ptMap (TrivSqZeroExt.fstHom O O O) ≫ x = toUnit (specO O O) ≫ η[G] := by
    have h : (toUnit (specO O O)).left = 𝟙 (Sp O) := by
      rw [Over.toUnit_left]
      exact Spec.map_id _
    ext1
    simp only [Over.comp_left, h]
    exact (comp_deform _ _ (epsFn_sq O) D (sec_hom (epsZero O)) (epsZero_epsFn O)).trans
      (Category.id_comp _).symm
  refine ⟨⟨x, hx⟩, (homGlobalEquiv _ _).injective (omega_hom_ext fun W f => ?_)⟩
  refine dualApp_tangent_dUnit ⟨x, hx⟩ le_rfl f
    ((le_preimage_iff (sec_hom (epsZero O))).2 le_rfl) le_rfl le_rfl
    ((unitSec G).appLE W _ le_rfl f) (val D le_rfl f) ?_
  exact (deform_appLE _ _ (epsFn_sq O) D W le_rfl f).trans (resG_self _ _)

end GlobalTheory.LieVB.TangentSurj

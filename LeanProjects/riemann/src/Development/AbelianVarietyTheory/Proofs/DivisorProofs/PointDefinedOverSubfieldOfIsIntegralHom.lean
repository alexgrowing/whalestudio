import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DefOverIntegral

theorem mem_of_isIntegral {K : Type} [Field K] (k₀ : Subfield K) (hk : IsAlgClosed k₀) {x : K}
    (hx : IsIntegral k₀ x) : x ∈ k₀ := by
  obtain ⟨a, ha⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k₀)
    (K := integralClosure k₀ K)).2 ⟨x, hx⟩
  have h1 : ((algebraMap k₀ (integralClosure k₀ K) a : integralClosure k₀ K) : K) = x := congrArg Subtype.val ha
  have h2 : ((algebraMap k₀ (integralClosure k₀ K) a : integralClosure k₀ K) : K) = (a : K) := rfl
  rw [← h1, h2]
  exact a.2

theorem defOver_of_isIntegralHom : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] {K : Type} [Field K]
    (k₀ : Subfield K), IsAlgClosed k₀ → ∀ P : Sp K ⟶ X, GlobalTheory.UChart.DefOver k₀ (P ≫ f) → GlobalTheory.UChart.DefOver k₀ P := by
  intro X Y f _ K _ k₀ hk P ⟨Q₀, hQ⟩
  let g := pullback.snd f Q₀
  let Pt : Sp K ⟶ pullback f Q₀ := pullback.lift P (spMap k₀.subtype) hQ.symm
  haveI : IsAffine (pullback f Q₀) := isAffine_of_isAffineHom g
  have hint : (g.app ⊤).hom.IsIntegral := g.isIntegral_app ⊤ (isAffineOpen_top _)
  let φc : Γ(pullback f Q₀, ⊤) ⟶ CommRingCat.of K := Pt.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom
  have hPt : Pt = Spec.map φc ≫ (pullback f Q₀).isoSpec.inv := by
    have h := Scheme.isoSpec_inv_naturality Pt
    rw [Scheme.isoSpec_Spec_inv] at h
    rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]
  have hg : Pt ≫ g = spMap k₀.subtype := pullback.lift_snd _ _ _
  have hcomp : g.appTop ≫ φc = (Scheme.ΓSpecIso (CommRingCat.of k₀)).hom ≫ CommRingCat.ofHom k₀.subtype := by
    have h := congrArg Scheme.Hom.appTop hg
    rw [Scheme.Hom.comp_appTop] at h
    simp only [φc, ← Category.assoc, h]
    exact Scheme.ΓSpecIso_naturality _
  have hmem : ∀ r, φc.hom r ∈ k₀ := by
    intro r
    obtain ⟨p, hpm, hp⟩ := hint r
    refine mem_of_isIntegral k₀ hk ⟨p.map (Scheme.ΓSpecIso (CommRingCat.of k₀)).hom.hom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap k₀ K).comp (Scheme.ΓSpecIso (CommRingCat.of k₀)).hom.hom = φc.hom.comp (g.app ⊤).hom := by
      have := congrArg CommRingCat.Hom.hom hcomp
      exact this.symm
    rw [e]
    have h3 := Polynomial.hom_eval₂ p (g.app ⊤).hom φc.hom r
    rw [hp] at h3
    exact h3.symm.trans (RingHom.map_zero _)
  let φ₀ : Γ(pullback f Q₀, ⊤) →+* k₀ := φc.hom.codRestrict k₀ hmem
  refine ⟨Spec.map (CommRingCat.ofHom φ₀) ≫ (pullback f Q₀).isoSpec.inv ≫ pullback.fst f Q₀, ?_⟩
  have e2 : spMap k₀.subtype ≫ Spec.map (CommRingCat.ofHom φ₀) = Spec.map φc := by
    rw [spMap, ← Spec.map_comp]
    rfl
  rw [← Category.assoc, e2, ← Category.assoc, ← hPt]
  exact pullback.lift_fst _ _ _

end GlobalTheory.DefOverIntegral

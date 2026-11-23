import Mathlib
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.GenIdeal

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace ChowFormHeightComparison₂.CF

namespace PullbackComparison

variable {Y Z : Scheme.{0}} (i : Y ⟶ Z)

theorem resG_appLE {U : Z.Opens} {V V' : Y.Opens} (e : V ≤ i ⁻¹ᵁ U) (h : V' ≤ V) (a : Γ(Z, U)) :
    resG Y h ((i.appLE U V e).hom a) = (i.appLE U V' (h.trans e)).hom a := by
  rw [← Scheme.Hom.appLE_map i e (homOfLE h).op]
  rfl

theorem appLE_resG {U U' : Z.Opens} {V : Y.Opens} (e : V ≤ i ⁻¹ᵁ U') (h : U' ≤ U) (e' : V ≤ i ⁻¹ᵁ U) (a : Γ(Z, U)) :
    (i.appLE U' V e).hom (resG Z h a) = (i.appLE U V e').hom a := by
  rw [← Scheme.Hom.map_appLE i e (homOfLE h).op]
  rfl

theorem algX_comp {R : Type} [CommRing R] (p : Z ⟶ Sp R) {U : Z.Opens} {V : Y.Opens} (e : V ≤ i ⁻¹ᵁ U) (a : R) :
    algX (i ≫ p) V a = (i.appLE U V e).hom (algX p U a) := by
  simp only [algX, RingHom.comp_apply]
  rw [← Scheme.Hom.appLE_comp_appLE i p ⊤ U V (by simp) e]
  rfl

theorem surj_appLE [IsClosedImmersion i] {U : Z.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (e : V = i ⁻¹ᵁ U) :
    Function.Surjective (i.appLE U V e.le).hom := by
  subst e
  rw [Scheme.Hom.appLE_eq_app]
  exact i.app_surjective U hU

theorem eval_appLE {U : Z.Opens} {V : Y.Opens} (e : V ≤ i ⁻¹ᵁ U) (y : Y) (hy : y ∈ V) (a : Γ(Z, U)) :
    (Y.evaluation V y hy).hom ((i.appLE U V e).hom a) =
      (i.residueFieldMap y).hom ((Z.evaluation U (i y) (e hy)).hom a) := by
  refine Eq.trans ?_ (Scheme.evaluation_naturality_apply i y (e hy) a).symm
  simp only [Scheme.Hom.appLE, Scheme.evaluation, LocallyRingedSpace.evaluation, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_res_apply]

end PullbackComparison

open PullbackComparison

theorem stPull : StPull := by
  intro R _ Z Y p B m s i _ hE
  have hAR : ∀ {U U' : Z.Opens} {W : Y.Opens} (e : W ≤ i ⁻¹ᵁ U') (h : U' ≤ U) (a : Γ(Z, U)),
      (i.appLE U' W e).hom (resG Z h a) = (i.appLE U W (fun y hy => h (e hy))).hom a :=
    fun e h a => appLE_resG i e h _ a
  have hf : ∀ (t : B.Sec) (J : (B.pull i).ι), (GlobalTheory.secPull t i).f J =
      (i.appLE (B.U (J PUnit.unit)) ((B.pull i).U J) (GlobalTheory.LB.pull_U i J).le).hom (t.f (J PUnit.unit)) := by
    intro t J
    simp only [GlobalTheory.secPull, GlobalTheory.chartSec_f]
    rfl
  refine ⟨⟨LB.isLB_pull hE.isLB i, ?_, ?_⟩, ?_, ?_⟩
  · rw [eq_top_iff]
    intro y _
    have h : i y ∈ ⨆ k, nonzeroLocus (s k) := by rw [hE.cover]; trivial
    rw [TopologicalSpace.Opens.mem_iSup] at h ⊢
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [GlobalTheory.nonzeroLocus_secPull]; exact hk⟩
  · intro k
    obtain ⟨hAff, t, hsurj, hrel⟩ := hE.chart k
    have hV : nonzeroLocus (GlobalTheory.secPull (s k) i) = i ⁻¹ᵁ nonzeroLocus (s k) := GlobalTheory.nonzeroLocus_secPull _ _
    refine ⟨by rw [hV]; exact hAff.preimage i, fun j => (i.appLE _ _ hV.le).hom (t j), ?_, ?_⟩
    · have hcomp : eval₂Hom (algX (i ≫ p) (nonzeroLocus (GlobalTheory.secPull (s k) i)))
          (fun j => (i.appLE _ _ hV.le).hom (t j)) =
          (i.appLE _ _ hV.le).hom.comp (eval₂Hom (algX p (nonzeroLocus (s k))) t) := by
        apply MvPolynomial.ringHom_ext
        · intro a
          simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
          exact algX_comp i p hV.le a
        · intro j
          simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [hcomp]
      exact (surj_appLE i hAff hV).comp hsurj
    · intro j J
      have hle : nonzeroLocus (GlobalTheory.secPull (s k) i) ⊓ (B.pull i).U J ≤
          i ⁻¹ᵁ (nonzeroLocus (s k) ⊓ B.U (J PUnit.unit)) := by
        intro y hy
        exact ⟨hV.le hy.1, (GlobalTheory.LB.pull_U i J).le hy.2⟩
      have key := congrArg (i.appLE _ _ hle).hom (hrel j (J PUnit.unit))
      simp only [map_mul, hAR] at key
      simp only [hf, resG_appLE]
      exact key
  · intro y
    have hker : ∀ (J : (B.pull i).ι) (h : y ∈ (B.pull i).U J),
        RingHom.ker (coneHom (i ≫ p) (fun k => GlobalTheory.secPull (s k) i) y J h) =
          RingHom.ker (coneHom p s (i y) (J PUnit.unit) ((GlobalTheory.LB.pull_U i J).le h)) := by
      intro J h
      have heq : coneHom (i ≫ p) (fun k => GlobalTheory.secPull (s k) i) y J h =
          (Polynomial.mapRingHom (i.residueFieldMap y).hom).comp
            (coneHom p s (i y) (J PUnit.unit) ((GlobalTheory.LB.pull_U i J).le h)) := by
        apply MvPolynomial.ringHom_ext
        · intro a
          simp only [coneHom, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, Polynomial.coe_mapRingHom,
            Polynomial.map_C]
          rw [algX_comp i p (GlobalTheory.LB.pull_U i J).le a]
          congr 1
          exact eval_appLE i (GlobalTheory.LB.pull_U i J).le y h _
        · intro k
          simp only [coneHom, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', Polynomial.coe_mapRingHom,
            Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
          rw [hf]
          congr 2
          exact eval_appLE i (GlobalTheory.LB.pull_U i J).le y h _
      rw [heq]
      exact RingHom.ker_comp_of_injective _ (Polynomial.map_injective _ (i.residueFieldMap y).hom.injective)
    apply le_antisymm
    · refine le_iInf₂ fun j hj => ?_
      let J : (B.pull i).ι := fun _ => j
      have hJ : y ∈ (B.pull i).U J := (GlobalTheory.LB.pull_U i J).ge hj
      exact (iInf₂_le J hJ).trans_eq (hker J hJ)
    · refine le_iInf₂ fun J hJ => ?_
      rw [hker J hJ]
      exact iInf₂_le (J PUnit.unit) ((GlobalTheory.LB.pull_U i J).le hJ)
  · intro u su hc J
    rw [hf, hc (J PUnit.unit), map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, ← algX_comp, hf]

end ChowFormHeightComparison₂.CF

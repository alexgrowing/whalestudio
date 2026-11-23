import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExceptional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometricStatement
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.FlagPull

open VMetric

theorem isFlagCh2_flag_pull : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar p 1 → IsArithVar q 1 → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl : Vert.Flag E r) (a : ℝ), VMetric.IsFlagCh2 H fl a ↔ VMetric.IsFlagCh2 (H.pull π hπ) (fl.pull π) (π.residueDegree (genericPoint Y) * a) := by
  intro hA k _ X p _ Y _ q hp hq π hπ hg hd E r h H fl a
  set d := π.residueDegree (genericPoint Y) with hd'
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hdE₀ : (d : ENNReal) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hdE₁ : (d : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top d
  have hm := fun i σ => bcMeas_pullStep hp hq π hπ hg hd H fl i σ
  have hfin : h.FlagBcFinite fl ↔ (h.pull π hπ).FlagBcFinite (fl.pull π) := by
    have key (x : ENNReal) : x ≠ ⊤ ↔ (d : ENNReal) * x ≠ ⊤ := by
      simp [ENNReal.mul_eq_top, hdE₀, hdE₁]
    refine forall_congr' fun i => forall_congr' fun σ => ?_
    rw [hm i σ]
    exact key _
  have := hp.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have hbc : (h.pull π hπ).flagBc (fl.pull π) = d * h.flagBc fl := by
    rw [flagBc, flagBc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bcInt, bcInt, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hm i σ, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hx : ∀ (i : Fin r) (x : ℝ), (grLB fl i H).IsSelfInter x →
      (grLB (fl.pull π) i (H.pull π hπ)).IsSelfInter (d * x) := fun i x hx =>
    (GlobalTheory.T.graded_metric_pullback_isometric k X Y p q E r h H fl π hπ i).symm.isSelfInter hq ((hA.arProj k X Y p q 1 hp hq π hπ hg hd).1 _ x hx)
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, x, h₂, rfl⟩
    refine ⟨hfin.1 h₁, fun i => d * x i, fun i => hx i _ (h₂ i), ?_⟩
    rw [hbc, mul_sub, Finset.mul_sum]
    simp only [mul_div_assoc]
  · rintro ⟨h₁, x', h₂, e⟩
    choose x hx₀ using fun i => exists_isSelfInter hA hp (grLB fl i H)
    refine ⟨hfin.2 h₁, x, hx₀, mul_left_cancel₀ hd0 (e.trans ?_)⟩
    have e' (i) : x' i = d * x i := (h₂ i).unique hq (hx i _ (hx₀ i))
    rw [hbc, mul_sub, Finset.mul_sum]
    simp only [e', mul_div_assoc]

end GlobalTheory.FlagPull

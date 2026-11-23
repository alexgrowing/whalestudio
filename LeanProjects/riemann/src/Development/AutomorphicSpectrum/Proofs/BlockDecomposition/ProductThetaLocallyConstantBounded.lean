import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetFinAtMemIntegralGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitMeasureFiniteCompactSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyFinAtMemAndIntegralGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedLocalThetaLocallyConstantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedLocalThetaBoundedIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousTwistedLocalThetaInTorusStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedThetaValueIndicatorStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.ThetaFin

variable {K : Type} [Field K] [NumberField K]

theorem tw_one {c : HeckeCharacter K} {v : Pl} (L : LM c v) : L.tw 1 = L := by
  cases L with
  | sp w₁ w₂ Φ =>
    have h : (fun x : Qv v × Qv v => Φ (x * (1, 1))) = Φ := by
      funext x
      exact congrArg Φ (mul_one x)
    simp [LM.tw, h]
  | ns w σ η Φ => simp [LM.tw]

theorem integral_iff (w : PlK K) (x : K) :
    algebraMap K (Kv K w) x ∈ 𝒪[Kv K w] ↔ w.valuation K x ≤ 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation _), ← Valuation.vle_iff_le,
    Valuation.vle_iff_le Valued.v, map_one]
  have h : Valued.v (algebraMap K (w.adicCompletion K) x) = w.valuation K x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  rw [h]

theorem lies_under (w : PlK K) : w.asIdeal.LiesOver (w.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩

theorem tu_off (Sv : Finset Pl) (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) {v : Pl}
    (h1 : v ∉ Sv) (h2 : v ∉ m.support) : tu Sv m u v = 1 := by
  have : m v = 0 := by simpa using h2
  simp [tu, h1, this]

theorem tu_mem (Sv : Finset Pl) (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) (hu : ∀ v : Sv, u v ∈ unQ v.1) (v : Pl) :
    tu Sv m u v ∈ (fun x => unifUnit (Qv v) ^ (m v) * x) '' (unQ v ∪ {1}) := by
  by_cases h : v ∈ Sv
  · exact ⟨u ⟨v, h⟩, Or.inl (hu ⟨v, h⟩), by simp [tu, h]⟩
  · exact ⟨1, Or.inr rfl, by simp [tu, h]⟩

theorem compact_alt (m : Pl →₀ ℤ) (v : Pl) :
    IsCompact ((fun x => unifUnit (Qv v) ^ (m v) * x) '' (unQ v ∪ {1})) :=
  ((GlobalTheory.CompanionTheory.ThetaUnits.isCompact_unQ v).union isCompact_singleton).image (by fun_prop)

theorem measurable_tu (Sv : Finset Pl) (m : Pl →₀ ℤ) (v : Pl) {f : (Qv v)ˣ → ℂ} (hf : Continuous f) :
    Measurable (fun u : ∀ v : Sv, (Qv v.1)ˣ => f (tu Sv m u v)) := by
  by_cases h : v ∈ Sv
  · have hc : Continuous (fun x : (Qv v)ˣ => f (unifUnit (Qv v) ^ (m v) * x)) := by fun_prop
    have : (fun u : ∀ v : Sv, (Qv v.1)ˣ => f (tu Sv m u v)) =
        (fun x : (Qv v)ˣ => f (unifUnit (Qv v) ^ (m v) * x)) ∘ (fun u => u ⟨v, h⟩) := by
      funext u; simp [tu, h]
    rw [this]
    exact hc.measurable.comp (measurable_pi_apply _)
  · have : (fun u : ∀ v : Sv, (Qv v.1)ˣ => f (tu Sv m u v)) = fun _ => f (unifUnit (Qv v) ^ (m v)) := by
      funext u; simp [tu, h]
    rw [this]
    exact measurable_const

theorem exists_finset_integral (ξ : K) : ∃ T : Finset Pl, ∀ v ∉ T, ∀ w : PlK K,
    w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w] := by
  classical
  refine ⟨(HeightOneSpectrum.Support.finite (𝓞 K) ξ).toFinset.image (fun w => w.under (𝓞 ℚ)), ?_⟩
  intro v hv w hw
  rw [integral_iff]
  by_contra hlt
  apply hv
  refine Finset.mem_image.2 ⟨w, ?_, HeightOneSpectrum.ext hw.over.symm⟩
  simpa [HeightOneSpectrum.Support] using hlt

theorem valuation_natCast_le_one (w : PlK K) (n : ℕ) : w.valuation K (n : K) ≤ 1 := by
  have h := w.valuation_le_one (K := K) (n : 𝓞 K)
  simpa using h

theorem finitePart : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M →
  ∀ (Sv : Finset Pl) (m : Pl →₀ ℤ) (g₀ : G2), g₀ ∈ Gp M → ∃ (W : Set G2) (N : ℕ) (B : ℝ), W ∈ nhds g₀ ∧ N ≠ 0 ∧
    (∀ g ∈ W, g ∈ Gp M → ∀ u (ξ : K), ∏ᶠ v, (twM M Sv m u v).val (finAt v g) ξ = ∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ) ∧
    (∀ u, (∀ v : Sv, u v ∈ unQ v.1) → ∀ ξ : K, ‖∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ‖ ≤ B ∧
      (∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ ≠ 0 → ∃ a : 𝓞 K, (N : K) * ξ = a)) ∧
    ∀ ξ : K, Measurable (fun u => ∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ) := by
  classical
  intro K _ _ hK c M hM Sv m g₀ hg
  obtain ⟨hok, S0, hS0⟩ := hM
  obtain ⟨S1, hS1⟩ := GlobalTheory.CompanionTheory.AdelicIntegral.exists_finset_finAt_mem_integralGL g₀
  obtain ⟨S, hS⟩ : ∃ S : Finset Pl, S = S0 ∪ m.support ∪ Sv ∪ S1 := ⟨_, rfl⟩
  have hmem : ∀ v ∉ S, v ∉ S0 ∧ v ∉ m.support ∧ v ∉ Sv ∧ v ∉ S1 := by
    intro v hv
    subst hS
    simp only [Finset.mem_union, not_or] at hv
    exact ⟨hv.1.1.1, hv.1.1.2, hv.1.2, hv.2⟩
  have hplus : ∀ v, (M v).plus (finAt v g₀) := hg.1
  have hoff : ∀ v ∉ S, ∀ u, twM M Sv m u v = M v := by
    intro v hv u
    obtain ⟨-, h2, h3, -⟩ := hmem v hv
    simp only [twM]
    rw [tu_off Sv m u h3 h2, tw_one]
  have hint0 : ∀ v ∉ S, finAt v g₀ ∈ integralGL (Qv v) 2 := fun v hv => hS1 v (hmem v hv).2.2.2
  have hsph : ∀ v ∉ S, ∀ k ∈ integralGL (Qv v) 2, ∀ ξ : K,
      ((∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w]) → (M v).val k ξ = 1) ∧
      (¬ (∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w]) → (M v).val k ξ = 0) :=
    fun v hv k hk ξ => GlobalTheory.T.unramified_theta_value_indicator K hK c v (M v) (hok v) (hS0 v (hmem v hv).1).2 (hS0 v (hmem v hv).1).1 k hk ξ
  choose U hU hUc using fun v => GlobalTheory.T.twisted_local_theta_locally_constant K hK c v (M v) (hok v) (finAt v g₀) (hplus v)
  choose Bf Nf hNf hBN using fun v =>
    GlobalTheory.T.twisted_local_theta_bounded_integral K hK c v (M v) (hok v) (finAt v g₀) (hplus v) _ (compact_alt m v)
  have hW := GlobalTheory.CompanionTheory.AdelicIntegral.eventually_finAt_mem_and_integralGL S g₀ U (fun v _ => hU v) hint0
  have key : ∀ ξ : K, ∃ T : Finset Pl,
      (∀ u, ∀ v ∉ S ∪ T, (twM M Sv m u v).val (finAt v g₀) ξ = 1) ∧
      ∀ u, ∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ = ∏ v ∈ S ∪ T, (twM M Sv m u v).val (finAt v g₀) ξ := by
    intro ξ
    obtain ⟨T, hT⟩ := exists_finset_integral ξ
    have hone : ∀ u, ∀ v ∉ S ∪ T, (twM M Sv m u v).val (finAt v g₀) ξ = 1 := by
      intro u v hv
      simp only [Finset.mem_union, not_or] at hv
      rw [hoff v hv.1 u]
      exact (hsph v hv.1 _ (hint0 v hv.1) ξ).1 (hT v hv.2)
    refine ⟨T, hone, fun u => finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_⟩
    by_contra h
    exact hv (hone u v (by simpa using h))
  refine ⟨_, ∏ v ∈ S, Nf v, ∏ v ∈ S, max (Bf v) 1, hW, Finset.prod_ne_zero_iff.2 fun v _ => hNf v, ?_, ?_, ?_⟩
  · intro g hgW _ u ξ
    refine finprod_congr fun v => ?_
    by_cases hv : v ∈ S
    · exact hUc v _ (hgW.1 v hv) _ ξ
    · rw [hoff v hv u]
      have a := hsph v hv _ (hgW.2 v hv) ξ
      have b := hsph v hv _ (hint0 v hv) ξ
      by_cases hi : ∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w]
      · rw [a.1 hi, b.1 hi]
      · rw [a.2 hi, b.2 hi]
  · intro u hu ξ
    obtain ⟨T, hone, hfp⟩ := key ξ
    have hloc := fun v => hBN v (tu Sv m u v) (tu_mem Sv m u hu v) ξ
    rw [hfp u]
    constructor
    · rw [norm_prod]
      calc ∏ v ∈ S ∪ T, ‖(twM M Sv m u v).val (finAt v g₀) ξ‖
          ≤ ∏ v ∈ S ∪ T, (if v ∈ S then max (Bf v) 1 else 1) := by
            refine Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => ?_
            by_cases hv : v ∈ S
            · rw [if_pos hv]
              exact (hloc v).1.trans (le_max_left _ _)
            · rw [if_neg hv, hoff v hv u]
              have b := hsph v hv _ (hint0 v hv) ξ
              by_cases hi : ∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w]
              · rw [b.1 hi]; simp
              · rw [b.2 hi]; simp
        _ = ∏ v ∈ S, (if v ∈ S then max (Bf v) 1 else 1) :=
            (Finset.prod_subset Finset.subset_union_left fun v _ hv => if_neg hv).symm
        _ = ∏ v ∈ S, max (Bf v) 1 := Finset.prod_congr rfl fun v hv => if_pos hv
    · intro hne
      have hfv : ∀ v, (twM M Sv m u v).val (finAt v g₀) ξ ≠ 0 := by
        intro v
        by_cases hv : v ∈ S ∪ T
        · exact Finset.prod_ne_zero_iff.1 hne v hv
        · rw [hone u v hv]; exact one_ne_zero
      have hall : ∀ w : PlK K, w.valuation K (((∏ v ∈ S, Nf v : ℕ) : K) * ξ) ≤ 1 := by
        intro w
        have hl := lies_under w
        by_cases hv : w.under (𝓞 ℚ) ∈ S
        · have h1 := (integral_iff w _).1 ((hloc _).2 (hfv _) w hl)
          have h2 : ((∏ v ∈ S, Nf v : ℕ) : K) * ξ =
              ((∏ v ∈ S.erase (w.under (𝓞 ℚ)), Nf v : ℕ) : K) * ((Nf (w.under (𝓞 ℚ)) : K) * ξ) := by
            rw [← Finset.mul_prod_erase S Nf hv]
            push_cast
            ring
          rw [h2, map_mul]
          exact mul_le_one' (valuation_natCast_le_one w _) h1
        · have hi : ∀ w' : PlK K, w'.asIdeal.LiesOver (w.under (𝓞 ℚ)).asIdeal →
              algebraMap K (Kv K w') ξ ∈ 𝒪[Kv K w'] := by
            by_contra hi
            have := (hsph _ hv _ (hint0 _ hv) ξ).2 hi
            apply hfv (w.under (𝓞 ℚ))
            rw [hoff _ hv u]
            exact this
          rw [map_mul]
          exact mul_le_one' (valuation_natCast_le_one w _) ((integral_iff w _).1 (hi w hl))
      obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K _ hall
      exact ⟨r, hr.symm⟩
  · intro ξ
    obtain ⟨T, -, hfp⟩ := key ξ
    have h : (fun u => ∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ) =
        fun u => ∏ v ∈ S ∪ T, (twM M Sv m u v).val (finAt v g₀) ξ := funext hfp
    rw [h]
    exact Finset.measurable_fun_prod _ fun v _ =>
      measurable_tu Sv m v (GlobalTheory.T.continuous_twisted_local_theta_in_torus K hK c v (M v) (hok v) _ (hplus v) ξ)

end GlobalTheory.CompanionTheory.ThetaFin

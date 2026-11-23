import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeMulFundamentalDomainDiff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E.E3
open scoped ENNReal GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.LocSlice

theorem lintegral_compact_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (Fd P : Set G) (hF : IsFundamentalDomain Γ Fd μ) (hP : IsCompact P) (f : G → ℂ) (hf : Continuous f)
    (hinv : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (w : G → ℝ) (W : ℝ) (K : ℕ) (hw1 : ∀ x, 1 ≤ w x)
    (hw : ∀ γ ∈ Γ, ∀ p ∈ P, w (γ * p) ≤ W) (N : ℕ)
    (hN : ∀ x, {γ : Γ | (γ : G) * x ∈ P}.encard ≤ N) :
    ∫⁻ x in P, ‖f x‖ₑ ^ 2 ∂μ ≤
      N * (ENNReal.ofReal (W ^ (2 * K)) *
        ∫⁻ x in Fd, ENNReal.ofReal (w x ^ (-(2 * K : ℤ))) * ‖f x‖ₑ ^ 2 ∂μ) := by
  classical
  let T : Set G := ⋃ γ : Γ, (fun x => (γ : G) * x) '' P
  have hTm : MeasurableSet T := MeasurableSet.iUnion fun γ =>
    (hP.image (continuous_const.mul continuous_id)).isClosed.measurableSet
  have hPT : P ⊆ T := fun x hx => Set.mem_iUnion.2 ⟨1, x, hx, by simp⟩
  have hTinv : ∀ γ ∈ Γ, ∀ x ∈ T, γ * x ∈ T := by
    intro γ hγ x hx
    obtain ⟨δ, p, hp, rfl⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩ * δ, p, hp, by simp [mul_assoc]⟩
  let h : G → ℝ≥0∞ := T.indicator fun x => ‖f x‖ₑ ^ 2
  have hh : Measurable h := (hf.measurable.enorm.pow_const 2).indicator hTm
  have hhinv : ∀ γ ∈ Γ, ∀ x, h (γ * x) = h x := by
    intro γ hγ x
    by_cases hx : x ∈ T
    · simp only [h, Set.indicator_of_mem hx, Set.indicator_of_mem (hTinv γ hγ x hx), hinv γ hγ x]
    · have hx' : γ * x ∉ T := fun h' => hx (by
        simpa using hTinv γ⁻¹ (inv_mem hγ) _ h')
      simp only [h, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
  have h1 : ∫⁻ x in P, ‖f x‖ₑ ^ 2 ∂μ = ∫⁻ x in P, h x ∂μ :=
    setLIntegral_congr_fun hP.measurableSet fun x hx => by
      simp only [h, Set.indicator_of_mem (hPT hx)]
  have h2 := GlobalTheory.CompanionTheory.Unfolding.setLIntegral_le_mul_fundamentalDomain_diff Γ μ Fd P ∅ hF hP.measurableSet
    MeasurableSet.empty h hh hhinv N hN (by simp)
  rw [h1]
  refine h2.trans ?_
  gcongr
  rw [Set.diff_empty, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ T
  · obtain ⟨δ, p, hp, rfl⟩ := Set.mem_iUnion.1 hx
    have hwW := hw δ δ.2 p hp
    have hw0 : 0 < w ((δ : G) * p) := lt_of_lt_of_le one_pos (hw1 _)
    have hpow : w ((δ : G) * p) ^ (2 * K) ≤ W ^ (2 * K) := pow_le_pow_left₀ hw0.le hwW _
    have hq : (1 : ℝ) ≤ W ^ (2 * K) * w ((δ : G) * p) ^ (-(2 * K : ℤ)) := by
      have e : w ((δ : G) * p) ^ (-(2 * K : ℤ)) = (w ((δ : G) * p) ^ (2 * K))⁻¹ := by
        rw [_root_.zpow_neg]
        norm_cast
      rw [e, ← div_eq_mul_inv, one_le_div (pow_pos hw0 _)]
      exact hpow
    have hW0 : 0 ≤ W ^ (2 * K) := (pow_pos hw0 _).le.trans hpow
    simp only [h, Set.indicator_of_mem hx]
    rw [← mul_assoc, ← ENNReal.ofReal_mul hW0]
    calc ‖f ((δ : G) * p)‖ₑ ^ 2 = 1 * ‖f ((δ : G) * p)‖ₑ ^ 2 := (one_mul _).symm
      _ ≤ _ := by
        gcongr
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hq
  · simp only [h, Set.indicator_of_notMem hx, zero_le]

theorem pair_bound {X Y : Type} [Group X] [Group Y] [TopologicalSpace X] [TopologicalSpace Y]
    [IsTopologicalGroup X] [IsTopologicalGroup Y] [T2Space X] [T2Space Y]
    [LocallyCompactSpace X] [LocallyCompactSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y] (μ₁ : Measure X) (μ₂ : Measure Y)
    [μ₁.IsHaarMeasure] [μ₂.IsHaarMeasure] (m : MeasurableSpace (X × Y)) (e : Prod.instMeasurableSpace = m)
    (Γ : Subgroup (X × Y)) [Countable Γ] (μ : @Measure (X × Y) m)
    (hL : @Measure.IsMulLeftInvariant _ m _ μ) (hO : @Measure.IsOpenPosMeasure _ _ m μ)
    (hLF : @IsLocallyFiniteMeasure _ m _ μ) (Fd : Set (X × Y))
    (hF : @IsFundamentalDomain Γ (X × Y) _ _ m Fd μ) (f : X × Y → ℂ) (hf : Continuous f)
    (hinv : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (w : X × Y → ℝ) (K : ℕ) (hw1 : ∀ x, 1 ≤ w x) :
    ∃ c : NNReal, ∀ (A : Set X) (B : Set Y) (W : ℝ) (N : ℕ), IsCompact A → IsCompact B →
      (∀ γ ∈ Γ, ∀ p ∈ A ×ˢ B, w (γ * p) ≤ W) →
      (∀ x, {γ : Γ | (γ : X × Y) * x ∈ A ×ˢ B}.encard ≤ N) →
      (∫⁻ x in A, ∫⁻ y in B, ‖f (x, y)‖ₑ ^ 2 ∂μ₂ ∂μ₁ ≤ c * (N * (ENNReal.ofReal (W ^ (2 * K)) *
        @lintegral _ m (@Measure.restrict _ m μ Fd)
          fun x => ENNReal.ofReal (w x ^ (-(2 * K : ℤ))) * ‖f x‖ₑ ^ 2))) ∧
      (∫⁻ y in B, ∫⁻ x in A, ‖f (x, y)‖ₑ ^ 2 ∂μ₁ ∂μ₂ ≤ c * (N * (ENNReal.ofReal (W ^ (2 * K)) *
        @lintegral _ m (@Measure.restrict _ m μ Fd)
          fun x => ENNReal.ofReal (w x ^ (-(2 * K : ℤ))) * ‖f x‖ₑ ^ 2))) := by
  subst e
  haveI : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  haveI := hL
  haveI := hO
  haveI := hLF
  haveI : μ.IsHaarMeasure := {}
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ₁.prod μ₂ = c • μ := ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun A B W N hA hB hw hN => ?_⟩
  have hmeas : Measurable fun p : X × Y => ‖f p‖ₑ ^ 2 := hf.measurable.enorm.pow_const 2
  have h1 : ∫⁻ x in A, ∫⁻ y in B, ‖f (x, y)‖ₑ ^ 2 ∂μ₂ ∂μ₁ =
      c * ∫⁻ p in A ×ˢ B, ‖f p‖ₑ ^ 2 ∂μ := by
    have e1 : ∫⁻ x in A, ∫⁻ y in B, ‖f (x, y)‖ₑ ^ 2 ∂μ₂ ∂μ₁ =
        ∫⁻ p in A ×ˢ B, ‖f p‖ₑ ^ 2 ∂(μ₁.prod μ₂) := by
      rw [← Measure.prod_restrict, lintegral_prod _ hmeas.aemeasurable]
    rw [e1, hc, Measure.restrict_smul, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  have h2 := lintegral_compact_le Γ μ Fd (A ×ˢ B) hF (hA.prod hB) f hf hinv w W K hw1 hw N hN
  have h3 : ∫⁻ x in A, ∫⁻ y in B, ‖f (x, y)‖ₑ ^ 2 ∂μ₂ ∂μ₁ ≤ c * (N * (ENNReal.ofReal (W ^ (2 * K)) *
      ∫⁻ x in Fd, ENNReal.ofReal (w x ^ (-(2 * K : ℤ))) * ‖f x‖ₑ ^ 2 ∂μ)) := by
    rw [h1]; gcongr
  refine ⟨h3, ?_⟩
  have h4 : ∫⁻ y in B, ∫⁻ x in A, ‖f (x, y)‖ₑ ^ 2 ∂μ₁ ∂μ₂ = ∫⁻ x in A, ∫⁻ y in B, ‖f (x, y)‖ₑ ^ 2 ∂μ₂ ∂μ₁ :=
    (lintegral_lintegral_swap (f := fun x y => ‖f (x, y)‖ₑ ^ 2) hmeas.aemeasurable).symm
  rw [h4]
  exact h3

theorem final_le (Cy c : NNReal) (n n₂ K : ℕ) (R R₂ : ℝ) (hR : 0 ≤ R) (hR₂ : 0 ≤ R₂) (I : ℝ≥0∞) (hI : I ≠ ⊤) :
    (Cy : ℝ≥0∞) * (c * (((n * n₂ : ℕ) : ℝ≥0∞) * (ENNReal.ofReal ((1 + R + R₂) ^ (2 * K)) * I))) ≤
      ENNReal.ofReal ((Cy : ℝ) * c * n₂ * (1 + R₂) ^ (2 * K) * I.toReal * n * (1 + R) ^ (2 * K)) := by
  have e1 : I = ENNReal.ofReal I.toReal := (ENNReal.ofReal_toReal hI).symm
  have e2 : (Cy : ℝ≥0∞) = ENNReal.ofReal Cy := (ENNReal.ofReal_coe_nnreal).symm
  have e3 : (c : ℝ≥0∞) = ENNReal.ofReal c := (ENNReal.ofReal_coe_nnreal).symm
  have e4 : ((n * n₂ : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n * n₂ : ℕ) : ℝ) := (ENNReal.ofReal_natCast _).symm
  have hI0 : 0 ≤ I.toReal := ENNReal.toReal_nonneg
  have hp : (0 : ℝ) ≤ (1 + R + R₂) ^ (2 * K) := by positivity
  rw [e4, e2, e3]
  nth_rw 1 [e1]
  rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : (1 + R + R₂) ^ (2 * K) ≤ (1 + R) ^ (2 * K) * (1 + R₂) ^ (2 * K) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [mul_nonneg hR hR₂]) _
  have h2 : (0 : ℝ) ≤ (Cy : ℝ) * c * (n * n₂) * I.toReal := by positivity
  push_cast
  calc (Cy : ℝ) * (c * (n * n₂ * ((1 + R + R₂) ^ (2 * K) * I.toReal)))
      = ((Cy : ℝ) * c * (n * n₂) * I.toReal) * (1 + R + R₂) ^ (2 * K) := by ring
    _ ≤ ((Cy : ℝ) * c * (n * n₂) * I.toReal) * ((1 + R) ^ (2 * K) * (1 + R₂) ^ (2 * K)) :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = _ := by ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem logSize_nonneg {n : ℕ} (g : GA E n) : 0 ≤ logSize g := by
  have hM : ∀ A : Matrix (Fin n) (Fin n) (Ad E), 0 ≤ logSizeM A := fun A =>
    add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg)
      (finsum_nonneg fun _ => Real.posLog_nonneg)
  exact add_nonneg (hM _) (hM _)

theorem redSize_nonneg {n : ℕ} (g : GA E n) : 0 ≤ redSize g :=
  Real.iInf_nonneg fun _ => logSize_nonneg _

theorem redSize_mul_le {n : ℕ} (γ : GL (Fin n) E) (g : GA E n) : redSize (ratGL E n γ * g) ≤ logSize g := by
  have h := ciInf_le (f := fun δ : GL (Fin n) E => logSize (ratGL E n δ * (ratGL E n γ * g)))
    ⟨0, by rintro _ ⟨δ, rfl⟩; exact logSize_nonneg _⟩ γ⁻¹
  simpa [redSize, ← mul_assoc] using h

theorem one_le_wt (x : H E a b) : 1 ≤ wt x := by
  have h1 := redSize_nonneg x.1
  have h2 := redSize_nonneg x.2
  unfold wt
  linarith

theorem wt_mul_le {R₁ R₂ : ℝ} (γ : H E a b) (hγ : γ ∈ ratH E a b) (p : H E a b) (h₁ : logSize p.1 ≤ R₁)
    (h₂ : logSize p.2 ≤ R₂) : wt (γ * p) ≤ 1 + R₁ + R₂ := by
  obtain ⟨⟨A, B⟩, rfl⟩ := hγ
  have h3 := redSize_mul_le A p.1
  have h4 := redSize_mul_le B p.2
  have e : wt (((ratGL E a).prodMap (ratGL E b) (A, B)) * p) =
      1 + redSize (ratGL E a A * p.1) + redSize (ratGL E b B * p.2) := rfl
  rw [e]
  linarith

theorem mult_prod {A : Set (GA E a)} {B : Set (GA E b)} {n₁ n₂ : ℕ} (h₁ : Mult A n₁) (h₂ : Mult B n₂)
    (x : H E a b) : {γ : ratH E a b | (γ : H E a b) * x ∈ A ×ˢ B}.encard ≤ ((n₁ * n₂ : ℕ) : ℕ∞) := by
  let φ : ratH E a b → (ratGL E a).range × (ratGL E b).range := fun γ =>
    (⟨γ.1.1, γ.2.choose.1, congrArg Prod.fst γ.2.choose_spec⟩,
      ⟨γ.1.2, γ.2.choose.2, congrArg Prod.snd γ.2.choose_spec⟩)
  have hφ : Function.Injective φ := fun u v h => Subtype.ext (Prod.ext
    (congrArg (fun z => (z.1 : GA E a)) h) (congrArg (fun z => (z.2 : GA E b)) h))
  calc {γ : ratH E a b | (γ : H E a b) * x ∈ A ×ˢ B}.encard
      = (φ '' {γ : ratH E a b | (γ : H E a b) * x ∈ A ×ˢ B}).encard := (hφ.encard_image _).symm
    _ ≤ ({γ : (ratGL E a).range | (γ : GA E a) * x.1 ∈ A} ×ˢ
          {γ : (ratGL E b).range | (γ : GA E b) * x.2 ∈ B}).encard := by
        refine Set.encard_le_encard ?_
        rintro _ ⟨γ, hγ, rfl⟩
        exact ⟨hγ.1, hγ.2⟩
    _ = {γ : (ratGL E a).range | (γ : GA E a) * x.1 ∈ A}.encard *
          {γ : (ratGL E b).range | (γ : GA E b) * x.2 ∈ B}.encard := Set.encard_prod
    _ ≤ (n₁ : ℕ∞) * n₂ := mul_le_mul' (h₁ _) (h₂ _)
    _ = _ := by push_cast; rfl

theorem exists_logSize_le (hS : SizeT) {n : ℕ} {Q : Set (GA E n)} (hQ : IsCompact Q) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ q ∈ Q, logSize q ≤ R := by
  obtain ⟨C, hC0, hC⟩ := hS E n {(An.tor E (0 : Fin n → ℝ) : GA E n)⁻¹} Q isCompact_singleton hQ
  refine ⟨C, hC0, fun q hq => ?_⟩
  have h := hC _ rfl q hq 0
  simpa using h

theorem countable_ratH (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : Countable (ratH E a b) := by
  have hE : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  have hM : ∀ m : ℕ, Countable (GL (Fin m) E) := fun m =>
    haveI : Countable (Matrix (Fin m) (Fin m) E) := inferInstanceAs (Countable (Fin m → Fin m → E))
    (Units.val_injective (α := Matrix (Fin m) (Fin m) E)).countable
  haveI := hM a
  haveI := hM b
  exact ((ratGL E a).prodMap (ratGL E b)).rangeRestrict_surjective.countable

theorem loc_first (hT : SizeT) (hM : MultC) (hI : InterpolationL2Bound) (D : Dom E a b) (K : ℕ) (F : H E a b → ℂ)
    (hF : Continuous F) (hinv : LeftInv (fun _ : Unit => F)) (hW : WL2 D K (fun _ : Unit => F))
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun x y => F (x, y)))) (y₀ : GA E b)
    (μ : Measure (GA E a)) (hμ : μ.IsHaarMeasure) :
    ∃ (C : ℝ) (M : ℕ), ∀ S : Set (GA E a), IsCompact S → ∀ (n : ℕ) (R : ℝ), 0 ≤ R →
      Mult S n → (∀ g ∈ S, logSize g ≤ R) →
      ∫⁻ g in S, ‖F (g, y₀)‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * n * (1 + R) ^ M) := by
  haveI := hμ
  haveI := countable_ratH E a b
  obtain ⟨Ω, hΩ, hC⟩ := hI (GA E a) (GA E b) (Measure.haar : Measure (GA E b)) (fun x y => F (x, y))
    (fun x => hF.comp (Continuous.prodMk_right x)) hfd
  obtain ⟨Cy, hCy⟩ := hC y₀
  obtain ⟨n₂, hn₂⟩ := hM E b Ω hΩ
  have hm₂ : Mult Ω n₂ := by simpa using hn₂ 1 (by simp)
  obtain ⟨R₂, hR₂0, hR₂⟩ := exists_logSize_le hT hΩ
  obtain ⟨c, hc⟩ := pair_bound μ (Measure.haar : Measure (GA E b)) (borelH E a b)
    Prod.borelSpace.measurable_eq (ratH E a b) D.μ D.haar.1 D.haar.2.2.1 D.haar.2.2.2 D.F D.fd F hF
    (fun γ hγ x => hinv () ⟨γ, hγ⟩ x) wt K one_le_wt
  have hIt := (hW ()).ne
  refine ⟨(Cy : ℝ) * c * n₂ * (1 + R₂) ^ (2 * K) *
    (∫⁻ x, ENNReal.ofReal (wt x ^ (-(2 * K : ℤ))) * ‖F x‖ₑ ^ 2 ∂D.ν).toReal, 2 * K, fun S hS n R hR hn hSz => ?_⟩
  have h1 := (hc S Ω (1 + R + R₂) (n * n₂) hS hΩ
    (fun γ hγ p hp => wt_mul_le γ hγ p (hSz _ hp.1) (hR₂ _ hp.2)) (mult_prod hn hm₂)).1
  calc ∫⁻ g in S, ‖F (g, y₀)‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ g in S, (Cy : ℝ≥0∞) * ∫⁻ y in Ω, ‖F (g, y)‖ₑ ^ 2 ∂(Measure.haar : Measure (GA E b)) ∂μ :=
        lintegral_mono fun x => hCy x
    _ = Cy * ∫⁻ g in S, ∫⁻ y in Ω, ‖F (g, y)‖ₑ ^ 2 ∂(Measure.haar : Measure (GA E b)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ _ := mul_le_mul_right h1 _
    _ ≤ _ := final_le Cy c n n₂ K R R₂ hR hR₂0 _ hIt

theorem loc_second (hT : SizeT) (hM : MultC) (hI : InterpolationL2Bound) (D : Dom E a b) (K : ℕ) (F : H E a b → ℂ)
    (hF : Continuous F) (hinv : LeftInv (fun _ : Unit => F)) (hW : WL2 D K (fun _ : Unit => F))
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun y x => F (x, y)))) (x₀ : GA E a)
    (μ : Measure (GA E b)) (hμ : μ.IsHaarMeasure) :
    ∃ (C : ℝ) (M : ℕ), ∀ S : Set (GA E b), IsCompact S → ∀ (n : ℕ) (R : ℝ), 0 ≤ R →
      Mult S n → (∀ g ∈ S, logSize g ≤ R) →
      ∫⁻ g in S, ‖F (x₀, g)‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * n * (1 + R) ^ M) := by
  haveI := hμ
  haveI := countable_ratH E a b
  obtain ⟨Ω, hΩ, hC⟩ := hI (GA E b) (GA E a) (Measure.haar : Measure (GA E a)) (fun y x => F (x, y))
    (fun y => hF.comp (Continuous.prodMk_left y)) hfd
  obtain ⟨Cy, hCy⟩ := hC x₀
  obtain ⟨n₂, hn₂⟩ := hM E a Ω hΩ
  have hm₂ : Mult Ω n₂ := by simpa using hn₂ 1 (by simp)
  obtain ⟨R₂, hR₂0, hR₂⟩ := exists_logSize_le hT hΩ
  obtain ⟨c, hc⟩ := pair_bound (Measure.haar : Measure (GA E a)) μ (borelH E a b)
    Prod.borelSpace.measurable_eq (ratH E a b) D.μ D.haar.1 D.haar.2.2.1 D.haar.2.2.2 D.F D.fd F hF
    (fun γ hγ x => hinv () ⟨γ, hγ⟩ x) wt K one_le_wt
  have hIt := (hW ()).ne
  refine ⟨(Cy : ℝ) * c * n₂ * (1 + R₂) ^ (2 * K) *
    (∫⁻ x, ENNReal.ofReal (wt x ^ (-(2 * K : ℤ))) * ‖F x‖ₑ ^ 2 ∂D.ν).toReal, 2 * K, fun S hS n R hR hn hSz => ?_⟩
  have h1 := (hc Ω S (1 + R + R₂) (n * n₂) hΩ hS
    (fun γ hγ p hp => (wt_mul_le γ hγ p (hR₂ _ hp.1) (hSz _ hp.2)).trans_eq (by ring))
    (fun x => by rw [mul_comm n n₂]; exact mult_prod hm₂ hn x)).2
  calc ∫⁻ g in S, ‖F (x₀, g)‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ g in S, (Cy : ℝ≥0∞) * ∫⁻ x in Ω, ‖F (x, g)‖ₑ ^ 2 ∂(Measure.haar : Measure (GA E a)) ∂μ :=
        lintegral_mono fun x => hCy x
    _ = Cy * ∫⁻ g in S, ∫⁻ x in Ω, ‖F (x, g)‖ₑ ^ 2 ∂(Measure.haar : Measure (GA E a)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ _ := mul_le_mul_right h1 _
    _ ≤ _ := final_le Cy c n n₂ K R R₂ hR hR₂0 _ hIt

theorem locSlGlue : PositivityTheory.Rg.BcB.E.E3.LocSlGlue := by
  intro hT hM hI E _ _ _ a b D K F hF hinv hW
  exact ⟨fun hfd y μ hμ => loc_first hT hM hI D K F hF hinv hW hfd y μ hμ,
    fun hfd x μ hμ => loc_second hT hM hI D K F hF hinv hW hfd x μ hμ⟩

end GlobalTheory.CompanionTheory.LocSlice

end

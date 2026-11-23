import Mathlib
import Formalism.UnipotentAdelicQuotients.HaarProductClosedCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarProductClosedCompactHolds
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SmulNn

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology Set
open scoped NNReal ENNReal Pointwise

namespace PositivityTheory.ThKR.Sieg

section Retract

variable {H N : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
  [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
  [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N]

theorem char_eq_of_retract (ι : N →* H) (hι : Continuous ι) (π : H → N) (hπ : Continuous π)
    (hmul : ∀ x p, π (ι x * p) = x * π p) (φ : H ≃ₜ* H) (ψ : N ≃ₜ* N) (h1 : ∀ p, π (φ p) = ψ (π p))
    (h2 : ∀ p, (ι (π (φ p)))⁻¹ * φ p = (ι (π p))⁻¹ * p) : mulEquivHaarChar φ = mulEquivHaarChar ψ :=
  _root_.UpperTheory.Reformulated.B.Yhb4.main ι hι π hπ hmul φ ψ h1 h2

end Retract

section Heis

variable {A B : Type} [AddCommGroup A] [AddCommGroup B]

@[nolint unusedArguments]
def Heis (_ : A →+ A →+ B) : Type := A × B

variable (β : A →+ A →+ B)

instance : Group (Heis β) where
  mul x y := (x.1 + y.1, x.2 + y.2 + β x.1 y.1)
  one := (0, 0)
  inv x := (-x.1, -x.2 + β x.1 x.1)
  mul_assoc x y z := Prod.ext (add_assoc _ _ _) (by
    change x.2 + y.2 + β x.1 y.1 + z.2 + β (x.1 + y.1) z.1 = x.2 + (y.2 + z.2 + β y.1 z.1) + β x.1 (y.1 + z.1)
    simp only [map_add, AddMonoidHom.add_apply]
    abel)
  one_mul x := Prod.ext (zero_add _) (by change 0 + x.2 + β 0 x.1 = x.2; simp)
  mul_one x := Prod.ext (add_zero _) (by change x.2 + 0 + β x.1 0 = x.2; simp)
  inv_mul_cancel x := Prod.ext (neg_add_cancel _) (by
    change -x.2 + β x.1 x.1 + x.2 + β (-x.1) x.1 = 0; simp)

theorem Heis.mul_def (x y : Heis β) : x * y = (x.1 + y.1, x.2 + y.2 + β x.1 y.1) := rfl

theorem Heis.inv_def (x : Heis β) : x⁻¹ = (-x.1, -x.2 + β x.1 x.1) := rfl

variable [TopologicalSpace A] [TopologicalSpace B]

instance : TopologicalSpace (Heis β) := inferInstanceAs (TopologicalSpace (A × B))

instance [T2Space A] [T2Space B] : T2Space (Heis β) := inferInstanceAs (T2Space (A × B))

instance [LocallyCompactSpace A] [LocallyCompactSpace B] : LocallyCompactSpace (Heis β) :=
  inferInstanceAs (LocallyCompactSpace (A × B))

instance [SecondCountableTopology A] [SecondCountableTopology B] : SecondCountableTopology (Heis β) :=
  inferInstanceAs (SecondCountableTopology (A × B))

instance [MeasurableSpace A] [MeasurableSpace B] : MeasurableSpace (Heis β) :=
  inferInstanceAs (MeasurableSpace (A × B))

instance [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B] [SecondCountableTopology A] :
    BorelSpace (Heis β) := inferInstanceAs (BorelSpace (A × B))

variable [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]

theorem Heis.isTopologicalGroup (hβ : Continuous fun p : A × A => β p.1 p.2) : IsTopologicalGroup (Heis β) where
  continuous_mul := by
    change Continuous fun p : (A × B) × A × B => ((p.1.1 + p.2.1, p.1.2 + p.2.2 + β p.1.1 p.2.1) : A × B)
    exact (continuous_fst.fst.add continuous_snd.fst).prodMk ((continuous_fst.snd.add continuous_snd.snd).add
      (hβ.comp (continuous_fst.fst.prodMk continuous_snd.fst)))
  continuous_inv := by
    change Continuous fun p : A × B => ((-p.1, -p.2 + β p.1 p.1) : A × B)
    exact continuous_fst.neg.prodMk (continuous_snd.neg.add (hβ.comp (continuous_fst.prodMk continuous_fst)))

variable [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
  [LocallyCompactSpace B] [SecondCountableTopology B] [T2Space B] [MeasurableSpace B] [BorelSpace B]

theorem Heis.char_eq [IsTopologicalGroup (Heis β)] (hβ : Continuous fun p : A × A => β p.1 p.2) (ψ : Heis β ≃ₜ* Heis β)
    (θ₁ : A ≃ₜ+ A) (θ₂ : B ≃ₜ+ B) (h : ∀ x, ψ x = (θ₁ x.1, θ₂ x.2)) :
    mulEquivHaarChar ψ = addEquivAddHaarChar θ₁ * addEquivAddHaarChar θ₂ := by
  let μ₁ : Measure A := addHaar
  let μ₂ : Measure B := addHaar
  let μ : Measure (Heis β) := μ₁.prod μ₂
  have : IsFiniteMeasureOnCompacts μ := inferInstanceAs (IsFiniteMeasureOnCompacts (μ₁.prod μ₂))
  have : IsOpenPosMeasure μ := inferInstanceAs (IsOpenPosMeasure (μ₁.prod μ₂))
  have : IsMulLeftInvariant μ := ⟨fun x => by
    refine (MeasurePreserving.skew_product (μa := μ₁) (μc := μ₂) (μd := μ₂) (measurePreserving_add_left μ₁ x.1)
      (g := fun a b => x.2 + b + β x.1 a) ?_ (.of_forall fun a => ?_)).map_eq
    · exact ((continuous_const.add continuous_snd).add (hβ.comp (continuous_const.prodMk continuous_fst))).measurable
    · rw [show (fun b => x.2 + b + β x.1 a) = fun b => (x.2 + β x.1 a) + b from funext fun b => by abel]
      exact map_add_left_eq_self μ₂ _⟩
  have : IsHaarMeasure μ := {}
  obtain ⟨U, hU, hU0⟩ := exists_compact_mem_nhds (0 : A)
  obtain ⟨V, hV, hV0⟩ := exists_compact_mem_nhds (0 : B)
  have e := mulEquivHaarChar_smul_preimage μ (X := (U ×ˢ V : Set (A × B))) ψ
  have e1 := addEquivAddHaarChar_smul_preimage μ₁ (X := U) θ₁
  have e2 := addEquivAddHaarChar_smul_preimage μ₂ (X := V) θ₂
  have e3 : ψ ⁻¹' (U ×ˢ V : Set (A × B)) = ((θ₁ ⁻¹' U) ×ˢ (θ₂ ⁻¹' V) : Set (A × B)) := by
    ext x
    change ψ x ∈ (U ×ˢ V : Set (A × B)) ↔ _
    rw [h]
    rfl
  rw [e3] at e
  change _ • (μ₁.prod μ₂) _ = (μ₁.prod μ₂) _ at e
  rw [prod_prod, prod_prod, ← e1, ← e2] at e
  simp only [ENNReal.smul_def, smul_eq_mul] at e
  rw [mul_mul_mul_comm, ← ENNReal.coe_mul] at e
  refine ENNReal.coe_injective ((ENNReal.mul_left_inj (mul_ne_zero ?_ ?_) (ENNReal.mul_ne_top ?_ ?_)).1 e)
  · exact (measure_pos_of_mem_nhds _ (θ₁.continuous.continuousAt.preimage_mem_nhds (x := 0) (by simpa using hU0))).ne'
  · exact (measure_pos_of_mem_nhds _ (θ₂.continuous.continuousAt.preimage_mem_nhds (x := 0) (by simpa using hV0))).ne'
  · exact (θ₁.toHomeomorph.isCompact_preimage.2 hU).measure_lt_top.ne
  · exact (θ₂.toHomeomorph.isCompact_preimage.2 hV).measure_lt_top.ne

end Heis

section Bound

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {r : ℕ}

theorem isClosed_image_section {X : Type} [TopologicalSpace X] [T2Space X] (τ : X → Fin r → ℝ) (hτ : Continuous τ)
    (a : (Fin r → ℝ) → X) (ha : Continuous a) (h : ∀ t, τ (a t) = t) {D : Set (Fin r → ℝ)} (hD : IsClosed D) :
    IsClosed (a '' D) :=
  (Function.LeftInverse.isClosedEmbedding h hτ ha).isClosedMap _ hD

theorem lintegral_tau (ν : Measure G) [ν.IsHaarMeasure] (τ : G → Fin r → ℝ) (hτ : Continuous τ)
    (hτm : ∀ p q, τ (p * q) = τ p + τ q) (a : (Fin r → ℝ) → G) (ha : Continuous a) (hadd : ∀ s t, a (s + t) = a s * a t)
    (hτa : ∀ t, τ (a t) = t) (ρ : (Fin r → ℝ) → ℝ) (hρ : Continuous ρ) (hρa : ∀ s t, ρ (s + t) = ρ s + ρ t)
    (hmod : ∀ s, ν.map (· * a s) = ENNReal.ofReal (Real.exp (ρ s)) • ν) {Ω : Set G} (hΩ : IsCompact Ω)
    (hΩτ : ∀ p ∈ Ω, τ p = 0) :
    ∃ C : ℝ≥0, ∀ h : (Fin r → ℝ) → ℝ≥0∞, Measurable h →
      ∫⁻ p in Ω * range a, h (τ p) ∂ν = C * ∫⁻ t, h t * ENNReal.ofReal (Real.exp (-ρ t)) := by
  have hT : IsClosed (Ω * range a) := by
    rw [← image_univ]
    exact (isClosed_image_section τ hτ a ha hτa isClosed_univ).mul_left_of_isCompact hΩ
  set T := Ω * range a with hTdef
  let w : G → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (ρ (τ p)))
  have hw : Measurable w := (Real.continuous_exp.comp (hρ.comp hτ)).measurable.ennreal_ofReal
  let m : Measure (Fin r → ℝ) := ((ν.restrict T).withDensity w).map τ
  have hm : ∀ g : (Fin r → ℝ) → ℝ≥0∞, Measurable g → ∫⁻ t, g t ∂m = ∫⁻ p, T.indicator (fun p => w p * g (τ p)) p ∂ν :=
    fun g hg => by
      rw [lintegral_map hg hτ.measurable, lintegral_withDensity_eq_lintegral_mul _ hw (g := fun p => g (τ p)) (hg.comp hτ.measurable),
        lintegral_indicator hT.measurableSet]
      rfl
  have hTa : ∀ s p, p * a s ∈ T ↔ p ∈ T := by
    have : ∀ s p, p ∈ T → p * a s ∈ T := by
      rintro s _ ⟨p, hp, _, ⟨t, rfl⟩, rfl⟩
      exact ⟨p, hp, _, ⟨t + s, rfl⟩, by simp [hadd, mul_assoc]⟩
    have h0 : a 0 = 1 := by simpa using hadd 0 0
    refine fun s p => ⟨fun h => ?_, this s p⟩
    have := this (-s) _ h
    rwa [mul_assoc, ← hadd, add_neg_cancel, h0, mul_one] at this
  have : IsAddLeftInvariant m := ⟨fun s => by
    refine Measure.ext_of_lintegral _ fun g hg => ?_
    rw [lintegral_map hg (measurable_const_add s), hm (fun t => g (s + t)) (hg.comp (measurable_const_add s)), hm _ hg]
    have hG : Measurable (T.indicator fun p => w p * g (τ p)) :=
      (hw.mul (hg.comp hτ.measurable)).indicator hT.measurableSet
    have e := lintegral_map (μ := ν) hG (measurable_mul_const (a s))
    rw [hmod, lintegral_smul_measure, smul_eq_mul] at e
    have h0 : ENNReal.ofReal (Real.exp (ρ s)) ≠ 0 := by simp [Real.exp_pos]
    rw [← ENNReal.mul_right_inj h0 ENNReal.ofReal_ne_top, e, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun p => ?_
    by_cases hp : p ∈ T
    · rw [indicator_of_mem hp, indicator_of_mem ((hTa s p).2 hp)]
      simp only [w, hτm, hτa, hρa, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, add_comm s]
      ring
    · rw [indicator_of_notMem hp, indicator_of_notMem (mt (hTa s p).1 hp), mul_zero]⟩
  have : IsFiniteMeasureOnCompacts m := ⟨fun C hC => by
    obtain ⟨B, hB⟩ := hC.bddAbove_image hρ.continuousOn
    rw [← lintegral_indicator_one hC.measurableSet, hm _ (measurable_one.indicator hC.measurableSet)]
    have hK : IsCompact (Ω * a '' C) := hΩ.mul (hC.image ha)
    refine lt_of_le_of_lt (lintegral_mono (g := (Ω * a '' C).indicator fun _ => ENNReal.ofReal (Real.exp B)) fun p => ?_) ?_
    · by_cases hp : p ∈ T
      · by_cases hp' : τ p ∈ C
        · obtain ⟨q, hq, _, ⟨t, rfl⟩, rfl⟩ := hp
          have e : τ (q * a t) = t := by rw [hτm, hτa, hΩτ q hq, zero_add]
          simp only [e] at hp'
          rw [indicator_of_mem (show q * a t ∈ T from ⟨q, hq, _, ⟨t, rfl⟩, rfl⟩),
            indicator_of_mem (show q * a t ∈ Ω * a '' C from ⟨q, hq, _, ⟨t, hp', rfl⟩, rfl⟩), e, indicator_of_mem hp']
          simp only [w, e, Pi.one_apply, mul_one]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hB ⟨t, hp', rfl⟩))
        · rw [indicator_of_mem hp, indicator_of_notMem hp', mul_zero]
          exact zero_le
      · rw [indicator_of_notMem hp]
        exact zero_le
    · rw [lintegral_indicator_const hK.measurableSet]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top⟩
  refine ⟨addHaarScalarFactor m volume, fun h hh => ?_⟩
  have hg : Measurable fun t => h t * ENNReal.ofReal (Real.exp (-ρ t)) :=
    hh.mul (Real.continuous_exp.comp hρ.neg).measurable.ennreal_ofReal
  have e := hm _ hg
  rw [isAddLeftInvariant_eq_smul m volume, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul,
    lintegral_indicator hT.measurableSet] at e
  rw [e]
  refine lintegral_congr fun p => ?_
  rw [mul_left_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel]
  simp

theorem map_mul_right_of_char (ν : Measure G) [ν.IsHaarMeasure] (b : G) (φ : G ≃ₜ* G) (hφ : ∀ p, φ p = b⁻¹ * p * b) :
    ν.map (· * b) = ((mulEquivHaarChar φ)⁻¹ : ℝ≥0) • ν := by
  have e : (fun p => p * b) = φ ∘ fun p => b * p * 1 * b * b⁻¹ := funext fun p => by simp [hφ]
  rw [e, ← Measure.map_map (g := φ) φ.continuous.measurable (by fun_prop)]
  simp only [mul_one, mul_inv_cancel_right, map_mul_left_eq_self]
  conv_rhs => rw [← mulEquivHaarChar_smul_map ν φ]
  rw [smul_smul, inv_mul_cancel₀ (mulEquivHaarChar_pos φ).ne', one_smul]

theorem lintegral_siegel_le (μ : Measure G) [μ.IsHaarMeasure] (P K : Subgroup G) (hP : IsClosed (P : Set G))
    (hK : IsCompact (K : Set G)) (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) [LocallyCompactSpace P]
    (τ : P → Fin r → ℝ) (hτ : Continuous τ)
    (hτm : ∀ p q, τ (p * q) = τ p + τ q) (a : (Fin r → ℝ) → P) (ha : Continuous a) (hadd : ∀ s t, a (s + t) = a s * a t)
    (hτa : ∀ t, τ (a t) = t) (ρ : (Fin r → ℝ) → ℝ) (hρ : Continuous ρ) (hρa : ∀ s t, ρ (s + t) = ρ s + ρ t)
    (hmod : ∀ s, (haar : Measure P).map (· * a s) = ENNReal.ofReal (Real.exp (ρ s)) • haar) {Ω : Set G}
    (hΩ : IsCompact Ω) (hΩτ : ∀ p ∈ Ω, ∃ h : p ∈ P, τ ⟨p, h⟩ = 0) (hc : ∀ m : P, m.1 ∈ K → ∀ t, a t * m = m * a t) :
    ∃ C : ℝ≥0, ∀ (D : Set (Fin r → ℝ)) (S : Set G), MeasurableSet D → MeasurableSet S →
      (∀ g ∈ S, ∃ p ∈ Ω, ∃ t ∈ D, ∃ k ∈ K, g = p * a t * k) →
      ∀ (f : G → ℝ≥0∞) (h : (Fin r → ℝ) → ℝ≥0∞), Measurable h →
        (∀ p ∈ Ω, ∀ t ∈ D, ∀ k ∈ K, f (p * a t * k) ≤ h t) →
        ∫⁻ g in S, f g ∂μ ≤ C * ∫⁻ t in D, h t * ENNReal.ofReal (Real.exp (-ρ t)) := by
  have hι : IsClosedEmbedding ((↑) : P → G) := hP.isClosedEmbedding_subtypeVal
  have : SecondCountableTopology P := hι.isEmbedding.secondCountableTopology
  have hL : IsCompact (((↑) : P → G) ⁻¹' K) := hι.isCompact_preimage hK
  have hτL : ∀ m : P, m.1 ∈ K → τ m = 0 := fun m hm => by
    obtain ⟨B, hB⟩ := (hL.image hτ).isBounded.exists_norm_le
    have h1 : τ 1 = 0 := by simpa using hτm 1 1
    have h2 : ∀ j : ℕ, τ (m ^ j) = (j : ℝ) • τ m := fun j => by
      induction j with
      | zero => simpa using h1
      | succ j ih => rw [pow_succ, hτm, ih]; simp [add_smul]
    by_contra h0
    obtain ⟨j, hj⟩ := exists_nat_gt (B / ‖τ m‖)
    have h3 := hB _ ⟨m ^ j, K.pow_mem hm j, rfl⟩
    rw [h2, norm_smul, Real.norm_natCast] at h3
    rw [div_lt_iff₀ (norm_pos_iff.2 h0)] at hj
    linarith
  have hΩ' : IsCompact (((↑) : P → G) ⁻¹' Ω * ((↑) : P → G) ⁻¹' K) := (hι.isCompact_preimage hΩ).mul hL
  obtain ⟨C, hC⟩ := lintegral_tau (haar : Measure P) τ hτ hτm a ha hadd hτa ρ hρ hρa hmod hΩ' (by
    rintro _ ⟨p, hp, m, hm, rfl⟩
    obtain ⟨_, e⟩ := hΩτ _ hp
    rw [hτm, hτL m hm, e, add_zero])
  have hT : IsClosed (((↑) : P → G) ⁻¹' Ω * ((↑) : P → G) ⁻¹' K * range a) := by
    rw [← image_univ]
    exact (isClosed_image_section τ hτ a ha hτa isClosed_univ).mul_left_of_isCompact hΩ'
  set T := ((↑) : P → G) ⁻¹' Ω * ((↑) : P → G) ⁻¹' K * range a with hTdef
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let κ : Measure K := haarMeasure ⊤
  have hκ : κ univ = 1 := by simpa [κ] using haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))
  have hmP : Measurable ((↑) : P → G) := measurable_subtype_coe
  have hmK : Measurable ((↑) : K → G) := measurable_subtype_coe
  obtain ⟨c, -, hc', hΦ⟩ := GlobalTheory.CompanionTheory.HaarPK.haarProductClosedCompact_holds G μ inferInstance inferInstance
    (NeZero.ne μ) P K hP hK hPK ((haar : Measure P).map (↑)) (κ.map (↑))
    (by rw [Measure.map_apply hmP hP.measurableSet.compl]; simp [preimage])
    (fun p hp => by
      rw [Measure.map_map (measurable_const_mul p) hmP]
      conv_rhs => rw [← map_mul_left_eq_self (haar : Measure P) ⟨p, hp⟩, Measure.map_map hmP (measurable_const_mul _)]
      rfl)
    (fun s hs => by rw [Measure.map_apply hmP hs.measurableSet]; exact (hι.isCompact_preimage hs).measure_lt_top.ne)
    (by rw [Ne, Measure.map_eq_zero_iff hmP.aemeasurable]; exact NeZero.ne _)
    (by rw [Measure.map_apply hmK MeasurableSet.univ, preimage_univ, hκ])
    (by rw [Measure.map_apply hmK hK.measurableSet.compl]; simp [preimage])
    (fun p hp => by
      rw [Measure.map_map (measurable_const_mul p) hmK]
      conv_rhs => rw [← map_mul_left_eq_self κ ⟨p, hp⟩, Measure.map_map hmK (measurable_const_mul _)]
      rfl)
  refine ⟨c.toNNReal * C, fun D S hD hS hSΩ f h hh hf => ?_⟩
  rw [← lintegral_indicator hS, lintegral_eq_nnreal]
  refine iSup₂_le fun φ hφ => ?_
  have hφm : Measurable fun g => (φ g : ℝ≥0∞) := φ.measurable.coe_nnreal_ennreal
  rw [← SimpleFunc.lintegral_eq_lintegral]
  change ∫⁻ g, (φ g : ℝ≥0∞) ∂μ ≤ _
  rw [hΦ _ hφm, ENNReal.coe_mul, ENNReal.coe_toNNReal hc', mul_assoc, ← lintegral_indicator hD]
  have e : D.indicator (fun t => h t * ENNReal.ofReal (Real.exp (-ρ t))) =
      fun t => D.indicator h t * ENNReal.ofReal (Real.exp (-ρ t)) := funext fun t => by
    by_cases ht : t ∈ D <;> simp [ht]
  rw [e, ← hC _ (hh.indicator hD), ← lintegral_indicator hT.measurableSet]
  refine mul_le_mul_right ?_ _
  refine (lintegral_map_le _ ((↑) : P → G)).trans (lintegral_mono fun p => ?_)
  refine (lintegral_map_le _ ((↑) : K → G)).trans ?_
  refine (lintegral_mono (g := fun _ => T.indicator (fun p => D.indicator h (τ p)) p) fun k => ?_).trans
    (by rw [lintegral_const, hκ, mul_one])
  refine (hφ _).trans ?_
  by_cases hg : p.1 * k.1 ∈ S
  · obtain ⟨q, hq, t, ht, k', hk', e⟩ := hSΩ _ hg
    obtain ⟨hqP, hq0⟩ := hΩτ q hq
    let m : P := (⟨q, hqP⟩ * a t)⁻¹ * p
    have hm : m.1 = k' * k.1⁻¹ := by
      change (q * a t)⁻¹ * p.1 = _
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]
    have hmK : m.1 ∈ K := hm ▸ K.mul_mem hk' (K.inv_mem k.2)
    have hp : p = ⟨q, hqP⟩ * m * a t := by rw [mul_assoc, ← hc m hmK, ← mul_assoc, mul_inv_cancel_left]
    have hpT : p ∈ T := ⟨_, ⟨⟨q, hqP⟩, hq, m, hmK, rfl⟩, _, ⟨t, rfl⟩, hp.symm⟩
    have hτp : τ p = t := by rw [hp, hτm, hτm, hq0, hτL m hmK, hτa]; simp
    rw [indicator_of_mem hg, indicator_of_mem hpT, hτp, indicator_of_mem ht, e]
    exact hf q hq t ht k' hk'
  · rw [indicator_of_notMem hg]
    exact zero_le

end Bound

end PositivityTheory.ThKR.Sieg

end

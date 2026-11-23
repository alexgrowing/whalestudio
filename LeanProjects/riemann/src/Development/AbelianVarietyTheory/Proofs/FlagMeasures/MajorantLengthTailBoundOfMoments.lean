import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousOnMajorantFlagLengths
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TailMassLeOfMajorantLengthMomentBound
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Amp.TailTwo

theorem cheb_le {X : Type*} [MeasurableSpace X] (ν : Measure X) (l : X → ℝ) (f : X → ℝ≥0∞) (E : Set X)
    (hE : MeasurableSet E) (T : ℝ) (hT : 0 < T) (hl : ∀ x ∈ E, T ≤ l x) (n : ℕ) :
    ∫⁻ x in E, f x ∂ν ≤ ENNReal.ofReal ((T ^ n)⁻¹) * ∫⁻ x, ENNReal.ofReal (l x ^ n) * f x ∂ν := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans (setLIntegral_mono' hE fun x hx => ?_) (setLIntegral_le_lintegral E _)
  have hTn : 0 < T ^ n := pow_pos hT n
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hTn.le)]
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal, inv_mul_eq_div, one_le_div hTn]
  exact pow_le_pow_left₀ hT.le (hl x hx) n

theorem meas_closed (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ) (hg : ContinuousOn g (GG k r)) (t : Set ℝ) (ht : IsClosed t) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} := by
  obtain ⟨u, hu, h⟩ := (continuousOn_iff_isClosed.1 hg) t ht
  have h1 : MeasurableSet (α := Mt k r) u := IsClosed.measurableSet (α := Mt k r) hu
  have h2 : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (Cheb.isClosed_GG k r)
  have h3 : {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} = u ∩ GG k r := by
    rw [← h]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  rw [h3]
  exact h1.inter h2

theorem meas_open (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ) (hg : ContinuousOn g (GG k r)) (t : Set ℝ) (ht : IsOpen t) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} := by
  obtain ⟨u, hu, h⟩ := continuousOn_iff'.1 hg t ht
  have h1 : MeasurableSet (α := Mt k r) u := IsOpen.measurableSet (α := Mt k r) hu
  have h2 : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (Cheb.isClosed_GG k r)
  have h3 : {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} = u ∩ GG k r := by
    rw [← h]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  rw [h3]
  exact h1.inter h2

end GlobalTheory.Amp.TailTwo

namespace GlobalTheory.Amp.TailTwo

theorem tailBd_of_moments : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (νS : Measure (Mt k r)) (Φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) (q : ℕ) (H₁ : ℝ), inWb k r z → 0 < H₁ → νS {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → MomBd z νS Φ q H₁ → (∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal ((lA k r z (Matrix.of x) a)⁻¹ ^ (2 * q)) * (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤ ENNReal.ofReal (H₁ ^ (2 * q)) * l2SG νS Φ) → TailBd z νS Φ q H₁ := by
  intro k r Wp _ _ _ z νS Φ q H₁ _ hH hG _ hM hI la hla
  set T : ℝ := la * H₁ with hTdef
  have hT : 0 < T := mul_pos hla hH
  set f : Mt k r → ℝ≥0∞ := fun x => (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 with hf
  set A : Fin (r + 1) → Set (Mt k r) := fun a =>
    {x : Mt k r | Matrix.of x ∈ GG k r ∧ (fun g => lA k r z g a) (Matrix.of x) ∈ Set.Ici T} with hA
  set B : Fin (r + 1) → Set (Mt k r) := fun a =>
    {x : Mt k r | Matrix.of x ∈ GG k r ∧ (fun g => lA k r z g a) (Matrix.of x) ∈ Set.Ioi 0} ∩
    {x : Mt k r | Matrix.of x ∈ GG k r ∧ (fun g => lA k r z g a) (Matrix.of x) ∈ Set.Iic T⁻¹} with hB
  set N : Set (Mt k r) := {x | Matrix.of x ∉ GG k r} with hN
  have hGc : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (Cheb.isClosed_GG k r)
  have hNm : MeasurableSet N := hGc.compl
  have hAm : ∀ a, MeasurableSet (A a) := fun a =>
    meas_closed k r _ ((LenCont.lA_Sg_continuousOn k r z).1 a) _ isClosed_Ici
  have hBm : ∀ a, MeasurableSet (B a) := fun a =>
    (meas_open k r _ ((LenCont.lA_Sg_continuousOn k r z).1 a) _ isOpen_Ioi).inter
      (meas_closed k r _ ((LenCont.lA_Sg_continuousOn k r z).1 a) _ isClosed_Iic)
  set U : Set (Mt k r) := N ∪ ⋃ a, (A a ∪ B a) with hU
  have hUm : MeasurableSet U := hNm.union (MeasurableSet.iUnion fun a => (hAm a).union (hBm a))
  have hsub : {x : Mt k r | ∃ a : Fin (r + 1), la * H₁ ≤ max (lA k r z (Matrix.of x) a) (lA k r z (Matrix.of x) a)⁻¹} ⊆ U := by
    rintro x ⟨a, ha⟩
    by_cases hx : Matrix.of x ∈ GG k r
    · refine Or.inr (Set.mem_iUnion.2 ⟨a, ?_⟩)
      rcases le_max_iff.1 ha with h | h
      · exact Or.inl ⟨hx, h⟩
      · have hpos : 0 < lA k r z (Matrix.of x) a := inv_pos.1 (lt_of_lt_of_le hT h)
        refine Or.inr ⟨⟨hx, hpos⟩, hx, ?_⟩
        show lA k r z (Matrix.of x) a ≤ T⁻¹
        exact (le_inv_comm₀ hT hpos).1 h
    · exact Or.inl hx
  have hc : ∀ a, ∫⁻ x in A a ∪ B a, f x ∂νS ≤ 2 * (ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ) := by
    intro a
    have key : ENNReal.ofReal ((T ^ (2 * q))⁻¹) * (ENNReal.ofReal (H₁ ^ (2 * q)) * l2SG νS Φ) =
        ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [Real.rpow_neg hla.le, hTdef, mul_pow]
      have : la ^ (2 * (q : ℝ)) = la ^ (2 * q) := by
        rw [← Real.rpow_natCast]; push_cast; ring_nf
      rw [this]
      have h1 : H₁ ^ (2 * q) ≠ 0 := pow_ne_zero _ hH.ne'
      field_simp
    have hA' : ∫⁻ x in A a, f x ∂νS ≤ ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
      refine (cheb_le νS (fun x => lA k r z (Matrix.of x) a) f (A a) (hAm a) T hT (fun x hx => hx.2) (2 * q)).trans ?_
      rw [← key]
      gcongr
      exact hM a
    have hB' : ∫⁻ x in B a, f x ∂νS ≤ ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
      refine (cheb_le νS (fun x => (lA k r z (Matrix.of x) a)⁻¹) f (B a) (hBm a) T hT (fun x hx => ?_) (2 * q)).trans ?_
      · have hpos : 0 < lA k r z (Matrix.of x) a := hx.1.2
        exact (le_inv_comm₀ hT hpos).2 hx.2.2
      · rw [← key]
        gcongr
        exact hI a
    refine (lintegral_union_le _ _ _).trans ?_
    exact (add_le_add hA' hB').trans (le_of_eq (two_mul _).symm)
  calc ∫⁻ x, Set.indicator {x : Mt k r | ∃ a : Fin (r + 1), la * H₁ ≤ max (lA k r z (Matrix.of x) a) (lA k r z (Matrix.of x) a)⁻¹}
          (fun x => (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) x ∂νS
        ≤ ∫⁻ x, U.indicator f x ∂νS := lintegral_mono fun x => Set.indicator_le_indicator_of_subset hsub (fun _ => by simp) x
    _ = ∫⁻ x in U, f x ∂νS := lintegral_indicator hUm _
    _ ≤ ∫⁻ x in N, f x ∂νS + ∫⁻ x in ⋃ a, (A a ∪ B a), f x ∂νS := lintegral_union_le _ _ _
    _ ≤ 0 + ∑ a : Fin (r + 1), ∫⁻ x in A a ∪ B a, f x ∂νS := by
        gcongr
        · exact (setLIntegral_measure_zero _ _ hG).le
        · exact (lintegral_iUnion_le _ _).trans (le_of_eq (tsum_fintype _))
    _ ≤ ∑ _a : Fin (r + 1), 2 * (ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ) := by
        rw [zero_add]; exact Finset.sum_le_sum fun a _ => hc a
    _ ≤ ENNReal.ofReal (2 * (2 * r + 2 : ℝ) * la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← mul_assoc,
          ENNReal.ofReal_mul (by positivity)]
        gcongr ?_ * _ * _
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        push_cast
        have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        nlinarith

end GlobalTheory.Amp.TailTwo

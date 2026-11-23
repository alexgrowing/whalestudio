import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem exists_mem_boxK_two_pow {K W : Type} [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) {n M : ℕ}
    {R : ℝ} (hR : 0 < R) (X : Fin n → Fin M → K) :
    ∃ j : ℕ, X ∈ boxK κ (fun _ _ => (2 : ℝ) ^ j * R) := by
  set B : ℝ := ∑ a, ∑ i, ∑ w, ‖κ (X a i) w‖ with hB
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (B / R) (one_lt_two : (1 : ℝ) < 2)
  refine ⟨j, fun a i w => ?_⟩
  have h1 : ‖κ (X a i) w‖ ≤ ∑ w, ‖κ (X a i) w‖ :=
    Finset.single_le_sum (f := fun w => ‖κ (X a i) w‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  have h2 : ∑ w, ‖κ (X a i) w‖ ≤ ∑ i, ∑ w, ‖κ (X a i) w‖ :=
    Finset.single_le_sum (f := fun i => ∑ w, ‖κ (X a i) w‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have h3 : ∑ i, ∑ w, ‖κ (X a i) w‖ ≤ B :=
    Finset.single_le_sum (f := fun a => ∑ i, ∑ w, ‖κ (X a i) w‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ a)
  have h4 : B < (2 : ℝ) ^ j * R := (div_lt_iff₀ hR).1 hj
  linarith

theorem exists_large_ofReal_div_mul_le {A : ℝ} (hA : 0 ≤ A) {D ε : ℝ≥0∞} (hD : D ≠ ⊤) (hε : ε ≠ 0) :
    ∃ R : ℝ, 1 ≤ R ∧ ENNReal.ofReal (A / R) * D ≤ ε := by
  obtain ⟨δ, hδ0, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hε)
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hDr : 0 ≤ D.toReal := ENNReal.toReal_nonneg
  have hq : 0 ≤ A * D.toReal / δ := by positivity
  refine ⟨1 + A * D.toReal / δ, by linarith, ?_⟩
  have hRpos : 0 < 1 + A * D.toReal / δ := by linarith
  have hkey : A / (1 + A * D.toReal / δ) * D.toReal ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hRpos]
    have : (δ : ℝ) * (1 + A * D.toReal / δ) = δ + A * D.toReal := by
      field_simp
    rw [this]
    have : (0 : ℝ) ≤ δ := hδ0'.le
    linarith
  calc ENNReal.ofReal (A / (1 + A * D.toReal / δ)) * D
      = ENNReal.ofReal (A / (1 + A * D.toReal / δ)) * ENNReal.ofReal D.toReal := by
        rw [ENNReal.ofReal_toReal hD]
    _ = ENNReal.ofReal (A / (1 + A * D.toReal / δ) * D.toReal) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (δ : ℝ) := ENNReal.ofReal_le_ofReal hkey
    _ = δ := ENNReal.ofReal_coe_nnreal
    _ ≤ ε := hδ.le

theorem tsum_geometric_half_mul (c d : ℝ≥0∞) :
    ∑' j : ℕ, c * (2⁻¹ : ℝ≥0∞) ^ j * d = c * 2 * d := by
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
    ENNReal.one_sub_inv_two, inv_inv]

theorem shell_real_identity {c R : ℝ} (hR : 0 < R) (e j : ℕ) :
    c / ((2 : ℝ) ^ j * R) ^ (e + 1) * ((2 : ℝ) ^ (j + 1) * R) ^ e
      = c * 2 ^ e / R * (1 / 2) ^ j := by
  have h2 : (2 : ℝ) ^ (j + 1) * R = 2 * ((2 : ℝ) ^ j * R) := by ring
  have key : ∀ P : ℝ, P ≠ 0 → c / P ^ (e + 1) * (2 * P) ^ e = c * 2 ^ e / P := by
    intro P hP
    rw [mul_pow, pow_succ]
    field_simp
  rw [h2, key _ (by positivity), one_div, inv_pow]
  field_simp

theorem tail_small_of_density :
    ∀ (K W : Type) [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) (n M : ℕ) (H : Type) [MeasurableSpace H] [MeasurableSpace (Fin n → Fin M → K)] (μ : Measure (Fin n → Fin M → K)) (ν : Measure H) (q : (Fin n → Fin M → K) → H) (C₀ : ℝ≥0∞), C₀ ≠ ⊤ → (∀ r : Fin n → W → ℝ, (∀ a w, 0 < r a w) → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n)))) → Measurable q → (∀ r : Fin n → W → ℝ, MeasurableSet (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) → ∀ φ : (Fin n → Fin M → K) → ℂ, (∀ k : ℕ, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X, X ∉ GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) → ‖φ X‖ ≤ C / R ^ k) → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ R : ℝ, 1 ≤ R ∧ ∀ Y, MeasurableSet Y → ∫⁻ X in (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε * ν Y := by
  intro K W _ _ κ n M H _ _ μ ν q C₀ hC₀ hden hq hbox φ hφ ε hε
  obtain ⟨e, he⟩ : ∃ e : ℕ, e = 2 * (M - n) * Fintype.card W * n := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ := hφ (e + 1)
  have hA : 0 ≤ |C| * (2 : ℝ) ^ e := by positivity
  obtain ⟨R, hR1, hRε⟩ := exists_large_ofReal_div_mul_le hA
    (ENNReal.mul_ne_top (by simp) hC₀ : (2 : ℝ≥0∞) * C₀ ≠ ⊤) hε
  refine ⟨R, hR1, fun Y hY => ?_⟩
  have hR0 : 0 < R := by linarith
  let S : ℕ → Set (Fin n → Fin M → K) := fun j =>
    (boxK κ (fun _ _ => (2 : ℝ) ^ (j + 1) * R) \ boxK κ (fun _ _ => (2 : ℝ) ^ j * R)) ∩ q ⁻¹' Y
  have hcover : (boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y ⊆ ⋃ j, S j := by
    rintro X ⟨hX, hXY⟩
    classical
    have hex := exists_mem_boxK_two_pow κ hR0 X
    have hne : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0] at this
      simp only [pow_zero, one_mul] at this
      exact hX this
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
    refine Set.mem_iUnion.2 ⟨j, ⟨?_, ?_⟩, hXY⟩
    · have := Nat.find_spec hex
      rw [hj] at this
      exact this
    · exact Nat.find_min hex (by omega)
  have hshell : ∀ j, ∫⁻ X in S j, ‖φ X‖ₑ ∂μ
      ≤ ENNReal.ofReal (|C| * 2 ^ e / R) * (2⁻¹ : ℝ≥0∞) ^ j * (C₀ * ν Y) := by
    intro j
    have hRj : 1 ≤ (2 : ℝ) ^ j * R := by
      have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
      nlinarith
    have hRj0 : 0 < (2 : ℝ) ^ j * R := by linarith
    have hSm : MeasurableSet (S j) := ((hbox _).diff (hbox _)).inter (hq hY)
    have hpt : ∀ X ∈ S j, ‖φ X‖ₑ ≤ ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) := by
      rintro X ⟨⟨-, hX⟩, -⟩
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ((hC _ hRj X hX).trans ?_)
      exact div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
    have hmu : μ (S j) ≤ C₀ * ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e) * ν Y := by
      have h1 := hden (fun _ _ => (2 : ℝ) ^ (j + 1) * R) (fun _ _ => by positivity) Y hY
      have h2 : μ (S j) ≤ μ (boxK κ (fun _ _ => (2 : ℝ) ^ (j + 1) * R) ∩ q ⁻¹' Y) :=
        measure_mono fun X hX => ⟨hX.1.1, hX.2⟩
      have h3 : (∏ a : Fin n, ∏ w : W, ENNReal.ofReal ((2 : ℝ) ^ (j + 1) * R) ^ (2 * (M - n)))
          = ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e) := by
        rw [ENNReal.ofReal_pow (by positivity), he]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      rw [h3] at h1
      exact h2.trans h1
    calc ∫⁻ X in S j, ‖φ X‖ₑ ∂μ
        ≤ ∫⁻ _ in S j, ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) ∂μ :=
          setLIntegral_mono' hSm hpt
      _ = ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) * μ (S j) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) *
            (C₀ * ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e) * ν Y) := by gcongr
      _ = (ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) *
            ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e)) * (C₀ * ν Y) := by ring
      _ = ENNReal.ofReal (|C| * 2 ^ e / R) * (2⁻¹ : ℝ≥0∞) ^ j * (C₀ * ν Y) := by
          rw [← ENNReal.ofReal_mul (by positivity), shell_real_identity hR0,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
          congr 3
          rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
          simp
  calc ∫⁻ X in (boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ
      ≤ ∫⁻ X in ⋃ j, S j, ‖φ X‖ₑ ∂μ := lintegral_mono_set hcover
    _ ≤ ∑' j, ∫⁻ X in S j, ‖φ X‖ₑ ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (|C| * 2 ^ e / R) * (2⁻¹ : ℝ≥0∞) ^ j * (C₀ * ν Y) :=
        ENNReal.tsum_le_tsum hshell
    _ = ENNReal.ofReal (|C| * 2 ^ e / R) * 2 * (C₀ * ν Y) := tsum_geometric_half_mul _ _
    _ = ENNReal.ofReal (|C| * 2 ^ e / R) * (2 * C₀) * ν Y := by ring
    _ ≤ ε * ν Y := by gcongr

end GlobalTheory.CompanionTheory.WhitFree.AvgInf

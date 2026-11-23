import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.OneLeGN
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrVGA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrableOfDecayVG

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem conj_inv_mul_conj {m : ℕ} (P Y g : Matrix (Fin m) (Fin m) ℂ) (hP : IsUnit P.det) :
    P * ((P⁻¹ * Y * P)⁻¹ * g) * P⁻¹ = Y⁻¹ * (P * g * P⁻¹) := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hP]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hP]

theorem unitary_hermitian_form_mul_mem {k r : ℕ} {s x : Mat k r} (hs : s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : s * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  show (s * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (s * x) = Formalism.QuantumDeterminants.Hpk k r
  have hs' : sᴴ * Formalism.QuantumDeterminants.Hpk k r * s = Formalism.QuantumDeterminants.Hpk k r := hs
  have hx' : xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r := hx
  calc (s * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (s * x) = xᴴ * (sᴴ * Formalism.QuantumDeterminants.Hpk k r * s) * x := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [hs', hx']

theorem conjTranspose_inv_mul_conjTranspose {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : IsUnit P.det) : P⁻¹ᴴ * Pᴴ = 1 := by
  rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv P hP, Matrix.conjTranspose_one]

theorem cayley_conj_mem_unitary_group {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {g : Mat k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : P * g * P⁻¹ ∈ UJset ε := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hJ : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.2
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  show inUJ ε (P * g * P⁻¹)
  rw [← mir_inUJ_iff]
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  have e1 := conjTranspose_inv_mul_conjTranspose P hd
  have e2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = P⁻¹ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = P⁻¹ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hJ, hg']
    _ = (P⁻¹ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]

theorem cayley_conj_inv_mem_hermitian_group {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {Y : Mat k r} (hY : Y ∈ UJset ε) : P⁻¹ * Y * P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hJ : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.2
  have hY' : Yᴴ * Formalism.REAL.Jm ε * Y = Formalism.REAL.Jm ε := (mir_inUJ_iff ε Y).2 hY
  show (P⁻¹ * Y * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (P⁻¹ * Y * P) = Formalism.QuantumDeterminants.Hpk k r
  have e1 := conjTranspose_inv_mul_conjTranspose P hd
  have e2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  rw [← hJ]
  calc (P⁻¹ * Y * P)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * (P⁻¹ * Y * P)
      = Pᴴ * (Yᴴ * ((P⁻¹ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹)) * Y) * P := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * Formalism.REAL.Jm ε * P := by
        rw [e1, e2, Matrix.one_mul, Matrix.mul_one, hY']

theorem ae_mem_unitary_nilpotent_product {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  haveI : SigmaFinite μN := hN.1
  rw [ae_iff]
  have hsub : {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r |
      ¬(Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r)} ⊆
      ({x | Matrix.of x ∉ Formalism.QuantumDeterminants.UWset k r z} ×ˢ Set.univ) ∪
        (Set.univ ×ˢ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) := by
    intro p hp
    simp only [Set.mem_ofPred_eq, not_and_or] at hp
    rcases hp with hp | hp
    · exact Or.inl ⟨hp, trivial⟩
    · exact Or.inr ⟨trivial, hp⟩
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.prod_prod, hW.2.2.1, zero_mul]
  · rw [Measure.prod_prod, hN.2.2.1, mul_zero]

theorem finB_frob_eq {k r : ℕ} (g : Mat k r) : frob g = Formalism.FourierDecayAlt.B.gN g := by
  unfold frob Formalism.FourierDecayAlt.B.gN
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq]

theorem finB_Jct {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

theorem finB_inv_eq {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {g : Mat k r} (hg : g ∈ UJset ε) :
    g⁻¹ = Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε := by
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := (mir_inUJ_iff ε g).2 hg
  apply Matrix.inv_eq_left_inv
  calc Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, signature_matrix_sq]

theorem finB_mul_inv {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {g : Mat k r} (hg : g ∈ UJset ε) :
    g * g⁻¹ = 1 := by
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := (mir_inUJ_iff ε g).2 hg
  have h1 : g⁻¹ * g = 1 := by
    rw [finB_inv_eq hg]
    calc Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, signature_matrix_sq]
  exact mul_eq_one_comm.mp h1

theorem finB_frob_inv {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {g : Mat k r} (hg : g ∈ UJset ε) :
    frob g⁻¹ = frob g := by
  have hJ : (Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε = 1 := by rw [finB_Jct, signature_matrix_sq]
  rw [finB_frob_eq, finB_frob_eq, finB_inv_eq hg, S0.DecA.gN_right _ hJ, S0.DecA.gN_left _ hJ, S0.DecA.gN_conjT]

theorem finB_frob_mul_le {k r : ℕ} (a b : Mat k r) : frob (a * b) ≤ frob a * frob b := by
  rw [finB_frob_eq, finB_frob_eq, finB_frob_eq]
  exact S0.DecA.gN_mul_le' a b

theorem finB_one_le {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {g : Mat k r} (hg : g ∈ UJset ε) :
    1 ≤ frob g := by
  have h0 : (1 : ℝ) ≤ frob (1 : Mat k r) := by
    rw [finB_frob_eq]
    have := S0.DecA.gN_entry (1 : Mat k r) ⟨0, by omega⟩ ⟨0, by omega⟩
    simpa using this
  have h1 : frob (1 : Mat k r) ≤ frob g * frob g := by
    have := finB_frob_mul_le g g⁻¹
    rwa [finB_mul_inv hg, finB_frob_inv hg] at this
  nlinarith [Real.sqrt_nonneg (∑ i, ∑ j, ‖g i j‖ ^ 2), show frob g = Real.sqrt (∑ i, ∑ j, ‖g i j‖ ^ 2) from rfl]

theorem finB_le_mul {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Y : Mat k r} (hY : Y ∈ UJset ε) (g : Mat k r) :
    frob g ≤ frob Y * frob (Y⁻¹ * g) := by
  have := finB_frob_mul_le Y (Y⁻¹ * g)
  rwa [← Matrix.mul_assoc, finB_mul_inv hY, Matrix.one_mul] at this

theorem finB_intJ {k r : ℕ} (ε : Fin (2 * r + k + 1) → Bool) (hq : 1 ≤ S7.q0 ε) (b : ℝ)
    (hb : 2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) < b) :
    Integrable (fun y : Formalism.REAL.UJ ε => frob (Formalism.MainNotions.S.umat y) ^ (-b)) (Formalism.REAL.muG ε) := by
  refine integrable_muG_of_haar ε (fun g => frob g ^ (-b)) (fun ν _ => ?_)
  obtain ⟨s, hs⟩ := S7.exists_signVG ε
  have hb0 : 0 ≤ b := by
    have : (0 : ℝ) ≤ 2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) := by positivity
    linarith
  have hmem : ∀ g : S7.UJ ε, S7.toM g ∈ UJset ε := fun g => unitary_matrix_mem_set ε g
  have hone : ∀ g : S7.UJ ε, 1 ≤ frob (S7.toM g) := fun g => finB_one_le (hmem g)
  have hfr : ∀ g : Mat k r, frob g = Real.sqrt (S7.hs g) := fun g => rfl
  have hcont : Continuous (fun g : S7.UJ ε => frob (S7.toM g) ^ (-b)) := by
    have h1 : Continuous (fun g : S7.UJ ε => frob (S7.toM g)) := by
      have : Continuous (fun g : Mat k r => frob g) := by
        simp only [hfr]; exact Real.continuous_sqrt.comp S7.hs_contVG
      exact this.comp (S7.continuous_toM ε)
    exact h1.rpow_const (fun g => Or.inl (by linarith [hone g]))
  refine S7.integrable_of_decayVG ε s ν _ hcont.aestronglyMeasurable 1 (fun g _ => ?_) b ?_ (fun g hg => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hone g]) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (hone g) (by linarith)
  · rw [hs]; push_cast at hb ⊢; linarith
  · set H := S7.hs (S7.toM g) with hH
    have hn : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
    have hn0 : (0 : ℝ) < ((2 * r + k + 1 : ℕ) : ℝ) := by linarith
    have hH0 : 0 < H := by
      have : (0 : ℝ) < ((2 * r + k + 1 : ℕ) : ℝ) * Real.exp 2 + 1 := by positivity
      linarith
    have hq0 : 0 < H / ((2 * r + k + 1 : ℕ) : ℝ) := div_pos hH0 hn0
    refine ⟨Real.log (H / ((2 * r + k + 1 : ℕ) : ℝ)) / 2, ?_, ?_⟩
    · rw [show 2 * (Real.log (H / ((2 * r + k + 1 : ℕ) : ℝ)) / 2) = Real.log (H / ((2 * r + k + 1 : ℕ) : ℝ)) by ring,
        Real.exp_log hq0, mul_div_cancel₀ _ hn0.ne']
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hone g]) _), one_mul, hfr,
        ← hH, Real.sqrt_eq_rpow, ← Real.rpow_mul hH0.le]
      have e : -(b * (Real.log (H / ((2 * r + k + 1 : ℕ) : ℝ)) / 2)) =
          Real.log (H / ((2 * r + k + 1 : ℕ) : ℝ)) * (-(b / 2)) := by ring
      rw [e, ← Real.rpow_def_of_pos hq0, Real.div_rpow hH0.le hn0.le, show (1 / 2 : ℝ) * -b = -(b / 2) by ring]
      have h1 : (1 : ℝ) ≤ (((2 * r + k + 1 : ℕ) : ℝ) ^ (-(b / 2)))⁻¹ := by
        rw [Real.rpow_neg hn0.le, inv_inv]
        exact Real.one_le_rpow hn (by linarith)
      rw [div_eq_mul_inv]
      have h2 : 0 ≤ H ^ (-(b / 2)) := Real.rpow_nonneg hH0.le _
      exact le_mul_of_one_le_right h2 h1

end ReciprocityTheory.ChartRestriction.DS.Lap

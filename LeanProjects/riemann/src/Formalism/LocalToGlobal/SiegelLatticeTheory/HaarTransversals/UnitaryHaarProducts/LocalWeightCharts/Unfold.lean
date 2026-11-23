import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas
open scoped ENNReal

namespace WlocSk

namespace Grp

def sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if i.val < r ∨ r + k < i.val then ⟨2 * r + k - i.val, by omega⟩ else i

lemma sig_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (sig k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := by
  unfold sig; split_ifs <;> rfl

lemma sig_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : sig k r (sig k r i) = i := by
  apply Fin.ext
  have hi := i.isLt
  have h1 := sig_val k r i
  have h2 := sig_val k r (sig k r i)
  split_ifs at h1 h2 <;> omega

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

lemma sgn_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : sgn k r (sig k r i) = sgn k r i := by
  have hi := i.isLt
  have h1 := sig_val k r i
  unfold sgn
  split_ifs at h1 ⊢ <;> first | rfl | (exfalso; omega)

lemma Hpk_eq (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.Hpk k r i j = if j = sig k r i then sgn k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  have hs := sig_val k r i
  have e1 : (j = sig k r i) ↔ j.val = (sig k r i).val := Fin.ext_iff
  have e2 : (i = j) ↔ i.val = j.val := Fin.ext_iff
  unfold Formalism.QuantumDeterminants.Hpk sgn
  simp only [e1, e2]
  split_ifs at * <;> first | rfl | (exfalso; omega)

lemma Hpk_sq (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  ext i j
  rw [mul_apply]
  simp only [Hpk_eq k r i, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Hpk_eq, sig_sig, sgn_sig, one_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm]; unfold sgn; split_ifs <;> norm_num
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

variable {k r : ℕ}

lemma one_mem : (1 : Mat k r) ∈ Gr k r := by
  show (1 : Mat k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

lemma mul_mem {a b : Mat k r} (ha : a ∈ Gr k r) (hb : b ∈ Gr k r) : a * b ∈ Gr k r := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha', hb']

lemma of_mul_mem {s x : Mat k r} (hs : s ∈ Gr k r) (hsx : s * x ∈ Gr k r) : x ∈ Gr k r := by
  have hs' : sᴴ * Formalism.QuantumDeterminants.Hpk k r * s = Formalism.QuantumDeterminants.Hpk k r := hs
  have hsx' : (s * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (s * x) = Formalism.QuantumDeterminants.Hpk k r := hsx
  show xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r
  calc xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = xᴴ * (sᴴ * Formalism.QuantumDeterminants.Hpk k r * s) * x := by rw [hs']
    _ = (s * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (s * x) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := hsx'

lemma inv_left {g : Mat k r} (hg : g ∈ Gr k r) :
    (Formalism.QuantumDeterminants.Hpk k r * gᴴ * Formalism.QuantumDeterminants.Hpk k r) * g = 1 := by
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  calc Formalism.QuantumDeterminants.Hpk k r * gᴴ * Formalism.QuantumDeterminants.Hpk k r * g
      = Formalism.QuantumDeterminants.Hpk k r * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', Hpk_sq]

lemma inv_eq {g : Mat k r} (hg : g ∈ Gr k r) : g⁻¹ = Formalism.QuantumDeterminants.Hpk k r * gᴴ * Formalism.QuantumDeterminants.Hpk k r :=
  Matrix.inv_eq_left_inv (inv_left hg)

lemma inv_mul {g : Mat k r} (hg : g ∈ Gr k r) : g⁻¹ * g = 1 := by
  rw [inv_eq hg]; exact inv_left hg

lemma mul_inv {g : Mat k r} (hg : g ∈ Gr k r) : g * g⁻¹ = 1 := by
  rw [inv_eq hg]; exact mul_eq_one_comm.mp (inv_left hg)

lemma inv_mem {g : Mat k r} (hg : g ∈ Gr k r) : g⁻¹ ∈ Gr k r := by
  apply of_mul_mem hg
  rw [mul_inv hg]; exact one_mem

lemma isClosed_Gr : IsClosed (Gr k r) := by
  have hc : Continuous (fun x : Mat k r => xᴴ * Formalism.QuantumDeterminants.Hpk k r * x) := by fun_prop
  exact isClosed_eq hc continuous_const

lemma continuous_of : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : Mat k r)) := continuous_id

lemma measurableSet_Gr : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Gr k r} :=
  (isClosed_Gr.preimage continuous_of).measurableSet

end Grp

section Unfold

variable {k r : ℕ}

lemma continuous_mulP : Continuous (mulP (k := k) (r := r)) := by
  have h1 : Continuous fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mat k r) :=
    continuous_fst
  have h2 : Continuous fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mat k r) :=
    continuous_snd
  exact h1.matrix_mul h2

lemma measurable_mulP : Measurable (mulP (k := k) (r := r)) := continuous_mulP.measurable

lemma continuous_rmul (x : Formalism.QuantumDeterminants.Mt k r) :
    Continuous (fun s : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of s * Matrix.of x) i j : Formalism.QuantumDeterminants.Mt k r)) := by
  have h1 : Continuous fun s : Formalism.QuantumDeterminants.Mt k r => (Matrix.of s : Mat k r) := continuous_id
  exact h1.matrix_mul continuous_const

theorem unfold_weil {μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} {cS : ℝ≥0∞} (hcS : cS ≠ ⊤)
    (hP : (μW.prod μN).map mulP = cS • μS) (hQ : IsQuotMeas μG μS ν)
    (f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, ∫⁻ p, f (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) ∂ν =
      cS * ∫⁻ y, f y ∂μG := by
  have hin : ∀ x : Formalism.QuantumDeterminants.Mt k r,
      ∫⁻ p, f (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) =
        cS * ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x
    have hm : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r => f (fun i j => (Matrix.of s * Matrix.of x) i j)) :=
      hf.comp (continuous_rmul x).measurable
    have h := lintegral_map (μ := μW.prod μN) hm measurable_mulP
    rw [hP, lintegral_smul_measure, smul_eq_mul] at h
    exact h.symm
  rw [lintegral_congr hin, lintegral_const_mul' _ _ hcS, hQ f hf]

theorem nu_conc {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)} {T : Set (Mat k r)} (hQ : IsQuotMeas μG μS ν)
    (hG : μG {x | Matrix.of x ∉ Gr k r} = 0) (hS0 : μS ≠ 0) (hSc : μS {x | Matrix.of x ∉ T} = 0)
    (hTG : T ⊆ Gr k r) : ν {x | Matrix.of x ∉ Gr k r} = 0 := by
  set E : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∉ Gr k r} with hEdef
  have hE : MeasurableSet E := Grp.measurableSet_Gr.compl
  have hw := hQ (E.indicator 1) (measurable_one.indicator hE)
  rw [lintegral_indicator_one hE, hG] at hw
  have hlow : ∀ x, E.indicator (fun _ => μS Set.univ) x ≤
      ∫⁻ s, E.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx]
      have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ T := ae_iff.mpr hSc
      have h1 : ∀ᵐ s ∂μS, E.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) = (1 : ℝ≥0∞) := by
        filter_upwards [hae] with s hs
        apply Set.indicator_of_mem
        intro hsx
        exact hx (Grp.of_mul_mem (hTG hs) hsx)
      rw [lintegral_congr_ae h1, lintegral_one]
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  have h2 := lintegral_mono (μ := ν) hlow
  rw [lintegral_indicator_const hE, ← hw] at h2
  have hpos : μS Set.univ ≠ 0 := by
    intro h0; exact hS0 (Measure.measure_univ_eq_zero.mp h0)
  exact (mul_eq_zero.mp (le_zero_iff.mp h2)).resolve_left hpos

end Unfold

section FromSteps

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ}
  {b : Fin (2 * r + 2) → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mat k r → (H →L[ℂ] H)} {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
  [FiniteDimensional ℂ Vp] {π : Mat k r → (Vp →L[ℂ] Vp)} {w : H}
  {μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}

lemma S_sub_G (hSG : SGrp) (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN) :
    Formalism.QuantumDeterminants.Sset k r z ⊆ Gr k r := by
  obtain ⟨hset, -⟩ := hyp
  obtain ⟨-, -, hz, hT, -⟩ := hset
  obtain ⟨hW, hN, -⟩ := hSG k r z c hz hT
  rintro s ⟨h, hh, m, hm, rfl⟩
  exact Grp.mul_mem (hW hh) (hN hm)

theorem unfold_of (hSP : SProd) (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN) :
    ∃ cS : ℝ≥0∞, cS ≠ 0 ∧ cS ≠ ⊤ ∧ ∀ f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, Measurable f →
      ∫⁻ x, ∫⁻ p, f (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) ∂ν =
        cS * ∫⁻ y, f y ∂μG := by
  obtain ⟨cS, h0, htop, hP⟩ := hSP k r z c u v b H σ Vp π w μG μS ν μW μN hyp
  exact ⟨cS, h0, htop, fun f hf => unfold_weil htop hP hyp.2.2.2.2.2.2.1 f hf⟩

theorem nu_conc_of (hSG : SGrp) (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN) :
    ν {x | Matrix.of x ∉ Gr k r} = 0 := by
  have hS := S_sub_G hSG hyp
  obtain ⟨-, -, -, -, hG, hSm, hQ, -⟩ := hyp
  exact nu_conc hQ hG.2.2.1 hSm.2.1 hSm.2.2.1 hS

end FromSteps

end WlocSk

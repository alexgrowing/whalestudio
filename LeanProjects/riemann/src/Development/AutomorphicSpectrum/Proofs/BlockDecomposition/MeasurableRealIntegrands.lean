import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Sec2

noncomputable section

open MeasureTheory Matrix Complex Ad3 Ad3.LR Ad3.K.GL2LocalData Ad3.K.GL2LocalData.WR GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst

namespace GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst.Meas

variable {α : Type*} [MeasurableSpace α]

def MM (A : α → Mt) : Prop := ∀ i j, Measurable fun a => A a i j

theorem cR {f : α → ℝ} (hf : Measurable f) : Measurable fun a => (f a : ℂ) :=
  Complex.measurable_ofReal.comp hf

theorem det_m {A : α → Mt} (hA : MM A) : Measurable fun a => (A a).det := by
  simp only [Matrix.det_fin_two]
  exact ((hA 0 0).mul (hA 1 1)).sub ((hA 0 1).mul (hA 1 0))

theorem mul_m {A B : α → Mt} (hA : MM A) (hB : MM B) : MM fun a => A a * B a := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hA i 0).mul (hB 0 j)).add ((hA i 1).mul (hB 1 j))

theorem inv_m {A : α → Mt} (hA : MM A) : MM fun a => (A a)⁻¹ := by
  intro i j
  have hd : Measurable fun a => ((A a).det)⁻¹ := (det_m hA).inv
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp
  · exact hd.mul (hA 1 1)
  · exact hd.mul (hA 0 1)
  · exact hd.mul (hA 1 0)
  · exact hd.mul (hA 0 0)

theorem glOf_val (h : Mt) : (glOf h).val = if h.det ≠ 0 then h else 1 := by
  unfold glOf
  split_ifs <;> rfl

theorem glOf_m {A : α → Mt} (hA : MM A) : MM fun a => (glOf (A a)).val := by
  intro i j
  have hs : MeasurableSet {a | (A a).det ≠ 0} :=
    (measurableSet_singleton (0 : ℝ)).compl.preimage (det_m hA)
  have : (fun a => (glOf (A a)).val i j) =
      fun a => if (A a).det ≠ 0 then A a i j else (1 : Mt) i j := by
    funext a
    rw [glOf_val]
    split_ifs <;> rfl
  rw [this]
  exact Measurable.ite hs (hA i j) measurable_const

theorem sg_m {t : α → ℝ} (ht : Measurable t) : Measurable fun a => sg (t a) := by
  unfold sg
  exact Measurable.ite (measurableSet_lt ht measurable_const) measurable_const measurable_const

theorem Wm_m (k : ℕ) {A : α → Mt} (hA : MM A) : Measurable fun a => Wm k (A a) := by
  unfold Wm
  have hd := det_m hA
  have hq : Measurable fun a => ((A a 1 1 : ℂ) - (A a 1 0 : ℂ) * Complex.I) :=
    (cR (hA 1 1)).sub ((cR (hA 1 0)).mul_const _)
  have hp : Measurable fun a => ((A a 0 1 : ℂ) - (A a 0 0 : ℂ) * Complex.I) :=
    (cR (hA 0 1)).sub ((cR (hA 0 0)).mul_const _)
  refine Measurable.ite (measurableSet_lt measurable_const hd) ?_ measurable_const
  refine ((cR (hd.pow_const _)).mul (hq.pow_const _)).mul ?_
  exact Complex.measurable_exp.comp ((hp.div hq).const_mul _)

theorem WthR_m (n : ℤ) {G : α → GL (Fin 2) ℝ} (hG : MM fun a => (G a).val) :
    Measurable fun a => WthR n (G a) := by
  unfold WthR
  have hd : Measurable fun a => ((G a).val).det := det_m hG
  have hq : Measurable fun a => (((G a).val 1 1 : ℂ) + Complex.I * ((G a).val 1 0 : ℂ)) :=
    (cR (hG 1 1)).add ((cR (hG 1 0)).const_mul _)
  have hp : Measurable fun a => (((G a).val 0 1 : ℂ) + Complex.I * ((G a).val 0 0 : ℂ)) :=
    (cR (hG 0 1)).add ((cR (hG 0 0)).const_mul _)
  refine Measurable.ite (measurableSet_lt measurable_const hd) ?_ measurable_const
  refine (((cR hd).pow_const _).mul (hq.pow_const _)).mul ?_
  exact Complex.measurable_exp.comp ((hp.div hq).const_mul _)

theorem measurable_first_gaussian_matrix (n : ℤ) {A : α → Mt} (hA : MM A) : Measurable fun a => phi1 n (A a) := by
  unfold phi1 zR nrm
  have hz : Measurable fun a => (((A a 0 0 + A a 1 1 : ℝ) : ℂ) + Complex.I * ((A a 1 0 - A a 0 1 : ℝ) : ℂ)) :=
    (cR ((hA 0 0).add (hA 1 1))).add ((cR ((hA 1 0).sub (hA 0 1))).const_mul _)
  have hn : Measurable fun a => ∑ i, ∑ j, A a i j ^ 2 := by
    simp only [Fin.sum_univ_two]
    exact (((hA 0 0).pow_const 2).add ((hA 0 1).pow_const 2)).add
      (((hA 1 0).pow_const 2).add ((hA 1 1).pow_const 2))
  exact (hz.pow_const _).mul (cR (Real.measurable_exp.comp (hn.const_mul _)))

theorem measurable_second_gaussian_vector (k : ℕ) (n : ℤ) {ξ : α → Fin 2 → ℝ} (h : ∀ i, Measurable fun a => ξ a i) :
    Measurable fun a => phi2h k n (ξ a) := by
  unfold phi2h
  refine ((((cR (h 1)).add ((cR (h 0)).const_mul _)).pow_const _)).mul ?_
  exact cR (Real.measurable_exp.comp
    ((((h 0).pow_const 2).add ((h 1).pow_const 2)).const_mul _))

theorem absc_m {A : α → Mt} (hA : MM A) (c : ℂ) :
    Measurable fun a => ((|(A a).det| : ℝ) : ℂ) ^ c :=
  (cR (det_m hA).abs).pow_const c

theorem measurable_section_matrix : MM fun q : M22 × Yc => sec2 q.2 := by
  have h0 : Measurable fun q : M22 × Yc => q.2.1 0 := (measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)
  have h1 : Measurable fun q : M22 × Yc => q.2.1 1 := (measurable_pi_apply 1).comp (measurable_fst.comp measurable_snd)
  have hd : Measurable fun q : M22 × Yc => q.2.2 := measurable_snd.comp measurable_snd
  have hn : Measurable fun q : M22 × Yc => nv q.2.1 := by
    unfold nv
    exact (h0.pow_const 2).add (h1.pow_const 2)
  intro i j
  fin_cases i <;> fin_cases j <;> simp [sec2]
  · exact (hd.mul h1).div hn
  · exact (hd.mul h0).neg.div hn
  · exact h0
  · exact h1

theorem of_m : MM fun q : M22 × Yc => (Matrix.of q.1 : Mt) := by
  intro i j
  exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst)

theorem main (k : ℕ) (n : ℤ) (s : ℂ) :
    Measurable (fun q : M22 × Yc => Uf k n s (sec2 q.2) (Matrix.of q.1)) ∧
    Measurable (fun q : M22 × Yc => Vf k n s (sec2 q.2) (Matrix.of q.1)) := by
  have hh := measurable_section_matrix
  have hg := of_m
  have hk := mul_m hh (inv_m hg)
  have hgd : Measurable fun q : M22 × Yc => sg (Matrix.of q.1 : Mt).det := sg_m (det_m hg)
  constructor
  · unfold Uf
    exact (((absc_m hh s).mul (Wm_m k hk)).mul (measurable_second_gaussian_vector k n (fun i => hk 1 i))).mul
      (WthR_m n (glOf_m hh)) |>.mul (((measurable_first_gaussian_matrix n hg).mul hgd).mul (absc_m hg _))
  · unfold Vf
    have hv : MM fun q : M22 × Yc => (glOf (sec2 q.2) * glOf (Matrix.of q.1 : Mt)).val := by
      simpa using mul_m (glOf_m hh) (glOf_m hg)
    exact (((absc_m hh s).mul (Wm_m k hh)).mul (measurable_second_gaussian_vector k n (fun i => hh 1 i))).mul
      ((((measurable_first_gaussian_matrix n hg).mul hgd).mul (absc_m hg _)).mul (WthR_m n hv))

end GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst.Meas

end

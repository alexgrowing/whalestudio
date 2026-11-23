import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCount.SpinRel

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def quadM (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • ∑ e, c a e * c e b

theorem term_comm {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b d g e : Fin n) :
    c a e * c e b * c d g - c d g * (c a e * c e b) =
      (if b = d then (if e = g then (2 : ℂ) • c a g else 0) else 0) -
        (if a = g then (if e = d then (2 : ℂ) • c d b else 0) else 0) := by
  have h1 := hc.1 e b d g
  have h2 := hc.1 a e d g
  have h : c a e * c e b * c d g - c d g * (c a e * c e b) =
      c a e * (c e b * c d g + c d g * c e b) - (c a e * c d g + c d g * c a e) * c e b := by
    noncomm_ring
  rw [h, h1, h2]
  by_cases hbd : b = d <;> by_cases heg : e = g <;> by_cases hag : a = g <;> by_cases hed : e = d <;>
    simp only [hbd, heg, hag, hed, and_self, and_true, and_false, true_and, false_and, if_true, if_false,
      mul_zero, zero_mul, sub_zero, two_smul, mul_two, two_mul] <;> simp_all [two_smul, mul_two, two_mul]

theorem quad_c {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b d g : Fin n) :
    quadM c a b * c d g - c d g * quadM c a b =
      (if b = d then c a g else 0) - (if a = g then c d b else 0) := by
  have h : quadM c a b * c d g - c d g * quadM c a b =
      (1 / 2 : ℂ) • ∑ e, (c a e * c e b * c d g - c d g * (c a e * c e b)) := by
    simp only [quadM, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum, ← smul_sub,
      Finset.sum_sub_distrib]
  rw [h]
  simp only [term_comm hc, Finset.sum_sub_distrib]
  by_cases hbd : b = d <;> by_cases hag : a = g <;>
    simp [hbd, hag, smul_sub, smul_smul]

theorem quad_quad {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b d e : Fin n) :
    quadM c a b * quadM c d e - quadM c d e * quadM c a b =
      (if b = d then quadM c a e else 0) - (if e = a then quadM c d b else 0) := by
  have h : ∀ f, quadM c a b * (c d f * c f e) - (c d f * c f e) * quadM c a b =
      ((if b = d then c a f else 0) - (if a = f then c d b else 0)) * c f e +
        c d f * ((if b = f then c a e else 0) - (if a = e then c f b else 0)) := by
    intro f
    rw [← quad_c hc a b d f, ← quad_c hc a b f e]
    noncomm_ring
  have h2 : quadM c a b * quadM c d e - quadM c d e * quadM c a b =
      (1 / 2 : ℂ) • ∑ f, (quadM c a b * (c d f * c f e) - (c d f * c f e) * quadM c a b) := by
    conv_lhs => rw [show quadM c d e = (1 / 2 : ℂ) • ∑ f, c d f * c f e from rfl]
    simp only [smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum, ← smul_sub,
      Finset.sum_sub_distrib]
  rw [h2]
  simp only [h, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  by_cases hbd : b = d <;> by_cases hae : a = e
  · have hea : e = a := hae.symm
    simp [hbd, hae, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel
  · have hea : ¬ e = a := fun h => hae h.symm
    simp [hbd, hae, hea, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel
  · have hea : e = a := hae.symm
    simp [hbd, hae, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel
  · have hea : ¬ e = a := fun h => hae h.symm
    simp [hbd, hae, hea, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel

theorem spinM_eq (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) :
    spinM c a b = quadM c a b - (if a = b then ((n : ℂ) / 2) • (1 : Matrix ι ι ℂ) else 0) := rfl

theorem spin_glRel {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) : Formalism.REAL.GlRel (spinM c) := by
  intro a b d e
  have h := quad_quad hc a b d e
  have hcomm : spinM c a b * spinM c d e - spinM c d e * spinM c a b =
      quadM c a b * quadM c d e - quadM c d e * quadM c a b := by
    simp only [spinM_eq]
    by_cases hab : a = b <;> by_cases hde : d = e <;>
      simp only [hab, hde, if_true, if_false, sub_zero, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one] <;> module
  rw [hcomm, h]
  by_cases hbd : b = d
  · by_cases hea : e = a
    · subst hbd
      subst hea
      simp [spinM_eq]
    · have hae : ¬ a = e := fun h => hea h.symm
      subst hbd
      simp [spinM_eq, hea, hae]
  · by_cases hea : e = a
    · have hdb : ¬ d = b := fun h => hbd h.symm
      simp [spinM_eq, hbd, hea, hdb]
    · simp [hbd, hea]

theorem spin_conjTranspose {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b : Fin n) :
    (spinM c a b)ᴴ = spinM c b a := by
  simp only [spinM_eq, quadM]
  by_cases hab : a = b
  · subst hab
    simp [conjTranspose_sum, conjTranspose_mul, hc.2, conjTranspose_smul, Complex.conj_ofNat]
  · simp [hab, Ne.symm hab, conjTranspose_sum, conjTranspose_mul, hc.2, conjTranspose_smul]

theorem spinRel : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    Formalism.REAL.GlRel (spinM c) ∧ ∀ a b, (spinM c a b)ᴴ = spinM c b a :=
  fun _ hc => ⟨spin_glRel hc, spin_conjTranspose hc⟩

end GlobalTheory.CompanionTheory.RealCount.SpinRel

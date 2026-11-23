import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefMod

noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame

abbrev Var (ι : Type) (d a : ℕ) : Type := ι × Fin d × Fin a

abbrev Pol (ι : Type) (d a : ℕ) : Type := MvPolynomial (Var ι d a) ℂ

abbrev Tup (ι : Type) (a d : ℕ) (n : ι → ℕ) : Type := ∀ τ, Fin (n τ) → {s : Fin a → Fin d // StrictMono s}

variable {ι : Type}

def minorAt (τ : ι) {a d : ℕ} (s : Fin a → Fin d) : Pol ι d a :=
  (Matrix.of fun i i' : Fin a => (X (τ, s i, i') : Pol ι d a)).det

variable [Fintype ι]

def prodMinors {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : Pol ι d a := ∏ τ, ∏ j, minorAt τ (T τ j).1

def rowSub {d a : ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) : Pol ι d a →ₐ[ℂ] Pol ι d a :=
  aeval fun y => ∑ i' : Fin d, C (κ y.1 i' y.2.1) * X (y.1, i', y.2.2)

def colSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) : Pol ι d a →ₐ[ℂ] Pol ι d a :=
  aeval fun y => ∑ j' : Fin a, C (g y.1 j' y.2.2) * X (y.1, y.2.1, j')

def detChar {a : ℕ} (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) : ℂ := ∏ τ, (g τ).det ^ n τ

def inv (a d : ℕ) (n : ι → ℕ) : Submodule ℂ (Pol ι d a) where
  carrier := {P | ∀ g : ι → Matrix.unitaryGroup (Fin a) ℂ,
    colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P = detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • P}
  add_mem' := by
    intro P Q hP hQ g
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, hP g, hQ g, smul_add]
  zero_mem' := by
    intro g
    simp
  smul_mem' := by
    intro c P hP g
    simp only [Set.mem_setOf_eq] at *
    rw [map_smul, hP g, smul_comm]

end GlobalTheory.MinorFrame

namespace GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

theorem colSub_minorAt {a d : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) (s : Fin a → Fin d) :
    colSub g (minorAt τ s) = (g τ).det • minorAt τ s := by
  unfold minorAt
  rw [AlgHom.map_det]
  have hM : (colSub g : Pol ι d a →ₐ[ℂ] Pol ι d a).mapMatrix (Matrix.of fun i i' : Fin a => (X (τ, s i, i') : Pol ι d a)) =
      (Matrix.of fun i i' : Fin a => (X (τ, s i, i') : Pol ι d a)) * (g τ).map C := by
    ext i i'
    simp [colSub, Matrix.mul_apply, mul_comm]
  rw [hM, Matrix.det_mul, show ((g τ).map C).det = C (g τ).det from ((C : ℂ →+* Pol ι d a).map_det (g τ)).symm, smul_eq_C_mul, mul_comm]

theorem colSub_prodMinors {a d : ℕ} {n : ι → ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (T : Tup ι a d n) :
    colSub g (prodMinors T) = detChar n g • prodMinors T := by
  unfold prodMinors detChar
  simp only [map_prod, colSub_minorAt, smul_eq_C_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, map_prod, map_pow]

theorem prodMinors_mem_inv {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : prodMinors T ∈ inv a d n :=
  fun g => colSub_prodMinors _ T

theorem colSub_rowSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (κ : ι → Matrix (Fin d) (Fin d) ℂ) (P : Pol ι d a) :
    colSub g (rowSub κ P) = rowSub κ (colSub g P) := by
  have : (colSub g).comp (rowSub κ) = (rowSub κ).comp (colSub g) := by
    apply MvPolynomial.algHom_ext
    intro y
    simp only [AlgHom.comp_apply, rowSub, colSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this

theorem rowSub_mem_inv {a d : ℕ} {n : ι → ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) {P : Pol ι d a} (hP : P ∈ inv a d n) :
    rowSub κ P ∈ inv a d n := by
  intro g
  rw [colSub_rowSub, hP g, map_smul]

end GlobalTheory.MinorFrame

namespace GlobalTheory.MinorFrame

open Classical

variable {ι : Type} [Fintype ι]

theorem fockS_conj {σ : Type} (f g : MvPolynomial σ ℂ) :
    Formalism.L2.DIV.fockS f g = starRingEnd ℂ (Formalism.L2.DIV.fockS g f) := by
  rw [Formalism.L2.DIV.fockS_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [map_mul, map_natCast, RCLike.star_def, Complex.conj_conj]
  ring

theorem fockS_self_re_pos {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) : 0 < (Formalism.L2.DIV.fockS f f).re := by
  unfold Formalism.L2.DIV.fockS
  rw [Complex.re_sum]
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hf
  have hms : m ∈ f.support := MvPolynomial.mem_support_iff.2 hm
  have key : ∀ k ∈ f.support, (star (f.coeff k) * f.coeff k * (Formalism.L2.DIV.mfact k : ℂ)).re =
      ‖f.coeff k‖ ^ 2 * (Formalism.L2.DIV.mfact k : ℝ) := by
    intro k _
    rw [RCLike.star_def, mul_comm (starRingEnd ℂ _), Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [Finset.sum_congr rfl key]
  have hpos : 0 < ‖f.coeff m‖ ^ 2 * (Formalism.L2.DIV.mfact m : ℝ) := by
    have : (0 : ℝ) < Formalism.L2.DIV.mfact m := by
      unfold Formalism.L2.DIV.mfact; exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _
    positivity
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun k => ‖f.coeff k‖ ^ 2 * (Formalism.L2.DIV.mfact k : ℝ))
    (fun k _ => by positivity) hms)

end GlobalTheory.MinorFrame

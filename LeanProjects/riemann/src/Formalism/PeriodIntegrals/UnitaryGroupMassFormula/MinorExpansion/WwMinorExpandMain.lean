import Mathlib
import Formalism.PeriodIntegrals.WwMinorExpand
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.DetSubmatrixFun

open Finset

noncomputable section

namespace PI.WwMinorExpandWork

open PI.WwMinorExpand

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)

def minX (s : Lt) (p : ℕ) (J : Fin p ↪o Fin N0) : MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  Matrix.det (Matrix.of fun i k : Fin p =>
    (MvPolynomial.X (s, (i : ℕ), J k) : MvPolynomial (Lt × ℕ × Fin N0) ℤ))

def RepM (s : Lt) (p : ℕ) (x : MvPolynomial (KM.XZ Lt N0 N1) ℤ) : Prop :=
  ∃ d : (Fin p ↪o Fin N0) → MvPolynomial (Lt × Fin N0 × Fin N1) ℤ,
    x = ∑ J, MvPolynomial.rename Sum.inl (minX N0 s p J) * MvPolynomial.rename Sum.inr (d J)

theorem repM_zero (s : Lt) (p : ℕ) : RepM N0 N1 s p 0 :=
  ⟨0, by simp⟩

theorem repM_add (s : Lt) (p : ℕ) {x y : MvPolynomial (KM.XZ Lt N0 N1) ℤ}
    (hx : RepM N0 N1 s p x) (hy : RepM N0 N1 s p y) : RepM N0 N1 s p (x + y) := by
  obtain ⟨d, rfl⟩ := hx
  obtain ⟨e, rfl⟩ := hy
  refine ⟨d + e, ?_⟩
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem repM_single (s : Lt) (p : ℕ) (J : Fin p ↪o Fin N0) (c : MvPolynomial (Lt × Fin N0 × Fin N1) ℤ) :
    RepM N0 N1 s p (MvPolynomial.rename Sum.inl (minX N0 s p J) * MvPolynomial.rename Sum.inr c) := by
  classical
  refine ⟨fun J' => if J' = J then c else 0, ?_⟩
  simp only [apply_ite, map_zero, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem minor_rep (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    RepM N0 N1 s p (KM.minorXZ N0 N1 s p I) := by
  classical
  let A : Matrix (Fin p) (Fin N0) (MvPolynomial (KM.XZ Lt N0 N1) ℤ) :=
    Matrix.of fun i a => MvPolynomial.X (Sum.inl (s, (i : ℕ), a))
  let B : Matrix (Fin N0) (Fin p) (MvPolynomial (KM.XZ Lt N0 N1) ℤ) :=
    Matrix.of fun a k => MvPolynomial.X (Sum.inr (s, a, I k))
  have hAB : KM.minorXZ N0 N1 s p I = (A * B).det := by
    unfold KM.minorXZ
    congr 1
  have hA : ∀ J : Fin p ↪o Fin N0,
      (A.submatrix id J).det = MvPolynomial.rename Sum.inl (minX N0 s p J) := by
    intro J
    rw [minX, AlgHom.map_det]
    congr 1
    ext i k
    simp [A]
  rw [hAB, GenFrameSpan.det_mul_rect]
  refine Finset.sum_induction _ (RepM N0 N1 s p) (fun x y hx hy => repM_add N0 N1 s p hx hy)
    (repM_zero N0 N1 s p) (fun f _ => ?_)
  have hB : (∏ i, B (f i) i) =
      MvPolynomial.rename Sum.inr (∏ i, (MvPolynomial.X (s, f i, I i) :
        MvPolynomial (Lt × Fin N0 × Fin N1) ℤ)) := by
    simp [map_prod, B]
  rcases GenFrameSpan.det_submatrix_fun A f with h0 | ⟨J, e, he⟩
  · rw [h0, mul_zero]
    exact repM_zero N0 N1 s p
  · have : (∏ i, B (f i) i) * (A.submatrix id f).det =
        MvPolynomial.rename Sum.inl (minX N0 s p J) *
          MvPolynomial.rename Sum.inr ((e : MvPolynomial (Lt × Fin N0 × Fin N1) ℤ) *
            ∏ i, (MvPolynomial.X (s, f i, I i) : MvPolynomial (Lt × Fin N0 × Fin N1) ℤ)) := by
      rw [he, hA, hB, map_mul, map_intCast]
      ring
    rw [this]
    exact repM_single N0 N1 s p J _

theorem wwMinorExpand_main : WwMinorExpand := by
  intro Lt _ _ N0 N1 nu I
  have h := fun (s : Lt) (c : Fin ((nu s).rowLen 0)) =>
    minor_rep N0 N1 s ((nu s).colLen c) (I s c)
  choose d hd using h
  refine ⟨fun J => ∏ s, ∏ c, d s c (J s c), ?_⟩
  change _ = ∑ᶠ J : (∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N0),
    MvPolynomial.rename Sum.inl (KM.nablaX N0 nu J) *
      MvPolynomial.rename Sum.inr (∏ s, ∏ c, d s c (J s c))
  rw [finsum_eq_sum_of_fintype]
  unfold KM.Gxz
  simp_rw [hd]
  simp_rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp only [KM.nablaX, minX, map_prod, ← Finset.prod_mul_distrib]

end PI.WwMinorExpandWork

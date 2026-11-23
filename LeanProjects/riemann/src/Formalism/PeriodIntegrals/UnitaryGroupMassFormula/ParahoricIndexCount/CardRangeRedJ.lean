import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ParahoricIndexCount.ThetaInjective

noncomputable section

open Matrix Formalism.DoubleCosetMeasures.P.GLRed

namespace PI.ParahoricIdxZ.W

section B

variable {F : Type} [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O)

def redJ {a : ℕ} (J' : Subgroup (GL (Fin a) F)) (hJ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a) :
    J' →* GL (Fin a) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) :=
  (red O a ϖ hϖ).comp (Subgroup.inclusion hJ)

theorem card_range_redJ (hϖ0 : ϖ ≠ 0) {a : ℕ} (J' : Subgroup (GL (Fin a) F))
    (hJ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a) :
    Nat.card (redJ O ϖ hϖ J' hJ).range = Nat.card (J' ⧸ (Formalism.DoubleCosetMeasures.congSub O ϖ a).subgroupOf J') := by
  have hk : (redJ O ϖ hϖ J' hJ).ker = (Formalism.DoubleCosetMeasures.congSub O ϖ a).subgroupOf J' := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change red O a ϖ hϖ (Subgroup.inclusion hJ k) = 1 ↔ _
    rw [← MonoidHom.mem_ker, ker_red O ϖ hϖ hϖ0, Subgroup.mem_subgroupOf]
    rfl
  rw [← hk]
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv).symm

theorem mk_congr {u v : F} (hu : u ∈ O) (hv : v ∈ O) (h : u = v) :
    Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (⟨u, hu⟩ : O) =
      Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (⟨v, hv⟩ : O) := by
  subst h; rfl

theorem mk_eq_zero {u : F} (hu : u ∈ O) (o : F) (ho : o ∈ O) (h : u = ϖ * o) :
    Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (⟨u, hu⟩ : O) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨⟨o, ho⟩, Subtype.ext (by simp [h, mul_comm])⟩

theorem red_eq_theta {a t : ℕ} (h : Formalism.DoubleCosetMeasures.GLint O (a + t))
    (A : Matrix (Fin a) (Fin a) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) (B : Matrix (Fin a) (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))
    (C : Matrix (Fin t) (Fin a) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) (D : Matrix (Fin t) (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))
    (H : ∀ x y, Ideal.Quotient.mk _ (⟨((h : GL (Fin (a + t)) F) : Matrix _ _ F)
      (finSumFinEquiv x) (finSumFinEquiv y), h.2.1 _ _⟩ : O) = Matrix.fromBlocks A B C D x y) :
    ((red O (a + t) ϖ hϖ h : GL (Fin (a + t)) _) : Matrix _ _ _) = theta A B C D := by
  ext i j
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  rw [red_val, theta_apply]
  exact H x y

theorem mk_entry {a t : ℕ} (g : Formalism.DoubleCosetMeasures.GLint O (a + t)) {A : Matrix (Fin a) (Fin a) F}
    {B : Matrix (Fin a) (Fin t) F} {C : Matrix (Fin t) (Fin a) F} {D : Matrix (Fin t) (Fin t) F}
    (hg : ((g : GL (Fin (a + t)) F) : Matrix _ _ F) = theta A B C D) (x y : Fin a ⊕ Fin t)
    (hv : Matrix.fromBlocks A B C D x y ∈ O) :
    Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (⟨((g : GL (Fin (a + t)) F) : Matrix _ _ F)
      (finSumFinEquiv x) (finSumFinEquiv y), g.2.1 _ _⟩ : O) =
      Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (⟨Matrix.fromBlocks A B C D x y, hv⟩ : O) :=
  mk_congr O ϖ hϖ _ _ (by rw [hg, theta_apply])

end B

end PI.ParahoricIdxZ.W

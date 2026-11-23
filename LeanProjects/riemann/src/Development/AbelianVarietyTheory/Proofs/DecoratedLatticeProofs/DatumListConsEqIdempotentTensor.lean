import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrOfMulEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.PutIn

theorem datJ_cons : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (Ψ : ι → Matrix n n' k → ℂ) (i : ι) (J : List ι), i ∉ J → (∀ j ∈ J, (p i).e * (p j).e = 0) → GlobalTheory.FinPl.PutIn.datJ p α β Ψ (i :: J) = GlobalTheory.FinPl.PutIn.tens (p i).e (GlobalTheory.FinPl.PutIn.datJ p α β Ψ J) (extFun (α i) (β i) (Ψ i)) := by
  intro D k _ _ _ _ ι p n n' _ _ _ _ S T α β Ψ i J _ horth
  funext t
  have he : eSum p J * (p i).e = 0 := eSum_mul p _ J fun j hj => by rw [mul_comm]; exact horth j hj
  have hii : (p i).e * (p i).e = (p i).e := (p i).split.1

  have hhalf : IsHalf (eSum p (i :: J)) t ↔ IsHalf (eSum p J) (t - (p i).e • t) := by
    rw [eSum_cons]
    constructor
    · intro h a b
      have := h a b
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
      rw [mul_sub, ← mul_assoc, he, zero_mul, sub_zero]
      linear_combination this
    · intro h a b
      have := h a b
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
      rw [mul_sub, ← mul_assoc, he, zero_mul, sub_zero] at this
      linear_combination this
  have hself : IsHalf (p i).e ((p i).e • t) := by
    intro a b
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← mul_assoc, hii]
  have hrdi : rd (α i) (β i) ((p i).e • t) = rd (α i) (β i) t := by
    unfold rd
    congr 2
    ext a b
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, pr_e]
  have hrdj : ∀ j ∈ J, rd (α j) (β j) (t - (p i).e • t) = rd (α j) (β j) t := by
    intro j hj
    have h0 : (p j).pr (p i).e = 0 := pr_of_mul_eq_zero (p j) (by rw [mul_comm]; exact horth j hj)
    unfold rd
    congr 2
    ext a b
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_sub, h0]
  have hprod : (J.map fun j => Ψ j (rd (α j) (β j) (t - (p i).e • t))).prod = (J.map fun j => Ψ j (rd (α j) (β j) t)).prod := by
    congr 1
    exact List.map_congr_left fun j hj => by rw [hrdj j hj]
  simp only [datJ, tens, extFun, if_pos hself, hrdi, List.map_cons, List.prod_cons]
  by_cases h : IsHalf (eSum p J) (t - (p i).e • t)
  · rw [if_pos (hhalf.2 h), if_pos h, hprod, mul_comm]
  · rw [if_neg (fun h' => h (hhalf.1 h')), if_neg h, zero_mul]

end GlobalTheory.FinPl.PutIn
end

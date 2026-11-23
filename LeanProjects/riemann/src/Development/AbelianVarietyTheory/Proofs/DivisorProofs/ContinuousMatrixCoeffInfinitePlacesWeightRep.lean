import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwiningGlOfUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAutRepOfVecFun
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

theorem continuous_coef_piTensorMap {X ι : Type} [TopologicalSpace X] [Fintype ι] {M : ι → Type}
    [∀ c, AddCommGroup (M c)] [∀ c, Module ℂ (M c)] [∀ c, Module.Finite ℂ (M c)]
    (f : X → ∀ c, M c →ₗ[ℂ] M c)
    (hf : ∀ c (x : M c) (ℓ : Module.Dual ℂ (M c)), Continuous fun g => ℓ (f g c x))
    (u : PiTensorProduct ℂ M) (ℓ : Module.Dual ℂ (PiTensorProduct ℂ M)) :
    Continuous fun g => ℓ (PiTensorProduct.map (f g) u) := by
  classical
  let bc := fun c => Module.Free.chooseBasis ℂ (M c)
  let B := Basis.piTensorProduct bc
  have key : ∀ k k', Continuous fun g => B.repr (PiTensorProduct.map (f g) (B k)) k' := by
    intro k k'
    simp only [B, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod, Basis.piTensorProduct_repr_tprod_apply]
    exact continuous_finset_prod _ fun c _ => by
      simpa [Module.Basis.coord_apply] using hf c (bc c (k c)) ((bc c).coord (k' c))
  have h : ∀ g, ℓ (PiTensorProduct.map (f g) u) =
      ∑ k, ∑ k', B.repr u k * (B.repr (PiTensorProduct.map (f g) (B k)) k' * ℓ (B k')) := by
    intro g
    conv_lhs => rw [← B.sum_repr u]
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_lhs => rw [← B.sum_repr (PiTensorProduct.map (f g) (B k))]
    simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  simp_rw [h]
  exact continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun k' _ =>
    continuous_const.mul ((key k k').mul continuous_const)

theorem continuous_coef_sqRep (n : ℕ) (mu : DomWeight n) (x : nablaSq ℂ n mu) (ℓ : Module.Dual ℂ (nablaSq ℂ n mu)) :
    Continuous fun a : GL (Fin n) ℂ => ℓ (GlobalTheory.Branching.sqRep ℂ n mu a x) := by
  obtain ⟨P, hP⟩ := GlobalTheory.Branching.exists_coef_sqRep n mu x ℓ
  simp only [hP]
  exact (Units.continuous_val.matrix_det.zpow₀ _
      fun a : GL (Fin n) ℂ => Or.inl (Matrix.GeneralLinearGroup.det a).ne_zero).mul
    ((MvPolynomial.continuous_eval P).comp (continuous_pi fun i => Units.continuous_val.matrix_elem i.1 i.2))

theorem continuous_coef_wInf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (lam : InfinitePlace E → DomWeight n) (u : Wsp lam) (ℓ : Module.Dual ℂ (Wsp lam)),
    Continuous fun g : UA E n => ℓ (wInf lam g u) := by
  intro E _ _ _ n lam u ℓ
  exact continuous_coef_piTensorMap
    (fun g v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding g))
    (fun v x ℓ' => (continuous_coef_sqRep n (lam v) x ℓ').comp (GlobalTheory.AutRec.continuous_cEmb_emb _)) u ℓ

end GlobalTheory.BCT.TrKer

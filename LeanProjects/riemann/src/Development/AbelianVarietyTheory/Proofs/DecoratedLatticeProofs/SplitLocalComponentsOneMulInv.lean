import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmEqSumLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

noncomputable section
namespace GlobalTheory.LocOm

theorem isLoc_one_mul_inv : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (V : HSp D) (Z : Type) [Fintype Z] [DecidableEq Z] (F : Frame k V.rank Z), p.IsLoc F 1 1 ∧ (∀ (g g' : GA D V) (gk gk' : GL Z k), p.IsLoc F g gk → p.IsLoc F g' gk' → p.IsLoc F (g * g') (gk * gk')) ∧ ∀ (g : GA D V) (gk : GL Z k), p.IsLoc F g gk → p.IsLoc F g⁻¹ gk⁻¹ := by
  intro D k _ _ _ _ p V Z _ _ F
  have hmul : ∀ g g' : GA D V, (mt V (g * g')).map p.π = (mt V g).map p.π * (mt V g').map p.π := fun g g' => by
    rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.map_mul]
  refine ⟨⟨GlobalTheory.SplitLinear.suppAt_one _ _, ?_⟩, fun g g' gk gk' h h' => ⟨GlobalTheory.SplitLinear.suppAt_mul h.1 h'.1, ?_⟩,
    fun g gk h => ⟨GlobalTheory.SplitLinear.suppAt_inv h.1, ?_⟩⟩
  · rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero p.π) (map_one p.π), Units.val_one, Matrix.mul_one, F.βγ]
  · rw [hmul, h.2, h'.2, Units.val_mul]
    rw [Matrix.mul_assoc (F.β * gk.val), ← Matrix.mul_assoc F.γ, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  · have e1 : (mt V g⁻¹).map p.π * (F.β * gk.val * F.γ) = 1 := by
      rw [← h.2, ← hmul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero p.π) (map_one p.π)]
    have e2 : (F.β * gk.val * F.γ) * (F.β * (gk⁻¹).val * F.γ) = 1 := by
      rw [Matrix.mul_assoc (F.β * gk.val), ← Matrix.mul_assoc F.γ, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul,
        Matrix.mul_assoc F.β, ← Matrix.mul_assoc gk.val, Units.mul_inv, Matrix.one_mul, F.βγ]
    calc (mt V g⁻¹).map p.π = (mt V g⁻¹).map p.π * ((F.β * gk.val * F.γ) * (F.β * (gk⁻¹).val * F.γ)) := by
          rw [e2, Matrix.mul_one]
      _ = F.β * (gk⁻¹).val * F.γ := by rw [← Matrix.mul_assoc, e1, Matrix.one_mul]

end GlobalTheory.LocOm
end

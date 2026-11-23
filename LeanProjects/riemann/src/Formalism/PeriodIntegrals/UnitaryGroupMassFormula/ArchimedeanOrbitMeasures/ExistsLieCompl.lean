import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GoodChartExOfStd

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

section Lie

variable {V : Type} [Fintype V] {n : ℕ}

def lieK (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) : Submodule ℝ (V → Matrix (Fin n) (Fin n) ℂ) where
  carrier := {M | ∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧
    ∀ i ∈ S v, ∀ j ∈ S v, M v i j = 0}
  zero_mem' := by intro v; simp
  add_mem' := by
    intro A B hA hB v
    refine ⟨?_, fun i hi j hj => ?_⟩
    · have e : (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) =
          ((A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * A v) +
            ((B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * B v) := by
        rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]; abel
      show (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) = 0
      rw [e, (hA v).1, (hB v).1, add_zero]
    · show A v i j + B v i j = 0
      rw [(hA v).2 i hi j hj, (hB v).2 i hi j hj, add_zero]
  smul_mem' := by
    intro c A hA v
    refine ⟨?_, fun i hi j hj => ?_⟩
    · show (c • A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (c • A v) = 0
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, (hA v).1,
        smul_zero]
    · show c • A v i j = 0
      rw [(hA v).2 i hi j hj, smul_zero]

def entL (V : Type) [Fintype V] (n : ℕ) :
    (V → Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℝ] EuclideanSpace ℂ (V × Fin n × Fin n) :=
  ({ toFun := fun M p => M p.1 p.2.1 p.2.2
     invFun := fun f v i j => f (v, i, j)
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } : (V → Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℝ] (V × Fin n × Fin n → ℂ)).trans
    ((EuclideanSpace.equiv (V × Fin n × Fin n) ℂ).toLinearEquiv.restrictScalars ℝ).symm

theorem entL_apply (M : V → Matrix (Fin n) (Fin n) ℂ) (p : V × Fin n × Fin n) :
    (EuclideanSpace.equiv (V × Fin n × Fin n) ℂ) (entL V n M) p = M p.1 p.2.1 p.2.2 := by
  simp [entL] <;> rfl

theorem norm_entL_sq (M : V → Matrix (Fin n) (Fin n) ℂ) :
    ‖entL V n M‖ ^ 2 = ∑ v, ∑ i, ∑ j, ‖M v i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := entL_apply M (v, i, j)
  simp only [EuclideanSpace.equiv] at this
  rw [← this]
  rfl

theorem exists_lieCompl (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) :
    ∃ (ι : Type) (_ : Fintype ι) (L : EuclideanSpace ℝ ι →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ)),
      (∀ x v, (L x v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * L x v = 0 ∧
        ∀ i ∈ S v, ∀ j ∈ S v, L x v i j = 0) ∧
      (∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2) ∧
      ∀ M : V → Matrix (Fin n) (Fin n) ℂ,
        (∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧ ∀ i ∈ S v, ∀ j ∈ S v, M v i j = 0) →
          ∃ x, L x = M := by
  set K' : Submodule ℝ (EuclideanSpace ℂ (V × Fin n × Fin n)) := (lieK ε S).map (entL V n).toLinearMap with hK'
  let b := stdOrthonormalBasis ℝ K'
  let L : EuclideanSpace ℝ (Fin (Module.finrank ℝ K')) →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ) :=
    (entL V n).symm.toLinearMap ∘ₗ K'.subtype ∘ₗ b.repr.symm.toLinearEquiv.toLinearMap
  have hLe : ∀ x, entL V n (L x) = (b.repr.symm x : EuclideanSpace ℂ (V × Fin n × Fin n)) := by
    intro x; simp [L]
  have hLK : ∀ x, L x ∈ lieK ε S := by
    intro x
    obtain ⟨M, hM, hMe⟩ := (b.repr.symm x).2
    have : L x = M := by
      apply (entL V n).injective
      rw [hLe]; exact hMe.symm
    rw [this]; exact hM
  refine ⟨Fin (Module.finrank ℝ K'), inferInstance, L, fun x v => hLK x v, fun x => ?_, fun M hM => ?_⟩
  · rw [← norm_entL_sq, hLe]
    exact congrArg (· ^ 2) (b.repr.symm.norm_map x)
  · have hM' : entL V n M ∈ K' := ⟨M, hM, rfl⟩
    refine ⟨b.repr ⟨entL V n M, hM'⟩, ?_⟩
    apply (entL V n).injective
    rw [hLe, LinearIsometryEquiv.symm_apply_apply]

end Lie

def StdConjEx : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I,
    ∃ (c : X.B.I.Ginf) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)), StdConj X hb u' c S

theorem stdDataEx_of (h : StdConjEx) : StdDataEx := by
  intro D X u' ψ hT μinf νinf fibInf hP hb
  obtain ⟨c, S, hc⟩ := h X u' ψ hT μinf νinf fibInf hP hb
  obtain ⟨ι, hι, L, h1, h2, h3⟩ := exists_lieCompl X.B.I.ε S
  exact ⟨c, S, ι, hι, L, hc, ⟨h1, h2, h3⟩⟩

end PI.AprimeInfW

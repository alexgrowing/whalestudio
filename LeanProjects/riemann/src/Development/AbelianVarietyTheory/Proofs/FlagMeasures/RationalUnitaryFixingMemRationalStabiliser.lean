import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGramStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryStabiliserOrthogonalSummand
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Transfer
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.RtUnitaryOf

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem rat_unitary_fixing_mem_gam : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ₀ : GL (Fin X.B.I.n) X.B.I.E), γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J → (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) → ∃ γ : Gam X u, (∀ v, uMat ((γ : X.B.I.GA).1 v) = (X.B.I.P v)⁻¹ * (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v) ∧ X.B.I.fmat (γ : X.B.I.GA).2 = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := by
  intro D X u γ₀ hγ₀ hfix
  have hs : (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)).comp (starRingEnd X.B.I.E) =
      (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)).comp (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := by
    ext e
    exact (PI.UnitaryGroupMassFormula.InHHClassFin.rt_sig X.B.I e).symm
  have hm := Formalism.UG.P.bc_mem _ _ _ hs X.B.I.J γ₀ hγ₀
  let g : X.B.I.Gf := ⟨_, hm⟩
  have hg : X.B.I.fmat g = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
      (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) :=
    Formalism.UG.P.bc_coe _ γ₀
  have hinf : (fun v => PI.UnitaryGroupMassFormula.InHHClassFin.rtReal X.B.I γ₀ hγ₀ v) ∈ Hinf X u := by
    intro v y hy
    have hP : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (X.B.I.P_unit v))
    show uMat (PI.UnitaryGroupMassFormula.InHHClassFin.rtReal X.B.I γ₀ hγ₀ v) *ᵥ
        ((X.B.I.P v)⁻¹ *ᵥ fun i => X.B.I.φ v (y i)) = (X.B.I.P v)⁻¹ *ᵥ fun i => X.B.I.φ v (y i)
    rw [PI.UnitaryGroupMassFormula.InHHClassFin.rt_uMat, Matrix.mulVec_mulVec, Matrix.mul_assoc _ (X.B.I.P v), hP,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    exact (RingHom.map_mulVec (X.B.I.φ v) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) y i).symm.trans
      (congrArg (X.B.I.φ v) (congrFun (hfix y hy) i))
  have hfin : g ∈ Hfin X u := by
    intro y hy
    rw [hg]
    funext i
    exact (RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))
      (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) y i).symm.trans
      (congrArg _ (congrFun (hfix y hy) i))
  refine ⟨⟨(fun v => PI.UnitaryGroupMassFormula.InHHClassFin.rtReal X.B.I γ₀ hγ₀ v, g), ?_⟩, ?_, ?_⟩
  · show _ ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ⊓ (Hinf X u).prod (Hfin X u)
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_prod.2 ⟨hinf, hfin⟩⟩
    exact ⟨γ₀, hγ₀, fun v => PI.UnitaryGroupMassFormula.InHHClassFin.rt_uMat X.B.I γ₀ hγ₀ v, hg⟩
  · intro v
    exact PI.UnitaryGroupMassFormula.InHHClassFin.rt_uMat X.B.I γ₀ hγ₀ v
  · exact hg

end GlobalTheory.St

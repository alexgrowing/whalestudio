import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComponentLatticeMarkingAdelicStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFiniteAdelicElementMarkingComponentStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroupStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryFramesOrthonormalUnitStatement
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem GlobalTheory.Member.Ctx.exists_isDict : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∃ dict, C.IsDict dict := by
  intro D H Dw l Xo c σ V r C hC
  classical
  choose k₀ γ₀ h₀ using GlobalTheory.T.exists_component_lattice_marking_adelic D H Dw l Xo c σ V r C hC
  refine ⟨fun h => if hk : ∃ k, C.Mark h k 1 then ⟨hk.choose, C.fr h hk.choose⟩
    else ⟨k₀ h, C.fr (γ₀ h * h) (k₀ h)⟩, ?_, ?_⟩
  · intro h
    by_cases hk : ∃ k, C.Mark h k 1
    · refine ⟨1, ?_⟩
      beta_reduce
      rw [dif_pos hk]
      exact ⟨hk.choose_spec, by rw [one_mul]⟩
    · refine ⟨γ₀ h, ?_⟩
      beta_reduce
      rw [dif_neg hk]
      exact ⟨h₀ h, rfl⟩
  · intro k
    obtain ⟨h, hf, hm⟩ := GlobalTheory.T.exists_finiteAdelic_element_marking_component D H Dw l Xo c σ V r C hC k
    have hk : ∃ k, C.Mark h k 1 := ⟨k, hm⟩
    refine ⟨h, ?_⟩
    beta_reduce
    rw [dif_pos hk]
    have e : hk.choose = k :=
      (GlobalTheory.T.marking_component_unique_frame_unique_arithmeticGroup D H Dw l Xo c σ V r C hC h).1 _ _ _ _ hk.choose_spec hm
    rw [e]
    have := (GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC 1 k).2.2.2.2.1 h hf
    rw [one_mul] at this
    rw [this]

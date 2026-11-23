import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FinJacAsm
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocMassTyp
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocJacOrd
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocJacTyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PhiBijective
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.TwoPrimes
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLocJacHypLemmas

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.Pf.MassDataX

variable {D : D7} (X : HidaSetting D)

theorem sig_ne_id : X.B.I.cm.sig ≠ AlgHom.id X.B.I.F X.B.I.E := by
  intro h
  have hall : ∀ a : X.B.I.E, a ∈ (⊥ : Subalgebra X.B.I.F X.B.I.E) := by
    intro a
    have h1 : X.B.I.cm.sig a = a := by rw [h]; rfl
    obtain ⟨c, hc⟩ := (X.B.I.cm.fixed a).1 h1
    exact Algebra.mem_bot.2 ⟨c, hc⟩
  have htop : (⊥ : Subalgebra X.B.I.F X.B.I.E) = ⊤ := eq_top_iff.2 fun a _ => hall a
  have h1 : Module.finrank X.B.I.F X.B.I.E = 1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 htop
  have h2 := X.B.I.cm.deg2
  omega

theorem idem_typed (v : PlX X) (hv : TypAt X v) :
    ∃ x : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1 := by
  obtain ⟨θ, -⟩ := MassDataIdxSteps.splitTheta_of X ⟨v, hv⟩ (MassDataIdxSteps.embP_holds X ⟨v, hv⟩)
  refine ⟨θ.symm (1, 0), ?_, ?_, ?_⟩
  · rw [← map_mul]
    congr 1
    ext <;> simp
  · intro h0
    have := congrArg θ h0
    rw [AlgEquiv.apply_symm_apply, map_zero] at this
    exact one_ne_zero (congrArg Prod.fst this)
  · intro h1
    have := congrArg θ h1
    rw [AlgEquiv.apply_symm_apply, map_one] at this
    exact zero_ne_one (congrArg Prod.snd this)

theorem jacLocAt_holds (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (v : PlX X) :
    JacLocAt X u u' ψ v := by
  intro hdiv
  by_cases h : TypAt X v
  · simp only [ZZX, jacX, localVolumeUnit, PPX, if_pos h]
    exact locJacTyp X.B.I.cm.sig ψ v _ _ _ _ _ _ _ X.B.I.cm.deg2 (sig_ne_id X) h (gAt_prime X v).pos
      (idem_typed X v h) (LJP.herm X u v) (LJP.herm X u' v) (LJP.integral X u u' v h (hdiv h)) (hdiv h)
  · simp only [ZZX, jacX, localVolumeUnit, PPX, if_neg h]
    exact locJacOrd ψ v _ _ _ X.B.I.cm.deg2 h

theorem finJac_holds (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : FinJac X u u' ψ :=
  Formalism.L2.SG.Pf.finJac_of X u u' ψ (jacLocAt_holds X u u' ψ)

theorem typLocX_holds (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) :
    TypLocX X u u' ψ := fun p => locMassTyp _ _ _ _ _ _ _ _

end Formalism.L2.SG.Pf.MassDataX

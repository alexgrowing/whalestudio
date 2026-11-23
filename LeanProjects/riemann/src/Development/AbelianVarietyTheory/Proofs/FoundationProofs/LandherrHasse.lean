import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedOfIsCMUnram

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.DefiniteOrthonormal

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem exists_orthonormal (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W : Formalism.BasicNotions.HSpace E) (hs : W.SigOK)
    (hp : ∀ τ : E →+* ℂ, W.sig τ = (W.rank, 0)) :
    ∃ b : Fin W.rank → W.V, LinearIndependent E b ∧
      ∀ a c, W.hT (b a) (b c) = if a = c then 1 else 0 := by
  obtain ⟨e, he⟩ := GlobalTheory.DefiniteMass.exists_isometry hc W hs hp
  refine ⟨(Pi.basisFun E (Fin W.rank)).map e.symm, Module.Basis.linearIndependent _, fun a c => ?_⟩
  rw [← he]
  simp only [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
  change ∑ i, star ((Pi.single a (1 : E) : Fin W.rank → E) i) * (Pi.single c (1 : E) : Fin W.rank → E) i = _
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_apply]
  · intro i _ hi
    simp [Pi.single_apply, hi]
  · simp

end

theorem landherrHasse : ∀ D : D7, LandherrHasse D := fun D =>
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  fun W hs hp => exists_orthonormal (E := D.host.E) D.sp.cm.cmUnram W hs hp

end GlobalTheory.DefiniteOrthonormal

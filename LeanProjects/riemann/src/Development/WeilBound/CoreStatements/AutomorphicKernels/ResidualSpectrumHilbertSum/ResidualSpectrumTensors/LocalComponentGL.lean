import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericCommutationOfReorder

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.RSHS.LocalComponentGL

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem isDiscrete_of_cusp {a : ℕ} {π : CuspSub E a} (hu : π.IsUnitary) (hn : IsNormalised π) : IsDiscrete π.V := by
  refine ⟨fun φ hφ => (π.cusp φ hφ).1, fun φ hφ => ?_, π.stable, π.ne_bot, π.irred⟩
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL.of_isUnitary hu hφ
  exact GlobalTheory.DiscChar.isSqInt_of_bounded (hn φ hφ) hC

theorem locCompGL_of_locComp {a : ℕ} {π : CuspSub E a} {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) : IsLocCompGL π.V w σ := by
  obtain ⟨f, h0, h1⟩ := hσ
  exact ⟨π.V.subtype.comp f, fun e => h0 (LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun e v)),
    fun v => (f v).2, fun g v => congrArg Subtype.val (h1 g v)⟩

theorem generic_unitarisable {a : ℕ} {π : CuspSub E a} (hu : π.IsUnitary) (hn : IsNormalised π)
    {w : HeightOneSpectrum (𝓞 E)} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) :
    GlobalTheory.LocGL.IsGeneric (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred).rep ∧
      GlobalTheory.SmGL.IsUnitarisable (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred).rep := by
  let e := GlobalTheory.LocGL.IrrGL.equivOf σ.ρ σ.smooth σ.irred
  have hg : GlobalTheory.LocGL.IsGeneric σ.ρ := GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E a π w σ hσ
  have hv : GlobalTheory.SmGL.IsUnitarisable σ.ρ :=
    GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL E a π.V (isDiscrete_of_cusp hu hn) w σ
      (locCompGL_of_locComp hσ)
  exact ⟨GlobalTheory.CompanionTheory.BZSeg.isGeneric_of_surjective e.symm.toIntertwiningMap e.symm.toLinearEquiv.surjective hg,
    GlobalTheory.GenericUnitary.isUnitarisable_of_equiv e hv⟩

end PositivityTheory.RSHS.LocalComponentGL

end

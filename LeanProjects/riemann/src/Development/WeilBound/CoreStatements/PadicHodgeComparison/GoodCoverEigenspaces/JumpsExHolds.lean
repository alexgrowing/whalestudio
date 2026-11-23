import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.JumpStepOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual GlobalTheory.Pst

namespace PositivityTheory.AutomorphicGaloisHodgeTate.G8

theorem jumpsEx_holds : JumpsEx := by
  intro E Ω _ _ _ _ _ l _ P AI hT Gw O _ _ _ Bw d r hc τ LL' τ' hτ
  obtain ⟨T⟩ := hT
  obtain ⟨L, r₁, hm, hcr⟩ := hc
  have := L.2
  have hd : Bw.IsdRE P L r₁ := by
    have h2 : Module.finrank ↥L.1 ↥(DdR (P.PD Bw.Kw) (Bw.repE L r₁)) =
        Module.finrank ℚ_[l] ↥Bw.Kw.1 * Module.finrank ↥L.1 (Fin d → ↥L.1) :=
      (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T Bw.Kw L (Fin d → ↥L.1) (Bw.repE L r₁) hcr).1
    rw [LocBridge.IsdRE, h2, Module.finrank_fin_fun]
  let τL : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1 := (IntermediateField.inclusion hm.1).comp
    ((LL'.1.val.comp τ').codRestrict Bw.LL.1.toSubalgebra fun x => Bw.LL_split _ x)
  have hτL : GlobalTheory.Pst.IsInduced Bw τ τL := fun x => hτ x
  exact GlobalTheory.Pst.IsModel.exists_isJumpsAt P hm hd hτL

end PositivityTheory.AutomorphicGaloisHodgeTate.G8

end

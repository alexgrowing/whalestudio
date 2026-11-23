import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.So.dcAt :
    UpperTheory.V.Z.Sym.So.DcAt := by
  intro L _ _ _ n U₀ S VL hP w hw hF d
  obtain ⟨hsec, hcomm, -, -, -, -, hcomp, hK⟩ := UpperTheory.V.Z.Sym.Dict.Br.uaFacts L n
  have hsp : IsSplitAt w := hP.split w hw
  obtain ⟨hloc, hcl, -, hsecx⟩ := hsec w hsp
  obtain ⟨-, -, -, -, -, hfin⟩ := UpperTheory.V.Z.Sym.Sig.finFacts (Kw w) (VL w)
  obtain ⟨hH, -, -, hJK⟩ := hfin n
  have hKO : GlobalTheory.SplitWeil.KO (Kw w) (Fin n) = GlobalTheory.LFun.KGL w n := GlobalTheory.SmGL.SphCompletion.KO_completion w n
  have hoff : ∀ (h : GL (Fin n) (Kw w)) (u : Plc L), un u ≠ un w → cLoc u (secW n w h) = 1 := fun h u e =>
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (hloc h).2 u) e
  have h2 : ∀ u ∈ lev U₀ S VL, cLoc w u ∈ (VL w).J n ∧ ∀ h, u * (secW n w (cLoc w u))⁻¹ * secW n w h =
      secW n w h * (u * (secW n w (cLoc w u))⁻¹) := fun u hu => by
    refine ⟨Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hu.2 w) hw, fun h => ?_⟩
    obtain ⟨a, ha, hau⟩ := hcomp w u (hF.1 hu.1).1
    have ea : secW n w (cLoc w u) = a := by rw [← hau w rfl, ← hsecx a ha]
    have hy : ∀ u', un u' = un w → cLoc u' (u * (secW n w (cLoc w u))⁻¹) = 1 := fun u' e => by
      rw [map_mul, map_inv, ea, hau u' e, mul_inv_cancel]
    exact (hcomm w _ (hloc h) _ hy).symm.eq
  have h3 : ∀ h ∈ (VL w).J n, secW n w h ∈ lev U₀ S VL := fun h hh => by
    refine ⟨hF.2 w (Finset.mem_singleton_self w) ⟨hloc h, ⟨(hloc h).1, Subgroup.mem_iInf.2 fun u => ?_⟩⟩, ?_⟩
    · by_cases e : un u = un w
      · refine hK w hsp _ ?_ u e
        rw [hcl, ← hKO]
        exact hJK hh
      · rw [Subgroup.mem_comap, hoff h u e]
        exact one_mem _
    · refine Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun hw' => ?_
      by_cases e : w' = w
      · subst e
        rw [Subgroup.mem_comap, hcl]
        exact hh
      · rw [Subgroup.mem_comap, hoff h w' fun e' => e (hP.inj hw' hw e')]
        exact one_mem _
  have main := fun (V : Type) [AddCommGroup V] [Module ℂ V] =>
    UpperTheory.V.Z.Sym.So.dcLocal _ _ V (secW n w) (cLoc w) ((VL w).J n) (lev U₀ S VL) hcl h2 h3 (Sig.dg d) (hH _)
  refine ⟨(main ℂ).1, fun V _ _ φ hφ c => ?_⟩
  unfold EigAt
  rw [(main V).2 φ hφ]

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateDividesOnNonzeroLocusSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedThetaSectionNonzeroEveryFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianExtensionAbelianLocusNonemptyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyZh

theorem lft_of_arithBase : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (M : ZH.RatModel o Ω), LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
  intro o Ω _ _ _ _ M
  have := M.lft
  have hft : Algebra.FiniteType ℤ o := (inferInstance : ZH.ArithBase o Ω).ft
  have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 hft
  infer_instance

theorem charZero_of_arithBase : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (M : ZH.RatModel o Ω), CharZero Γ(M.Z, ⊤) := by
  intro o Ω _ _ _ _ M
  have hne : ((⊤ : M.Z.Opens) : Set M.Z).Nonempty := ⟨genericPoint M.Z, trivial⟩
  have := (inferInstance : ZH.ArithBase o Ω).char
  exact (M.res ⊤ hne).charZero

theorem unifAlong_of_zhOut : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), UnifAlong Zh.G Zh.L.L := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Zh V _ _ _ _ hc _ ξ hne _
  obtain ⟨D, A, U, hU, -⟩ := Zh.unif V inferInstance inferInstance hc ξ hne
  exact ⟨D, A, U, hU⟩

theorem key_zh : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), 1 ≤ S.g → S.Over₀ M U₀ → IsOpen (abLocus Zh.G) → ∀ (δ : LB M.Z) (t : S.Gam → δ.Sec), δ.IsLB → (⨆ a, nonzeroLocus (t a)) = ⊤ → ZM.SecCoord δ t M.pt S.th → LBIso (lbPow δ 8) (lbPow (GlobalTheory.SiegelTor.hodge Zh.G S.g) 4) := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Zh hg hO hab δ t hδ hcov hsc
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_glued_thetaSection_nonzero_every_fibre o Ω S ρ M U₀ EE Zh hO δ t hδ hcov hsc
    (fun a z hz => GlobalTheory.T.coordinate_divides_on_nonzeroLocus_section o Ω M δ t S.th hδ hsc a z hz)
  exact GlobalTheory.T.keyFormula_evenDegeneration_global M.Z (M.s ≫ spMap (algebraMap ℤ o)) Zh.G S.g Zh.L δ σ hg inferInstance hO.normal
    (lft_of_arithBase o Ω M) (charZero_of_arithBase o Ω M) Zh.semi Zh.dim (GlobalTheory.T.semiAbelianExtension_abelianLocus_nonempty o Ω S ρ M U₀ EE Zh hO) hab
    Zh.sym hδ Zh.pol (unifAlong_of_zhOut o Ω S ρ M U₀ EE Zh) hσ

end GlobalTheory.KeyZh

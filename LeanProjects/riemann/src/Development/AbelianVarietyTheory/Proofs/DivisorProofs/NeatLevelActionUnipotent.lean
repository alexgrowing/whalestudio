import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismIntegralMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibreInjectsLevelModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreActionTrivialOfFixedPointResidueFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvAct

theorem eqvLin_pull : Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → FnAlgClosed Xo c → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ, UnipAt I (ι γ)) → ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom) → ∃ (G' : Over X') (_ : GrpObj G') (ψ : G'.left ⟶ TF.Y.t.G.left) (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)), GlobalTheory.HodgeLin.EqvLin TF.Y.t (φ ≫ (barComp TF.Y Z).ι) ρ' G' ψ act' m := by
  intro hP E _ _ _ H Dw l Xo c TF Z hpq hA hF I g hI hMb Γ _ _ ι ρ hU hAct X' _ φ ℓ ρ' hN hPr hO hj heq
  obtain ⟨m, hm, hmv⟩ := GlobalTheory.T.level_automorphism_integral_map hP E H Dw l Xo c TF Z hpq hA Γ ι ρ hAct X' φ ℓ ρ' hN hPr hO hj heq
  have hT := GlobalTheory.T.torsion_fibre_injects_levelModule E H Dw l Xo c TF Z hpq hA I g hI hMb Γ ι ρ hAct X' φ ℓ ρ' hN hPr hO hj heq m hm hmv
  exact ⟨pullG TF Z φ, inferInstance, pullψ TF Z φ, pullAct TF Z φ, m,
    isGrpPullback_pullψ TF Z φ, pullAct_pullψ TF Z φ, hm.1, hm.2.1, hm.2.2,
    GlobalTheory.T.fibre_action_trivial_of_fixed_point_residue_field E H Dw l Xo c TF Z hpq hA I g hI hMb Γ ι hU X' φ ρ' hN hPr m hm hT⟩

end GlobalTheory.EqvAct

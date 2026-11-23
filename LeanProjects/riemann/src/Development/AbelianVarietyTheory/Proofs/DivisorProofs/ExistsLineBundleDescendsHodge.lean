import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfHodgeWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDetLieEigenpartsToroidalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactificationComponentIntegralSmoothProjectiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDeterminantLinearisationEquivariantPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeatLevelActionUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestMore
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

namespace GlobalTheory.HodgeLin

theorem hodgeLine_ratLin : Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → FnAlgClosed Xo c → ∃ (δ : LB (X₀ TF.Y Z)) (hδ : δ.IsLB), CechPic.pull (π₀ TF.X Z) (cls δ hδ) = cls (L₀ TF.X Z (hodgeWt Dw)) (isLB_L₀ TF.X Z _) ∧ ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ, UnipAt I (ι γ)) → ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom) → RatLin ρ' (δ.pull φ) (LB.isLB_pull hδ φ) := by
  intro hP E _ _ _ H Dw l Xo c TF Z hpq hA hF
  obtain ⟨hI, -⟩ := GlobalTheory.BaseVar.isVariety_barComp E H Dw l Xo c TF Z hF
  obtain ⟨φ₀, f₀, hφ₀, hD⟩ := GlobalTheory.T.exists_cartierDivisor_det_lieEigenparts_toroidal E H Dw l Xo c TF Z
  obtain ⟨D, hDp, hDe⟩ := hD (GlobalTheory.HodgeLin.offCM H)
  refine ⟨toLB D, isLB_toLB D, ?_, ?_⟩
  · rw [hDp]
    have key : ∀ (L L' : LB (Y₀ TF.X Z)) (hL : L.IsLB) (hL' : L'.IsLB), L = L' → cls L hL = cls L' hL' := by
      rintro _ _ _ _ rfl; rfl
    exact key _ _ _ _ (congrArg (LL₀ TF.X Z) (GlobalTheory.HodgeLin.exOf_hodgeWt Dw)).symm
  · intro I g hI' hMb Γ _ _ ι ρ hU hAct X' _ φ ℓ ρ' hN hP' hO hj heq
    obtain ⟨G', _, ψ, act', m, hE⟩ := GlobalTheory.T.neat_level_action_unipotent hP E H Dw l Xo c TF Z hpq hA hF I g hI' hMb Γ ι ρ hU hAct X' φ ℓ ρ' hN hP' hO hj heq
    obtain ⟨v, hv⟩ := GlobalTheory.GenInterior.exists_j₀_eq_genericPoint E H Dw l Xo c TF Z
    have hd : IsDominant φ := ⟨by
      refine dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)
      rw [← (genericPoint_spec (X₀ TF.Y Z)).def]
      exact closure_mono (Set.singleton_subset_iff.2 ⟨ℓ v, by rw [← Scheme.Hom.comp_apply, hj, hv]⟩)⟩
    haveI : Nonempty (V₀ TF.Y Z) := ⟨v⟩
    haveI : IsDominant ℓ := ⟨ℓ.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
    have hρ : ∀ γ, (ρ' γ).hom ≫ φ ≫ s₀ TF.Y Z = φ ≫ s₀ TF.Y Z := fun γ => by
      refine ext_of_isDominant ℓ ?_
      rw [← Category.assoc, ← heq, Category.assoc, ← Category.assoc ℓ φ, hj]
      exact hAct.1 γ
    exact GlobalTheory.T.lieDeterminant_linearisation_equivariant_pullback E H Dw l Xo c TF Z φ₀ f₀ (GlobalTheory.HodgeLin.offCM H) D hφ₀ hDe Γ X' φ ρ' hd hρ G' ψ act' m hE

end GlobalTheory.HodgeLin

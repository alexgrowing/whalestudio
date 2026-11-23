import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationCompleteLocalEvenOnTorusStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinExtCubicalSymmetricEvenFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianUniformizationLinearActionDescentStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorTrait

theorem exists_trait_of_unif (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀] (hR : Base R₀)
    (D₀ : DegData R₀ (maximalIdeal R₀)) (A₀ : PolAV (Sp (FractionRing R₀))) (G₀ : Over (Sp R₀)) [GrpObj G₀]
    [IsCommMonObj G₀] (hG : IsSemiAbelian G₀) (U₀ : Unif (maximalIdeal R₀) D₀ A₀ G₀) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₀ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW)
      (_ : IsCommMonObj GW) (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W)))
      (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧
      IsGrpPullback GW G₀ (spMap φ) β ∧ LBIso UW.LG.L (U₀.LG.L.pull β) ∧ Nonempty (IsPullDeg φ D₀.toPre DW.toPre) := by
  have := hR.2
  have := hR.1.1
  obtain ⟨W, _, _, _, φ, hW, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R₀ (maximalIdeal R₀)
  haveI hloc : IsLocalHom φ := ((IsLocalRing.local_hom_TFAE φ).out 0 4).mpr hc
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨DW, hD, AW, UW, hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hR.1 hW' φ hφ (map_maximalIdeal_le φ) hG U₀
  have hb : (Iso.refl ((Over.pullback (specOf φ)).obj G₀)).hom.left ≫ pullback.fst G₀.hom (specOf φ) =
      pullback.fst G₀.hom (specOf φ) := Category.id_comp _
  refine ⟨W, _, inferInstance, inferInstance, φ, (Over.pullback (specOf φ)).obj G₀, inferInstance, inferInstance,
    (Iso.refl ((Over.pullback (specOf φ)).obj G₀)).hom.left ≫ pullback.fst G₀.hom (specOf φ), DW, AW, UW, hW, hφ, hloc,
    ?_, ⟨hP.lg.choose, hP.lg.choose_spec.1⟩, ⟨hD⟩⟩
  exact (isGrpPullback_pullback G₀ (spMap φ)).congr rfl hb.symm

theorem factor_unif_at_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (D₀ : DegData R₀ (maximalIdeal R₀)) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₀ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), FinExt ρ₀ ∧ Nonempty (IsPullDeg ρ₀ D.toPre D₀.toPre) ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₀ (spMap φ) β ∧ LBIso UW.LG.L (P.L.L.pull β) ∧ Nonempty (IsPullDeg φ D₀.toPre DW.toPre) ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) := by
  intro R _ _ _ hR D D' F hA A' G' _ _ hG' U' oA oG hO G _ _ hG inc pr hinc hpr h1 h2
  obtain ⟨R₉, _, _, _, ρ₉, G₉, _, _, β₉, β₉₂, P₉, A₉, gen₉, a1, a2, a3, a4, a5, a6, a7, a8⟩ :=
    GlobalTheory.T.exists_finExt_cubicalSymmetric_even_factor R hR D D' F hA A' G' hG' U' oA oG hO G hG inc pr hinc hpr h1 h2
  obtain ⟨R₀, _, _, _, ρ₀, D₀, G₀, _, _, β₀, β₀₂, P, A₀, gen₀, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ :=
    GlobalTheory.T.semiabelian_uniformization_linear_action_descent R hR D D' F A' G' hG' U' oA oG hO G hG inc pr hinc hpr h1 h2 R₉ ρ₉ G₉ β₉ β₉₂ P₉ A₉ gen₉ a1 a2 a3 a4 a5 a6 a7 a8
  haveI := hR.2
  have hR₀ : Base R₀ := ⟨c1.1, charZero_of_injective_ringHom c1.2.1⟩
  obtain ⟨D'', U'', hLG, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocal_evenOnTorus R₀ hR₀ G₀ P c5 c7 A₀ gen₀ c8 c9
  obtain ⟨W, _, _, _, φ, GW, _, _, β, DW, AW, UW, w1, w2, w3, w4, w5, -⟩ := exists_trait_of_unif R₀ hR₀ D'' A₀ G₀ c5 U''
  rw [hLG] at w5
  exact ⟨R₀, _, _, _, ρ₀, D₀, G₀, _, _, β₀, β₀₂, P, W, _, _, _, φ, GW, _, _, β, DW, AW, UW, c1, c2, c3, c4, c5, w1, w2, w3,
    w4, w5, c10 W w1 φ w2 w3 GW β DW AW UW w4 w5, c6⟩

end GlobalTheory.Mum.FactorTrait

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfIndepCombStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumSectionsPullbacksValueAbelianPartStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationUniformisedHomConvolutionExpansiAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedSectionJoinBundlesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedBundleFrameFromPartFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSectionValueProductExpansionTermsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationKillsMixedSectionSumsLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange
open GlobalTheory.Mum.Two.Mix

noncomputable section
namespace GlobalTheory.Mum.Two.Mix

theorem core : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁ U₂ a b h → Coord U₁ U₂ a b h → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (j j' : ℕ) (N : Type) [Fintype N] (ρ : N → R) (σ : N → H0 U₂.LG.L j) (σ' : N → H0 U₁.LG.L j') (f : N → ∀ α : D₂.toPre.X, D₂.toPre.SecB j α) (f' : N → ∀ α : D₁.toPre.X, D₁.toPre.SecB j' α), (∀ ν e, U₂.ExpandsAt e j (σ ν) (f ν)) → (∀ ν e, U₁.ExpandsAt e j' (σ' ν) (f' ν)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ G₁.left) (z : Z) (J₁ J₂), Good U₁.LG.L z J₁ → Good U₂.LG.L z J₂ → ∑ ν, constVal (r ≫ G₁.hom) z (ρ ν) * (sval (σ ν) (r ≫ a.left) z J₂ * sval (σ' ν) r z J₁) = 0) → ∀ (g : GtPtF D₁.toPre F) (g' : GtPtF D₂.toPre F), Act D₁.toPre D₂.toPre b h g g' → ∀ (w : Frm D₂.toPre F j g'.b) (w' : Frm D₁.toPre F j' g.b), w.IsGen → w'.IsGen → ∀ (x : N → D₂.toPre.X → F) (x' : N → D₁.toPre.X → F), (∀ ν χ, MixedConv.IsCoefB j g' w χ (f ν χ) (x ν χ)) → (∀ ν χ, MixedConv.IsCoefB j' g w' χ (f' ν χ) (x' ν χ)) → ∀ α : D₁.toPre.X, SumF I F (fun p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} => ∑ ν, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (ρ ν)) * (x ν p.1.1 * x' ν p.1.2)) 0 := by
  intro hL R _ _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a b h hLin hCo F _ _ _ j j' N _ ρ σ σ' f f' hE hE' hrel
    g g' hg w w' hw hw' x x' hx hx' α
  choose u hu using hCo
  choose n hn using fun (ν : N) (α : D₁.toPre.X) (p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α}) =>
    GlobalTheory.T.exists_mixed_section_join_bundles R D₁.toPre D₂.toPre b j j' p.1.1 (h p.1.1) p.1.2 α p.2 (u p.1.1) (hu p.1.1).1.1 (f ν p.1.1) (f' ν p.1.2)
  let m : ∀ α, {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} →
      SecOver D₁.toPre.P.A.hom (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j')) :=
    fun α p => ∑ ν, ρ ν • (show SecOver D₁.toPre.P.A.hom _ from n ν α p)
  have hm : ∀ α p (Z : Scheme.{0}) (r : Z ⟶ D₁.toPre.P.A.left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J →
      sval (m α p) r z J = ∑ ν, constVal (r ≫ D₁.toPre.P.A.hom) z (ρ ν) *
        (sval (f ν p.1.1) (r ≫ b.left) z (rr J) * sval (f' ν p.1.2) r z (rl J) *
          (val (u p.1.1) r z J * val (MixedConv.cubB D₁.toPre (h p.1.1) p.1.2) r z (rl J)).val) :=
    fun α p Z r z J hJ =>
      (sval_sum' (π := D₁.toPre.P.A.hom) hJ _ _ _).trans (Finset.sum_congr rfl fun ν _ =>
        (sval_smul' (π := D₁.toPre.P.A.hom) hJ _ _ _).trans (congrArg _ (hn ν α p Z r z J hJ)))
  obtain ⟨τ, hτ, hv⟩ := GlobalTheory.T.exists_mixed_bundle_frame_from_part_frames R D₁.toPre D₂.toPre F b α j j' g _ hg.1 w w' hw hw'
  refine GlobalTheory.T.adicSum_sections_pullbacks_value_abelianPart R I hR D₁ F _ (JN D₁.toPre D₂.toPre) (jn_isLB D₁.toPre D₂.toPre) _ (mixφ D₁.toPre D₂.toPre b α)
    (MixedConv.mixε j j') _ (m α) (0 : SecOver D₁.toPre.P.A.hom _) (fun e => ?_) g.b τ hτ _ 0 fun z J hJ => ⟨fun p => ?_, ?_⟩
  · obtain ⟨S, hS⟩ := GlobalTheory.T.integral_relation_kills_mixed_section_sums_level R I D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a b h hLin.2.2.1 u (fun χ => (hu χ).2) j j' e N ρ σ σ' f f' (fun ν => hE ν e)
      (fun ν => hE' ν e) hrel m hm α
    exact ⟨S, fun Z r z J hJ => ⟨(hS Z r z J hJ).1,
      (sval_zero' (π := D₁.toPre.P.A.hom) hJ _).trans (hS Z r z J hJ).2.symm⟩⟩
  · obtain ⟨⟨χ, δ⟩, hp⟩ := p
    rw [hm _ _ _ _ z J hJ, CoefBasic.cst_eq, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have c₁ : constVal (g.b.left ≫ D₁.toPre.P.A.hom) z (ρ ν) =
        CoefBasic.cstH z (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (ρ ν))) := by
      refine Eq.trans ?_ (CoefBasic.cst_eq z _)
      rw [Over.w g.b]
      refine (constVal_specMap (jFK (R := R) F) _ z _).trans ?_
      exact (congrArg (fun q => constVal q z _) (Category.id_comp _).symm).trans (constVal_specMap (𝟙 _) _ z _)
    have e₁ := GlobalTheory.T.mixed_section_value_product_expansion_terms R D₁.toPre D₂.toPre F b h g g' hg j j' w w' χ δ (u χ) (hu χ).1 (f ν χ) (f' ν δ) _ _ (hx ν χ) (hx' ν δ) z J hJ
    have e₂ := hv z J hJ
    dsimp only at hp
    subst hp
    rw [c₁, e₁, e₂, CoefBasic.cst_eq]
    simp only [map_mul]
    ring
  · rw [CoefBasic.cst_eq, map_zero, zero_mul]
    exact sval_zero' (π := D₁.toPre.P.A.hom) hJ _

end GlobalTheory.Mum.Two.Mix

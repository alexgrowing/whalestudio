import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrameChart

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

variable {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
  {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ}

theorem pulled_back_lineBundle_transition_unit_eq_restriction {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (j j' : PUnit.{1} → L.ι) :
    (L.pull f).g j j' = res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ => f) j PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ => f) j' PUnit.unit)))
      (pullU f _ (L.g (j PUnit.unit) (j' PUnit.unit))) := by
  have e : ∀ u : Γ(Y, L.wchart (fun _ => f) j ⊓ L.wchart (fun _ => f) j')ˣ, (∏ _k : PUnit.{1}, u ^ (1 : ℤ)) = u :=
    fun u => by simp
  exact e _

theorem pull_g_eq (h : IsGrpPullback H G x ψ) (j j' : ((hodge G g).pull x).ι) :
    ((hodge G g).pull x).g j j' =
      (isFrame_chart h j).detUnit (isFrame_chart h j') inf_le_left inf_le_right := by
  have e₁ := IsFrame.detUnit_map_iso
    (GlobalTheory.BadPt.Fibre.frame_pb x (j PUnit.unit).isFrame (LB.wchart_le (hodge G g) (fun _ => x) j PUnit.unit))
    (GlobalTheory.BadPt.Fibre.frame_pb x (j' PUnit.unit).isFrame (LB.wchart_le (hodge G g) (fun _ => x) j' PUnit.unit))
    (omegaBase h) (inf_le_left : LB.wchart (hodge G g) (fun _ => x) j ⊓ LB.wchart (hodge G g) (fun _ => x) j' ≤ _)
    inf_le_right
  refine Eq.trans ?_ e₁.symm
  have hT : LB.wchart (hodge G g) (fun _ => x) j ⊓ LB.wchart (hodge G g) (fun _ => x) j' ≤
      x ⁻¹ᵁ ((j PUnit.unit).U ⊓ (j' PUnit.unit).U) :=
    le_inf (inf_le_left.trans (LB.wchart_le (hodge G g) (fun _ => x) j PUnit.unit))
      (inf_le_right.trans (LB.wchart_le (hodge G g) (fun _ => x) j' PUnit.unit))
  refine Eq.trans ?_ (GlobalTheory.Vert.DivPull.detUnit_congr _ _ ((j PUnit.unit).isFrame.pullback x)
    ((j' PUnit.unit).isFrame.pullback x) _ _ (hT.trans (x.preimage_mono inf_le_left))
    (hT.trans (x.preimage_mono inf_le_right))
    (fun i => (QCoh.res_pullbackSections _ _ _ _ _).trans (QCoh.res_pullbackSections _ _ _ _ _).symm)
    (fun i => (QCoh.res_pullbackSections _ _ _ _ _).trans (QCoh.res_pullbackSections _ _ _ _ _).symm)).symm
  refine Units.ext ?_
  refine (congrArg Units.val (pulled_back_lineBundle_transition_unit_eq_restriction (hodge G g) x j j')).trans (Eq.trans ?_
    (IsFrame.val_detUnit_pullback (j PUnit.unit).isFrame (j' PUnit.unit).isFrame x inf_le_left inf_le_right hT).symm)
  rfl

theorem gen_isGen : ∀ {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a), (gen h ha).IsGen := by
  intro S' T G _ H _ x ψ _ g h a ha j j'
  refine (IsFrame.res_detUnit _ _ _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (pull_g_eq h j j').symm (IsFrame.res_detUnit _ _ _ _ _).symm)
  exact (IsFrame.detUnit_mul _ _ _ _ _ _).symm

end GlobalTheory.HodgeFrameGen

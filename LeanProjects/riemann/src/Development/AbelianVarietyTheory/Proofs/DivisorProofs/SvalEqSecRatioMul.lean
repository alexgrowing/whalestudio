import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTermsStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatSurjectiveKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitSvalIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TermWeight

theorem sval_eq_secRatio_mul {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (a b : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) (hz : r z ∈ nonzeroLocus a) :
    sval b r z J = gs r z (nonzeroLocus a) (GlobalTheory.ProjSpace.secRatio a b) * sval a r z J := by
  have hm : r z ∈ nonzeroLocus a ⊓ LB.wchart L φ (fun k => J (r ≫ φ k)) := ⟨hz, hJ.mem φ r⟩
  have e := congrArg (gs r z _) (GlobalTheory.ProjSpace.secRatio_on a b (fun k => J (r ≫ φ k))
    (W := nonzeroLocus a ⊓ LB.wchart L φ (fun k => J (r ≫ φ k))) inf_le_left inf_le_right)
  exact (gs_res r z inf_le_right hm _).symm.trans (e.trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_res r z inf_le_left hm _) (gs_res r z inf_le_right hm _))))

theorem isWt_secRatio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (i : splitTorus (Sp R) D.X ⟶ Y.H), (∀ (χ : D.X) (Z : Over (Sp R)) (t : Z ⟶ splitTorus (Sp R) D.X) (g : Z ⟶ Y.H) (z : Z.left) J, Good D.P.L z J → val ((Y.Φ Z ((t ≫ i) * g)).s χ) (𝟙 _) z J = gm t.left z ⊤ (charUnit (Sp R) D.X χ) * val ((Y.Φ Z g).s χ) (𝟙 _) z J) → IsPullback i (toUnit _) Y.q η[D.P.A] → ∀ (k : ℕ) (α : D.X) (b₀ : D.SecB k 0) (b : D.SecB k α) (τ₀ τ : SecK D.P.L Y.q.left k), IsTermOf Y b₀ τ₀ → IsTermOf Y b τ → GlobalTheory.UU.IsWt i (nonzeroLocus τ₀) (GlobalTheory.ProjSpace.secRatio τ₀ τ) α := by
  intro R _ _ D Y i hi hk k α b₀ b τ₀ τ h₀ h
  have := Y.isMonHom_q
  refine GlobalTheory.GtCoordCompare.isWt_of_gs fun Z t g hg z => ?_
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z
  have hq : (((t ≫ i) * g) ≫ Y.q).left = (g ≫ Y.q).left := GlobalTheory.GtCoordCompare.act_comp hk.w t g
  have z₁ : val ((Y.Φ Z ((t ≫ i) * g)).s 0) (𝟙 _) z J = 1 := GlobalTheory.TorusModel.cv_zero _ hJ
  have z₂ : val ((Y.Φ Z g).s 0) (𝟙 _) z J = 1 := GlobalTheory.TorusModel.cv_zero _ hJ
  have e₀ : sval τ₀ ((t ≫ i) * g).left z J = sval τ₀ g.left z J := by
    rw [h₀ Z _ z J hJ, h₀ Z g z J hJ, hq, z₁, z₂]
  have e : sval τ ((t ≫ i) * g).left z J =
      (gm t.left z ⊤ (charUnit (Sp R) D.X α)).val * sval τ g.left z J := by
    rw [h Z _ z J hJ, h Z g z J hJ, hq, hi α Z t g z J hJ, Units.val_mul, mul_left_comm]
  have hz : g.left z ∈ nonzeroLocus τ₀ := hg (Set.mem_univ z)
  have hu : IsUnit (sval τ₀ g.left z J) := (TermLocus.isUnit_sval_iff τ₀ _ z hJ).2 hz
  have hz' : ((t ≫ i) * g).left z ∈ nonzeroLocus τ₀ := (TermLocus.isUnit_sval_iff τ₀ _ z hJ).1 (e₀ ▸ hu)
  refine hu.mul_right_cancel ?_
  rw [_root_.mul_assoc, ← sval_eq_secRatio_mul τ₀ τ g.left z hJ hz, ← e, sval_eq_secRatio_mul τ₀ τ _ z hJ hz', e₀]

end GlobalTheory.Mum.TermWeight

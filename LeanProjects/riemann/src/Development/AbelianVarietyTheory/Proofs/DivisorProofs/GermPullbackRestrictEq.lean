import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTermsStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatSurjectiveKernel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem germPullback_restrict_eq {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) {U V : X.Opens} (hle : V ≤ U) (h : f z ∈ V)
    (a : Γ(X, U)) : gs f z V (resG X hle a) = gs f z U a := gs_res f z hle h a

open GlobalTheory.ProjSpace in

theorem secRatio_isTermOf_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (k : ℕ) (b₀ b : D.SecB k 0) (τ₀ τ : SecK D.P.L Y.q.left k), IsTermOf Y b₀ τ₀ → IsTermOf Y b τ → ∀ (W : Y.H.left.Opens) (h₁ : W ≤ Y.q.left ⁻¹ᵁ nonzeroLocus b₀) (h₂ : W ≤ nonzeroLocus τ₀), (Y.q.left.appLE (nonzeroLocus b₀) W h₁).hom (GlobalTheory.ProjSpace.secRatio b₀ b) = resG Y.H.left h₂ (GlobalTheory.ProjSpace.secRatio τ₀ τ) := by
  intro R _ _ D Y k b₀ b τ₀ τ h₀ h W h₁ h₂
  apply fn_ext
  intro y hy
  rw [gs_appLE Y.q.left (nonzeroLocus b₀) W h₁ (𝟙 _) y hy, Category.id_comp,
    germPullback_restrict_eq (𝟙 Y.H.left) y h₂ hy]
  choose J hJ using fun ψ : Y.H.left ⟶ D.P.A.left => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart D.P.isLB (ψ y)
  have hG : Good D.P.L y J := hJ
  have e := h Y.H (𝟙 _) y J hG
  have e₀ := h₀ Y.H (𝟙 _) y J hG
  rw [Category.id_comp] at e e₀

  have hqy : Y.q.left y ∈ nonzeroLocus b₀ ⊓ LB.wchart D.P.L (D.famφB 0) (fun κ => J (Y.q.left ≫ D.famφB 0 κ)) :=
    ⟨h₁ hy, hG.mem (D.famφB 0) Y.q.left⟩
  have sb := congrArg (gs Y.q.left y _) (secRatio_on b₀ b (fun κ => J (Y.q.left ≫ D.famφB 0 κ))
    (W := nonzeroLocus b₀ ⊓ LB.wchart D.P.L (D.famφB 0) (fun κ => J (Y.q.left ≫ D.famφB 0 κ))) inf_le_left inf_le_right)
  rw [gs_mul _ y _ hqy] at sb
  erw [germPullback_restrict_eq _ y _ hqy, germPullback_restrict_eq _ y _ hqy, germPullback_restrict_eq _ y _ hqy] at sb

  have hyτ : (𝟙 Y.H.left) y ∈ nonzeroLocus τ₀ ⊓ LB.wchart D.P.L (fun _ : Fin 1 => Y.q.left) (fun _ : Fin 1 => J (𝟙 Y.H.left ≫ Y.q.left)) :=
    ⟨h₂ hy, hG.mem (fun _ : Fin 1 => Y.q.left) (𝟙 Y.H.left)⟩
  have sτ := congrArg (gs (𝟙 Y.H.left) y _) (secRatio_on τ₀ τ (fun _ : Fin 1 => J (𝟙 Y.H.left ≫ Y.q.left))
    (W := nonzeroLocus τ₀ ⊓ LB.wchart D.P.L (fun _ : Fin 1 => Y.q.left) (fun _ : Fin 1 => J (𝟙 Y.H.left ≫ Y.q.left))) inf_le_left inf_le_right)
  rw [gs_mul _ y _ hyτ] at sτ
  erw [germPullback_restrict_eq _ y _ hyτ, germPullback_restrict_eq _ y _ hyτ, germPullback_restrict_eq _ y _ hyτ] at sτ
  have hu : IsUnit (sval τ₀ (𝟙 Y.H.left) y J) :=
    (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs τ₀ (𝟙 Y.H.left) y hyτ.2).1 hyτ.1
  change sval τ (𝟙 Y.H.left) y J = _ * sval τ₀ (𝟙 Y.H.left) y J at sτ
  change sval b Y.q.left y J = _ * sval b₀ Y.q.left y J at sb
  change sval τ (𝟙 Y.H.left) y J = _ at e
  change sval τ₀ (𝟙 Y.H.left) y J = _ at e₀
  refine hu.mul_right_cancel ?_
  rw [← sτ, e, sb, e₀]
  exact (_root_.mul_assoc _ _ _).symm
end GlobalTheory.Mum

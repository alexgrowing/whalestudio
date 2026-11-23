import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.PullNonzero

theorem eq_zero_of_dominant {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {ψ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L ψ ε)) (h : Y' ⟶ Y) [IsSchemeTheoreticallyDominant h] [QuasiCompact h]
    (h0 : ∀ y J, Good L y J → sval s h y J = 0) (j : K → L.ι) : s.f j = 0 := by
  refine h.app_injective (LB.wchart L ψ j) (Eq.trans ?_ (map_zero (h.app (LB.wchart L ψ j)).hom).symm)
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
  have e₁ := gs_pull (𝟙 Y') h y (LB.wchart L ψ j) hy (s.f j)
  rw [Category.id_comp] at e₁
  have e₂ := sec_trans s h y (j := j) hy (Good.mem hI ψ h)
  have e₃ : gs h y _ _ = 0 := h0 y I hI
  rw [e₃, MulZeroClass.mul_zero] at e₂
  refine (e₁.trans e₂).trans ?_
  rw [gs_eq _ y _ hy, map_zero, map_zero]

theorem sval_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {ψ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L ψ ε)) (h0 : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval s r z J = 0 := by
  refine (congrArg (gs r z (LB.wchart L ψ (fun k => J (r ≫ ψ k)))) (h0 _)).trans ((gs_eq r z _ (hJ.mem ψ r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D' : DegPre V) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (C : GlobalTheory.LN.Cmp φ U U' F), GlobalTheory.LN.CDvr V → Function.Injective φ → ∀ (σ : U.SecGT (𝟙_ _) 1) (σ' : U'.SecGT (𝟙_ _) 1), (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ 1 * sval σ' r' z J') → (∃ j, σ.f j ≠ 0) → ∃ j, σ'.f j ≠ 0 := by
  intro R _ _ _ _ D A G _ _ U V _ _ _ φ D' A' G' _ _ U' F C _ hφ σ σ' H ⟨j, hj⟩
  by_contra h0
  push Not at h0
  have hs := U.semi.smooth
  have : Flat G.hom := inferInstance
  have : IsDominant (spMap φ) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2
      (by rw [(RingHom.injective_iff_ker_eq_bot φ).1 hφ]; exact bot_le)
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap φ)
  have : IsSchemeTheoreticallyDominant F := IsSchemeTheoreticallyDominant.of_isPullback C.pb.1.flip
  have : QuasiCompact F := MorphismProperty.of_isPullback (P := @QuasiCompact) C.pb.1.flip inferInstance
  have e : ∀ {S : Scheme.{0}} (B : Over S), (λ_ B).inv.left ≫ (snd _ B).left = 𝟙 _ := fun B =>
    congrArg (fun q => q.left) (leftUnitor_inv_snd B)
  have : IsIso (λ_ G).inv.left := inferInstanceAs (IsIso ((Over.forget _).map (λ_ G).inv))
  refine hj (eq_zero_of_dominant U.P.L.isLB σ (F ≫ (λ_ G).inv.left) (fun y J hJ => ?_) j)
  choose J' hJ' using fun χ : G'.left ⟶ G'.left => exists_chart U'.P.L.isLB (χ y)
  have e₁ := H _ (λ_ G').inv.left (F ≫ (λ_ G).inv.left)
    (by rw [Category.assoc, e, ← Category.assoc, e, Category.id_comp, Category.comp_id]) y J J' hJ hJ'
  rw [sval_zero σ' h0 _ y hJ', MulZeroClass.mul_zero] at e₁
  exact e₁

end GlobalTheory.PullNonzero
end

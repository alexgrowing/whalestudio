import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHom
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomLoc
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsDescendHom
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsPullInjLoc
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomSectionsLoc
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

theorem SpreadHomLoc.proof (h₁ : DescendHom.Statement) (h₂ : PullInjLoc.Statement)
    (h₃ : SpreadHomSectionsLoc.Statement) : SpreadHomLoc.Statement := by
  intro X f _ _ p U F G hF hG φ
  obtain ⟨m₁, hm₁, hp₁, H₁⟩ := h₂ X f p U G hG
  obtain ⟨m₂, hm₂, hp₂, H₂⟩ := h₃ X f p U F G hF hG φ
  refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, fun h => ((Nat.Prime.dvd_mul p.2).1 h).elim hp₁ hp₂,
    fun n hn hmn hpn => ?_⟩
  have hle : U ⊓ invOpen f n ≤ U := inf_le_left
  have hunit : IsUnit (((n : ℤ) : ℤ) : ZLoc p) :=
    isUnit_intCast_zLoc p n (by exact_mod_cast hpn)
  have hrange : Set.range (baseChangeMap f (ZLoc p) ∣_ U) ⊆ Set.range (X.homOfLE hle) := by
    rintro _ ⟨y, rfl⟩
    have hy : ((baseChangeMap f (ZLoc p) ∣_ U) y).1 ∈ invOpen f n := by
      rw [morphismRestrict_base_coe]
      have := range_baseChangeMap_subset f (ZLoc p) n hunit ⟨y.1, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    exact ⟨⟨_, ((baseChangeMap f (ZLoc p) ∣_ U) y).2, hy⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  have e₂ : IsOpenImmersion.lift (X.homOfLE hle) _ hrange ≫ X.homOfLE hle =
      baseChangeMap f (ZLoc p) ∣_ U := IsOpenImmersion.lift_fac _ _ _
  have hR : ∀ V : (U : Scheme.{0}).Opens, V ≤ (X.homOfLE hle).opensRange →
      V ≤ invOpen (U.ι ≫ f) n := by
    intro V hV x hx
    have := hV hx
    rw [Scheme.opensRange_homOfLE] at this
    exact this.2
  obtain ⟨ψ, hψ⟩ := h₁ _ _ _ (X.homOfLE hle) _ _ e₂ F G φ
    (fun V hV => H₁ n hn (dvd_of_mul_right_dvd hmn) hpn V (hR V hV))
    (fun V hV => H₂ n hn (dvd_of_mul_left_dvd hmn) hpn V (hR V hV))
  refine ⟨ψ, ?_⟩
  have eg : Scheme.homOfLE _ ((baseChangeMap f (ZLoc p)).preimage_mono hle) ≫
      IsOpenImmersion.lift (X.homOfLE hle) _ hrange =
      baseChangeMap f (ZLoc p) ∣_ (U ⊓ invOpen f n) := by
    rw [← cancel_mono (X.homOfLE hle), Category.assoc, e₂,
      morphismRestrict_homOfLE (baseChangeMap f (ZLoc p)) _ U hle]
  rw [← hψ, pullbackHomAlong_trans e₂ (morphismRestrict_homOfLE (baseChangeMap f (ZLoc p)) _ U hle).symm
    eg rfl]

end GroundTheory.Heights₂.Heights.Model

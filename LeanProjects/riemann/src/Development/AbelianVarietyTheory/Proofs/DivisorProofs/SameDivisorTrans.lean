import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

private theorem resG_resG_sameDiv {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem SameDiv.trans_of_isLB : ∀ (X : Scheme.{0}) (L M N : LB X) (σ : L.Sec) (τ : M.Sec) (υ : N.Sec),
    M.IsLB → SameDiv σ τ → SameDiv τ υ → SameDiv σ υ := by
  intro X L M N σ τ υ _ h₁ h₂ x
  obtain ⟨U₁, i, j, hi, hj, u₁, hx₁, e₁⟩ := h₁ x
  obtain ⟨U₂, j', k, hj', hk, u₂, hx₂, e₂⟩ := h₂ x
  have hV : U₁ ⊓ U₂ ≤ M.U j ⊓ M.U j' := le_inf (inf_le_left.trans hj) (inf_le_right.trans hj')
  have c := congrArg (resG X hV) (τ.compat j j')
  have e₁' := congrArg (resG X (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) e₁
  have e₂' := congrArg (resG X (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) e₂
  change resG X hV (resG X inf_le_left (τ.f j)) =
    resG X hV ((M.g j j' : Γ(X, M.U j ⊓ M.U j')) * resG X inf_le_right (τ.f j')) at c
  simp only [map_mul, resG_resG_sameDiv] at c e₁' e₂'
  refine ⟨U₁ ⊓ U₂, i, k, inf_le_left.trans hi, inf_le_right.trans hk,
    res inf_le_left u₁ * res hV (M.g j j') * res inf_le_right u₂, ⟨hx₁, hx₂⟩, ?_⟩
  simp only [Units.val_mul, res, Units.coe_map, MonoidHom.coe_coe]
  rw [e₁', c, e₂']
  simp only [resG, mul_assoc]

end GlobalTheory.LogPair

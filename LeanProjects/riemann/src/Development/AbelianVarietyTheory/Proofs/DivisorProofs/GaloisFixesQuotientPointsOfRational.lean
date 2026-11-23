import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GalFixQ

open GlobalTheory.TorusExt

theorem qkExt_equiv_of_rational : ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (D₂ : DegData R₂ (maximalIdeal R₂)) (n : ℕ), (∀ p : QkPt D₂.toPre (Kb R₂) n, ∃ (p₀ : QkPt D₂.toPre (FractionRing R₂) n) (p₁ : QkPt D₂.toPre (Kb R₂) n), QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ ∧ QkPt.Equiv D₂.toPre (Kb R₂) p₁ p) → ∀ σ : Kb R₂ →ₐ[FractionRing R₂] Kb R₂, ∀ p p' : QkPt D₂.toPre (Kb R₂) n, QkExt σ.toRingHom p p' → QkPt.Equiv D₂.toPre (Kb R₂) p p' := by
  intro R₂ _ _ _ D₂ n hrat σ p p' hpp'
  have hB := D₂.tau_bimult
  have hf : σ.toRingHom.comp (algebraMap (FractionRing R₂) (Kb R₂)) = algebraMap (FractionRing R₂) (Kb R₂) :=
    σ.comp_algebraMap
  have ha : (algebraMap (FractionRing R₂) (Kb R₂)).comp (algebraMap (FractionRing R₂) (FractionRing R₂)) =
      algebraMap (FractionRing R₂) (Kb R₂) := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  obtain ⟨p₀, p₁, e₁, h₁⟩ := hrat p
  have hq : QkExt σ.toRingHom p₁ (qkExt hB σ.toRingHom hf p₁) := (qkExt_iff hB _ hf _ _).2 rfl
  have e₂ := GlobalTheory.LabTrans.qkExt_trans e₁ hq
  rw [hf] at e₂
  have hfix : qkExt hB σ.toRingHom hf p₁ = p₁ :=
    ((qkExt_iff hB _ ha _ _).1 e₂).trans ((qkExt_iff hB _ ha _ _).1 e₁).symm
  rw [hfix] at hq
  exact equiv_trans hB (equiv_symm hB h₁) (equiv_of_qkExt hB σ.toRingHom hf hq hpp' h₁)

end GlobalTheory.Mum.GalFixQ

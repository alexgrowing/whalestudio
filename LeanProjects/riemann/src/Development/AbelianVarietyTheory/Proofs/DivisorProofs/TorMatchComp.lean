import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

theorem torMatch_comp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (g₂ : V →+* V₂) (β₂ : G₂.left ⟶ G'.left), Function.Injective g₂ → (∀ k : ℕ, IsUnit (k : R) → IsUnit (k : V)) → ∀ ρ ρ₂, TorMatch U U' g β ρ → TorMatch U' U₂ g₂ β₂ ρ₂ → TorMatch U U₂ (g₂.comp g) (β₂ ≫ β) (ρ₂.comp ρ) := by
  intro R _ _ _ hRb G _ _ hG D A U V _ _ _ hVb G' _ _ hG' D' A' U' g β V₂ _ _ _ hV₂b G₂ _ _ hG₂ D₂ A₂ U₂ g₂ β₂
    hg₂ hkV ρ ρ₂ h₁ h₂
  intro F _ _ _ _ hF k hk τ τ₂ q q₂ a a₂ hτ₂ hττ hqy hqt hq₂y hq₂t ha ha₂
  have hinj : Function.Injective ((algebraMap (FractionRing V₂) F).comp ((algebraMap V₂ (FractionRing V₂)).comp g₂)) :=
    (algebraMap (FractionRing V₂) F).injective.comp ((IsFractionRing.injective V₂ (FractionRing V₂)).comp hg₂)
  letI : Algebra (FractionRing V) F := (IsFractionRing.lift hinj).toAlgebra
  have hV : ∀ v, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) v) =
      algebraMap (FractionRing V₂) F (algebraMap V₂ (FractionRing V₂) (g₂ v)) := fun v =>
    IsFractionRing.lift_algebraMap hinj v
  have hk' : IsUnit (k : V) := hkV k hk
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  let τ' : Multiplicative D'.toPre.X →* Fˣ := τ₂.comp (AddMonoidHom.toMultiplicative ρ₂)
  have hτ' : τ' ^ k = 1 := MonoidHom.ext fun χ => DFunLike.congr_fun hτ₂ _
  obtain ⟨q', hq'y, hq't⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D'.tau_bimult (k := k) τ' hτ'
  obtain ⟨hV', _⟩ := hVb
  obtain ⟨f', ⟨i', -⟩, -⟩ := GlobalTheory.TorsionIso.torsion_clause V (maximalIdeal V) hV' D' A' G' hG' U' F k hk1
  have e₁ := h₁ F (fun r => by rw [hF, hV]; rfl) k hk τ τ' q q' a (f' q') hτ' hττ hqy hqt hq'y hq't ha ((i' _ _).2 rfl)
  have e₂ := h₂ F hV k hk' τ' τ₂ q' q₂ (f' q') a₂ hτ₂ (fun _ => rfl) hq'y hq't hq₂y hq₂t ((i' _ _).2 rfl) ha₂
  rw [e₁, reassoc_of% e₂]

end GlobalTheory.Poinc.Eq8

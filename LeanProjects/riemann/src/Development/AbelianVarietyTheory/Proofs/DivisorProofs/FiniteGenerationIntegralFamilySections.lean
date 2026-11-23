import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinSubRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetPowSmulMem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem finFam_finite : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsLocallyNoetherian S] {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)), (⨆ i, V i) = ⊤ →
    (∀ i, ∀ y ∈ t i, (gp.app (V i)).hom.IsIntegralElem y) → ∀ W : S.Opens, IsAffineOpen W →
    ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ W), (∀ y ∈ s, y ∈ finFam gp V t W) ∧
      ∀ x ∈ finFam gp V t W, ∃ c : Γ(Sp K, gp ⁻¹ᵁ W) → Γ(S, W), x = ∑ y ∈ s, (gp.app W).hom (c y) * y := by
  first
  | exact @_root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite
  | exact _root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite
  | (apply _root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite ..)

end GlobalTheory.Mum

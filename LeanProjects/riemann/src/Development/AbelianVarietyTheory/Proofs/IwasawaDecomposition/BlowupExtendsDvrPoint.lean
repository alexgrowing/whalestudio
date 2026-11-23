import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef

theorem blow_sabMap_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n : ℕ), IsBlowOf X Z Y BY π e J EX n → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ gen Y) (t : SAB H (Sp W)), SABMap t Y.t (χ ≫ genι Y) → Set.range (jK W ≫ χ ≫ genι Y) ⊆ Set.range Y.j → Nonempty (SABMap t X.t (χ ≫ e.hom ≫ genι Z ≫ π)) ∧ Set.range (jK W ≫ χ ≫ e.hom ≫ genι Z ≫ π) ⊆ Set.range X.j := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n hB W _ _ _ hW χ t mt hr
  obtain ⟨-, hZX, hπs, hjQ, -, -, -⟩ := hB

  have hZY : Z.jQ ≫ e.inv = Y.jQ := by rw [← hjQ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨t₀, n₁, n₂, -⟩ := cmpSt_of_sabExtNormalSt (sabExtNormalSt_of_homExtNormalSt homExtNormal) E H D l Xo c
    c.F (𝓞 c.F) (RingHom.id c.F) (algebraMap (𝓞 c.F) c.F) Y Z e.inv hZY
    (ModelRelCompare.normal_genericFibre Z (ModelRelCompare.isDedFrac_in_use c).1).1
  obtain ⟨a⟩ := TraitOrder.cancel (g := χ ≫ e.hom) (h := χ ≫ genι Y)
    (by rw [Category.assoc, e.hom_inv_id_assoc]) n₂ mt
  obtain ⟨b⟩ := TraitOrder.comp (h := (χ ≫ e.hom) ≫ genι Z) rfl n₁ a

  let ρ : gen Z ⟶ gen X := pullback.map Z.s (spMap (algebraMap (𝓞 c.F) c.F)) X.s (spMap (algebraMap (𝓞 c.F) c.F)) π
    (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hπs]) (by rw [Category.comp_id, Category.id_comp])
  have hρι : ρ ≫ genι X = genι Z ≫ π := pullback.lift_fst _ _ _
  have hρ : Z.jQ ≫ ρ = X.jQ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hρι, ← Category.assoc]
      exact hZX
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Z.jQ_over, X.jQ_over]
  obtain ⟨t₁, m₁, m₂, -⟩ := cmpSt_of_sabExtNormalSt (sabExtNormalSt_of_homExtNormalSt homExtNormal) E H D l Xo c
    (𝓞 c.F) (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) (algebraMap (𝓞 c.F) c.F) X Z ρ hρ
    (ModelRelCompare.normal_genericFibre Z (ModelRelCompare.isDedFrac_in_use c).1).1
  obtain ⟨a'⟩ := TraitOrder.cancel (g := χ ≫ e.hom) rfl m₁ b
  obtain ⟨b'⟩ := TraitOrder.comp (h := χ ≫ e.hom ≫ genι Z ≫ π)
    (by simp only [hρι, Category.assoc]) m₂ a'
  refine ⟨⟨b'⟩, ?_⟩

  rintro _ ⟨p, rfl⟩
  have hz : (jK W ≫ χ) p ∈ Set.range Y.jQ := by
    rw [← Y.ab_gen]
    obtain ⟨q, hq⟩ := hr ⟨p, rfl⟩
    show (jK W ≫ χ ≫ genι Y) p ∈ abLocus Y.t.G
    rw [← hq]
    show genι Y (Y.jQ q) ∈ abLocus Y.t.G
    rw [← Set.mem_preimage, Y.ab_gen]
    exact ⟨q, rfl⟩
  obtain ⟨q, hq⟩ := hz
  refine ⟨q, ?_⟩
  rw [← hZX]
  show (Z.j ≫ π) q = _
  rw [show Z.j = Z.jQ ≫ genι Z from rfl, ← hjQ]
  simp only [Scheme.Hom.comp_apply] at hq ⊢
  rw [hq]

end GlobalTheory.TorRef

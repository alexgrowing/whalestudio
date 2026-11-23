import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Side
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpecMapFieldCancel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry GlobalTheory.ShFam.GalCarry.Corr

set_option autoImplicit false

namespace GlobalTheory.ShFam.GalCarry.Corr

theorem partner_generic_descends : ∀ (F : Type) [Field F] [CharZero F] (I I' : Type) (Y : I → Var F) (Y' : I' → Var F)
    (Rel : ∀ (K : Type) [Field K] (i : I) (i' : I'), (Sp K ⟶ (Y i).X) → (Sp K ⟶ (Y' i').X) → Prop), Side Y Y' Rel → ∀ i : I, ∃ (i' : I') (p' : Sp (Y i).Fn ⟶ (Y' i').X),
      p' ≫ (Y' i').str = genericPt (Y i) ≫ (Y i).str ∧
      Rel (AlgebraicClosure (Y i).Fn) i i' (spMap (algebraMap (Y i).Fn (AlgebraicClosure (Y i).Fn)) ≫ genericPt (Y i))
        (spMap (algebraMap (Y i).Fn (AlgebraicClosure (Y i).Fn)) ≫ p') := by
  intro F _ _ I I' Y Y' Rel hS i
  obtain ⟨h1, h2, h3, -⟩ := hS
  obtain ⟨ρ, hρ⟩ : ∃ ρ : F →+* (Y i).Fn, genericPt (Y i) ≫ (Y i).str = spMap ρ := ⟨_, (Spec.map_preimage _).symm⟩
  haveI : CharZero (Y i).Fn := (RingHom.charZero_iff ρ.injective).1 inferInstance
  set K := (Y i).Fn
  set ι := algebraMap K (AlgebraicClosure K)
  obtain ⟨⟨i', q⟩, hq, hqu⟩ := h3 (AlgebraicClosure K) i (spMap ι ≫ genericPt (Y i))
  have hfix : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      spMap (σ : AlgebraicClosure K →+* AlgebraicClosure K) ≫ q = q := by
    intro σ
    have hσι : (σ : AlgebraicClosure K →+* AlgebraicClosure K).comp ι = ι := RingHom.ext fun a => σ.commutes a
    have hR := h2 _ _ (σ : AlgebraicClosure K →+* AlgebraicClosure K) i i' _ _ hq
    rw [← Category.assoc, GlobalTheory.FieldPts.spMap_comp', hσι] at hR
    have := hqu ⟨i', spMap (σ : AlgebraicClosure K →+* AlgebraicClosure K) ≫ q⟩ hR
    simpa using this
  obtain ⟨p, hp⟩ := GlobalTheory.FieldPts.exists_of_fixed q hfix
  refine ⟨i', p, ?_, hp ▸ hq⟩
  refine GlobalTheory.spec_map_field_cancel ι _ _ ?_
  have e := h1 _ i i' _ _ hq
  simp only [Category.assoc] at e ⊢
  rw [← Category.assoc, hp, e]

end GlobalTheory.ShFam.GalCarry.Corr

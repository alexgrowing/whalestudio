import Development.EtaleCohomology.EtaleTrace.GenEtalePfBasic

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

def GenAffineData : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P]
  (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p → LocallyOfFiniteType r → IsFinite π → Surjective π →
  ∃ U : P.Opens, IsAffineOpen U ∧ (U : Set P).Nonempty ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ IsNoetherianRing Γ(P, U) ∧
    (π.app U).hom.Finite ∧ Function.Injective (π.app U).hom

def GenEtaleAtBot : Prop := ∀ {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P] (π : X ⟶ P) (U : P.Opens), IsAffineOpen U →
  (U : Set P).Nonempty → IsAffineOpen (π ⁻¹ᵁ U) → (π.app U).hom.Finite → Function.Injective (π.app U).hom →
  (π.stalkMap (genericPoint X)).hom.FormallyUnramified →
  ∃ _ : (⊥ : Ideal Γ(X, π ⁻¹ᵁ U)).IsPrime,
    (letI := (π.app U).hom.toAlgebra; Algebra.IsEtaleAt Γ(P, U) (⊥ : Ideal Γ(X, π ⁻¹ᵁ U)))

theorem GenAffineSetup_of (h1 : GenAffineData) (h2 : GenEtaleAtBot) : GenAffineSetup := by
  intro k _ _ X P _ _ p r π hπ hr hfin hsurj hun
  obtain ⟨U, hU, hne, hU', hN, hf, hi⟩ := h1 k p r π hπ hr hfin hsurj
  exact ⟨U, hU, hne, hU', hN, hf, hi, h2 π U hU hne hU' hf hi hun⟩

theorem GenEtale_of' (h1 : GenAffineData) (h2 : GenEtaleAtBot) : GenEtale :=
  GenEtale_of (GenAffineSetup_of h1 h2) etaleOverBasic

end LateralTheory.EtaleTrace.Cov

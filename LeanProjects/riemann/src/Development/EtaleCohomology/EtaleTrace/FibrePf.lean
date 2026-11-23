import Development.EtaleCohomology.EtaleTrace.LCoverCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

def GenEtale : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P] (p : X ⟶ S k)
  (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p → LocallyOfFiniteType r → IsFinite π → Surjective π →
  (π.stalkMap (genericPoint X)).hom.FormallyUnramified → ∃ V : P.Opens, (V : Set P).Nonempty ∧ Etale (π ∣_ V)

def RatPtIn : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {P : Scheme.{0}} (r : P ⟶ S k), LocallyOfFiniteType r →
  ∀ V : P.Opens, (V : Set P).Nonempty → ∃ t : Pt r, ∀ x, t.1.base x ∈ V

def FibreOfEtale : Prop := ∀ (k : Type) [Field k] {X P : Scheme.{0}} (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p →
  ∀ V : P.Opens, Etale (π ∣_ V) → ∀ t : Pt r, (∀ x, t.1.base x ∈ V) → Etale (equalizer.ι π (p ≫ t.1) ≫ p)

theorem Fibre_of (h1 : GenEtale) (h2 : RatPtIn) (h3 : FibreOfEtale) : Fibre := by
  intro k _ _ X P _ _ p r π hπ hr hfin hsurj hun
  obtain ⟨V, hV, hE⟩ := h1 k p r π hπ hr hfin hsurj hun
  obtain ⟨t, ht⟩ := h2 k r hr V hV
  exact ⟨t, h3 k p r π hπ V hE t ht⟩

end LateralTheory.EtaleTrace.Cov

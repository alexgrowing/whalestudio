import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts SameModel modVec resImage residue ResField)

def RestrictionPoints.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) (Ω : Type) [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime],
    (∀ k, y ⟨k, c k⟩ ≠ 0) →
      modelPts S (modVec S y c p) =
        {z' | ∃ z ∈ modelPts S y, z ≤ locIn (chartRingOver S y c) p ∧
          z' = Subring.closure (resImage S y c p z)}

def RestrictionSections.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) (Ω : Type) [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime],
    (∀ k, y ⟨k, c k⟩ ≠ 0) →
      ∀ β : K → ℤ, ∀ s ∈ secOver S y β,
        residue S y c p (s * ∏ k, y ⟨k, c k⟩ ^ (-β k)) ∈ secOver S (modVec S y c p) β

def RestrictionSame.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) (K' : Type) (ι' : K' → Type)
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω),
    SameModel S y y' →
    ∀ (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime], (∀ k, y ⟨k, c k⟩ ≠ 0) →
      ∀ (c' : ∀ k, ι' k) (p' : Ideal (chartRingOver S y' c')) [p'.IsPrime],
        (∀ k, y' ⟨k, c' k⟩ ≠ 0) →
        locIn (chartRingOver S y' c') p' = locIn (chartRingOver S y c) p →
        ∃ φ : ResField S y c p ≃ₐ[S] ResField S y' c' p',
          (∀ z ∈ modelPts S y, z ≤ locIn (chartRingOver S y c) p →
            φ '' resImage S y c p z = resImage S y' c' p' z) ∧
          SameModel S (fun q => φ (modVec S y c p q)) (modVec S y' c' p')

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

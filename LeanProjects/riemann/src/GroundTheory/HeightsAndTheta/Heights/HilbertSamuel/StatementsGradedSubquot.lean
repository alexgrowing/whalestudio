import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedModOfSubsingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def subGrading {S : Type*} [CommRing S] {K : Type*} {ι : K → Type*} {M : Type*} [AddCommGroup M]
    [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (N : Submodule (MRingOver S ι) M) (c : K → ℤ) : Submodule S N :=
  (𝓜 c).comap (N.subtype.restrictScalars S)

def quotGrading {S : Type*} [CommRing S] {K : Type*} {ι : K → Type*} {N : Type*} [AddCommGroup N]
    [Module (MRingOver S ι) N] [Module S N] [IsScalarTower S (MRingOver S ι) N]
    (𝓝 : (K → ℤ) → Submodule S N) (L : Submodule (MRingOver S ι) N) (c : K → ℤ) : Submodule S (N ⧸ L) :=
  (𝓝 c).map (L.mkQ.restrictScalars S)

def GradedSubquot.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (G H : Set M),
    KH.IsMGraded S ι 𝓜 → (∀ x ∈ G, ∃ c, x ∈ 𝓜 c) → (∀ x ∈ H, ∃ c, x ∈ 𝓜 c) →
    Submodule.span (MRingOver S ι) G ≤ Submodule.span (MRingOver S ι) H →
    KH.IsMGraded S ι (subGrading 𝓜 (Submodule.span (MRingOver S ι) H)) ∧
      KH.IsMGraded S ι (quotGrading (subGrading 𝓜 (Submodule.span (MRingOver S ι) H))
        ((Submodule.span (MRingOver S ι) G).comap (Submodule.span (MRingOver S ι) H).subtype))

abbrev noIdx : Fin 0 → Type := fun _ => Fin 1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

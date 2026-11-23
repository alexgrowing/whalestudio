import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedModOfSubsingleton
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGradedSubquot
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def IsClosedMultiPt {S : Type*} [CommRing S] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (P : Ideal (MRingOver S ι)) : Prop :=
  IsMultiProjPrime P ∧ ∀ Q : Ideal (MRingOver S ι), IsMultiProjPrime Q → P ≤ Q → Q = P

def GenNear (S : Type*) [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] (ι : K → Type*)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M]
    [Module S M] [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ)
    (f : MRingOver S ι) (δ : K → ℕ) : Prop :=
  ∀ I : KH.Cell K ι 0, ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d,
    ∃ (n : ℕ) (t : MRingOver S ι) (a : K → ℕ) (r : ℕ) (p : Fin r → MRingOver S ι) (z : Fin r → KH.CechC S ι M 0),
      t ∈ KH.cellMon S I.1 ∧ IsMultiHomog t a ∧ (∀ j, IsMultiHomog (p j) (a + n • δ)) ∧
      (∀ j, z j ∈ KH.cechZc ι 𝓜 d 0) ∧ (f ^ n * t) • x = ∑ j, p j • z j I

def locIdealPart {S : Type*} [CommRing S] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (T : Submonoid (MRingOver S ι)) (P : Ideal (MRingOver S ι)) (d : K → ℤ) :
    Submodule S (LocalizedModule T M) :=
  Submodule.span S {w | ∃ (p : MRingOver S ι) (a : K → ℕ) (y : LocalizedModule T M), p ∈ P ∧ IsMultiHomog p a ∧
    y ∈ KH.locPart ι 𝓜 T (d - fun k => (a k : ℤ)) ∧ w = p • y}

section Point

def pointCell : KH.Cell Unit pointIdx 0 := ⟨fun _ => Finset.univ, fun _ => Finset.univ_nonempty, by simp⟩

end Point

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

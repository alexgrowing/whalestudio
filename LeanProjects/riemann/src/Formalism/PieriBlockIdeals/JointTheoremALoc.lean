import Formalism.RankGapBounds.TheoremALocOfLemmaA

noncomputable section

open TensorProduct

namespace Formalism.CohomologicalDescent

open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization

def exactExp {k : Type} [CommRing k] {A : Type} [AddCommGroup A] [Module k A]
    (l : k) (B : Submodule k A) : ℕ := sInf {e : ℕ | LatIncl l B e}

def JointTheoremA : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (ι : Type) [Fintype ι]
    (A : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
    (B : ∀ i, Submodule k (A i)) (ρK : Representation k K (⨂[k] i, A i)) (l : k),
    (∀ i, ∃ e, LatIncl l (B i) e) →
    (∀ f ∈ AMFK k Γ K ρK, l ^ (∑ i, exactExp l (B i)) • f ∈ formsIn Γ K ρK (tensSub B)) ∧
    sInf {J : ℕ | ∀ f ∈ AMFK k Γ K ρK, l ^ J • f ∈ formsIn Γ K ρK (tensSub B)} ≤
      ∑ i, exactExp l (B i)

def JointTheoremALoc : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (ι : Type) [Fintype ι]
    (A : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
    (B : ∀ i, Submodule k (A i)) (ρK : Representation k K (⨂[k] i, A i)) (l : k)
    (T : Type) [CommRing T] [Algebra k T] [Module T (AMFK k Γ K ρK)]
    [IsScalarTower k T (AMFK k Γ K ρK)] (S : Submonoid T),
    (∀ i, ∃ e, LatIncl l (B i) e) →
    (∀ y : LocalizedModule S (AMFK k Γ K ρK),
        (algebraMap k T l) ^ (∑ i, exactExp l (B i)) • y ∈
          locSet S {x : AMFK k Γ K ρK | (x : G → ⨂[k] i, A i) ∈ formsIn Γ K ρK (tensSub B)}) ∧
    sInf {J : ℕ | ∀ y : LocalizedModule S (AMFK k Γ K ρK),
        (algebraMap k T l) ^ J • y ∈
          locSet S {x : AMFK k Γ K ρK | (x : G → ⨂[k] i, A i) ∈ formsIn Γ K ρK (tensSub B)}} ≤
      ∑ i, exactExp l (B i)

end Formalism.CohomologicalDescent

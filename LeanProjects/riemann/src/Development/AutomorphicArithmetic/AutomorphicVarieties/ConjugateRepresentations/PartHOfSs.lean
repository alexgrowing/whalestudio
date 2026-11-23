import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairFactsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor
open scoped TensorProduct

namespace UpperTheory.V.Cj

section Defs

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def ConjMat (σ : ℂ ≃+* ℂ) {Ξ Ξ' : AlgRep E a} (h : Ξ.d = Ξ'.d) : Prop :=
  ∀ γ i j, ratC Ξ' γ (Fin.cast h i) (Fin.cast h j) = σ (ratC Ξ γ i j)

def sigC {L S : Type} {d d' : ℕ} (σ : ℂ ≃+* ℂ) (h : d = d') (c : L → S → Fin d → ℂ) : L → S → Fin d' → ℂ :=
  fun z y i => σ (c z y (Fin.cast h.symm i))

def RelAt (U : Subgroup (GL (Fin a) (Af E))) (σ : ℂ ≃+* ℂ) {Ξ Ξ' : AlgRep E a} (h : Ξ.d = Ξ'.d) {q : ℕ}
    (α : Co Ξ q) (β : Co Ξ' q) : Prop :=
  IsLev U Ξ α ∧ IsLev U Ξ' β ∧ ∃ c c', IsPer U Ξ α c ∧ IsPer U Ξ' β c' ∧ HCob (levelRep ⊤ U (ratC Ξ')) q (c' - sigC σ h c)

def Lev (Ξ : AlgRep E a) {q : ℕ} (ω : Co Ξ q) : Prop :=
  ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧ IsLev U Ξ ω

def Exact (Ξ : AlgRep E a) {q : ℕ} (ω : Co Ξ q) : Prop :=
  ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧
    IsRelExact U Ξ ω

def HasChar (m : (E →+* ℂ) → Multiset ℂ) (φ : Sm E a) : Prop :=
  ∀ (t : E →+* ℂ) (u : ℂ), cap t u φ = ((m t).map (u + ·)).prod • φ

end Defs

def PartA : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) →
    ∀ (σ : ℂ ≃+* ℂ) (Ξ Ξ' : AlgRep E a) (h : Ξ.d = Ξ'.d), ConjMat σ h → ∀ (q : ℕ) (α : Co Ξ q),
      IsLev U Ξ α → dCo (smLie Ξ) α = 0 → CSupp α →
      ∃ U' ≤ U, IsOpen (U' : Set (GL (Fin a) (Af E))) ∧ IsCompact (U' : Set (GL (Fin a) (Af E))) ∧
        ∃ β : Co Ξ' q, dCo (smLie Ξ') β = 0 ∧ CSupp β ∧ RelAt U' σ h α β

def PartH : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (Ξ : AlgRep E a) (m : (E →+* ℂ) → Multiset ℂ),
    (∀ t, AlgInfChar Ξ t ((m t).map Neg.neg)) → ∀ q : ℕ, ∃ M : Submodule ℂ (Co Ξ q),
      (∀ x, ∀ ω ∈ M, trans x ω ∈ M) ∧ (∀ ω ∈ M, Lev Ξ ω ∧ dCo (smLie Ξ) ω = 0) ∧
      (∀ ω ∈ M, ∀ X i, IsAutForm (cmp i (ω X)) ∧ HasChar m (cmp i (ω X))) ∧
      (∀ ω ∈ M, Exact Ξ ω → ω = 0) ∧
      ∀ α : Co Ξ q, Lev Ξ α → dCo (smLie Ξ) α = 0 → CSupp α → ∃ ω ∈ M, Exact Ξ (α - ω)

def PartHss : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (Ξ : AlgRep E a) (m : (E →+* ℂ) → Multiset ℂ),
    (∀ t, AlgInfChar Ξ t ((m t).map Neg.neg)) → ∀ q : ℕ, ∃ M : Submodule ℂ (Co Ξ q),
      (∀ x, ∀ ω ∈ M, trans x ω ∈ M) ∧ (∀ ω ∈ M, Lev Ξ ω ∧ dCo (smLie Ξ) ω = 0) ∧
      (∀ ω ∈ M, ∀ X i, IsAutForm (cmp i (ω X)) ∧ HasChar m (cmp i (ω X))) ∧
      (∀ N ≤ M, (∀ x, ∀ ω ∈ N, trans x ω ∈ N) → ∃ N' ≤ M, (∀ x, ∀ ω ∈ N', trans x ω ∈ N') ∧ N ⊓ N' = ⊥ ∧ N ⊔ N' = M) ∧
      ∀ α : Co Ξ q, Lev Ξ α → dCo (smLie Ξ) α = 0 → CSupp α → ∃ ω ∈ M, Exact Ξ (α - ω)

def ExactSub : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (q : ℕ),
    ∃ B : Submodule ℂ (Co Ξ q), (∀ ω, ω ∈ B ↔ Exact Ξ ω) ∧ ∀ x, ∀ ω ∈ B, trans x ω ∈ B

theorem partH_of_ss (hB : ExactSub) (h : PartHss) : PartH := by
  intro E _ _ _ a ha Ξ m hm q
  obtain ⟨M, h1, h2, h3, h4, h5⟩ := h E a ha Ξ m hm q
  obtain ⟨B, b1, b2⟩ := hB E a Ξ q
  obtain ⟨N, n1, n2, n3, n4⟩ := h4 (M ⊓ B) inf_le_left fun x ω hω => ⟨h1 x ω hω.1, b2 x ω hω.2⟩
  refine ⟨N, n2, fun ω hω => h2 ω (n1 hω), fun ω hω => h3 ω (n1 hω), fun ω hω he => ?_, fun α a1 a2 a3 => ?_⟩
  · exact (Submodule.mem_bot ℂ).1 (n3 ▸ (⟨⟨n1 hω, (b1 ω).2 he⟩, hω⟩ : ω ∈ M ⊓ B ⊓ N))
  · obtain ⟨ω, hω, he⟩ := h5 α a1 a2 a3
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (n4.ge hω)
    refine ⟨z, hz, (b1 _).1 ?_⟩
    have e : α - z = α - (y + z) + y := by abel
    rw [e]
    exact B.add_mem ((b1 _).2 he) hy.2

end UpperTheory.V.Cj

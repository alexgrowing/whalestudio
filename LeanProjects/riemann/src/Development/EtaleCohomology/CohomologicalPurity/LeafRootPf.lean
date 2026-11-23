import Development.EtaleCohomology.CohomologicalPurity.LeafHensCutDef

noncomputable section
open Polynomial

namespace LateralTheory.CohomologicalPurity.Hz

def LeafRootStd : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) (f : A[X]) (a : A), f.Monic → f.eval a ∈ I →
  IsUnit (Ideal.Quotient.mk I (f.derivative.eval a)) →
  ∃ (S : Type) (_ : CommRing S) (φ : A →+* S) (b : S), φ.Etale ∧
    (∃ r : S →+* A ⧸ I, r.comp φ = Ideal.Quotient.mk I) ∧ (∀ s : S, ∃ a' : A, s - φ a' ∈ I.map φ) ∧
    (f.map φ).IsRoot b ∧ b - φ a ∈ I.map φ ∧
    (∀ (B : Type) [CommRing B] (χ₁ χ₂ : S →+* B), χ₁.comp φ = χ₂.comp φ → χ₁ b = χ₂ b → χ₁ = χ₂) ∧
    (∀ (B : Type) [CommRing B] (ψ : A →+* B) (c : B), (f.map ψ).IsRoot c →
      IsUnit ((f.derivative.map ψ).eval c) → IsUnit (((f /ₘ (X - C a)).map ψ).eval c) →
      ∃ χ : S →+* B, χ.comp φ = ψ ∧ χ b = c)

def LeafRootHens : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B), HenselianRing B J →
  ∀ (ψ : A →+* B), I ≤ J.comap ψ → ∀ (f : A[X]) (a : A), f.Monic → f.eval a ∈ I →
  IsUnit (Ideal.Quotient.mk I (f.derivative.eval a)) →
  ∃ c : B, (f.map ψ).IsRoot c ∧ c - ψ a ∈ J ∧ IsUnit ((f.derivative.map ψ).eval c) ∧
    IsUnit (((f /ₘ (X - C a)).map ψ).eval c) ∧ ∀ c' : B, (f.map ψ).IsRoot c' → c' - ψ a ∈ J → c' = c

theorem LeafRoot_of (h1 : LeafRootStd) (h2 : LeafRootHens) : LeafRoot := by
  intro A _ I f a hf hfa hu
  obtain ⟨S, _, φ, b, he, hr, hs, hb, hba, hext, hlift⟩ := h1 A I f a hf hfa hu
  refine ⟨S, inferInstance, φ, b, ⟨he, hr, hs, ?_⟩, hb, hba⟩
  intro B _ J hJ ψ hIJ
  obtain ⟨c, hc, _, hc1, hc2, huniq⟩ := h2 A B I J hJ ψ hIJ f a hf hfa hu
  obtain ⟨χ, hχ, hχb⟩ := hlift B ψ c hc hc1 hc2
  refine ⟨χ, hχ, fun χ' hχ' => hext B χ' χ (hχ'.trans hχ.symm) ?_⟩
  rw [hχb]
  have hpa : χ' (φ a) = ψ a := by rw [← hχ']; rfl
  apply huniq
  · have h4 : (f.map φ).map χ' = f.map ψ := by rw [Polynomial.map_map, hχ']
    rw [← h4]
    exact Polynomial.IsRoot.map hb
  · have h3 : (I.map φ).map χ' ≤ J := by
      rw [Ideal.map_map, hχ', Ideal.map_le_iff_le_comap]; exact hIJ
    have h5 := h3 (Ideal.mem_map_of_mem χ' hba)
    rwa [map_sub, hpa] at h5

end LateralTheory.CohomologicalPurity.Hz

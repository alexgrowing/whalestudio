import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.JoinBlock

theorem mConeMap_rename {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) {Ω : Type} [Field Ω] (y : (Σ k, ι' k) → Ω)
    (hv : ∀ p, (v p).1 = κ p.1) (f : MvPolynomial (Σ k, ι k) ℤ) :
    mConeMap y (rename v f) = rename κ (mConeMap (y ∘ v) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, hv]

theorem imageZ_coord {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) {Ω : Type} [Field Ω] (y : (Σ k, ι' k) → Ω)
    (hκ : Function.Injective κ) (hv : ∀ p, (v p).1 = κ p.1) :
    imageZ v (mCoordIdeal y) = mCoordIdeal (y ∘ v) := by
  ext f
  simp only [imageZ, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker]
  change mConeMap y (rename v f) = 0 ↔ _
  rw [mConeMap_rename κ v y hv f]
  exact map_eq_zero_iff _ (rename_injective κ hκ)

theorem pullDeg_comp {K K' K'' : Type} (κ : K → K') (κ' : K' → K'')
    (hκ : Function.Injective κ) (hκ' : Function.Injective κ') (a : K → ℤ) :
    pullDeg (κ' ∘ κ) a = pullDeg κ' (pullDeg κ a) := by
  funext k''
  simp only [pullDeg]
  by_cases h' : ∃ k', κ' k' = k''
  · obtain ⟨k', rfl⟩ := h'
    rw [hκ'.extend_apply]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hκ.extend_apply]
      exact (hκ'.comp hκ).extend_apply a 0 k
    · have h2 : ¬∃ k, (κ' ∘ κ) k = κ' k' := fun ⟨k, hk⟩ => h ⟨k, hκ' hk⟩
      rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h2]
      rfl
  · have h2 : ¬∃ k, (κ' ∘ κ) k = k'' := fun ⟨k, hk⟩ => h' ⟨κ k, hk⟩
    rw [Function.extend_apply' _ _ _ h', Function.extend_apply' _ _ _ h2]

end GlobalTheory.CompanionTheory.Ar.Cmp.JoinBlock

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open GlobalTheory.CompanionTheory.Ar.Cmp.JoinBlock in

theorem join_block_maps : (∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω : Type) (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω), IsBlockMap Sum.inl (joinInl ι₁ ι₂) ∧ IsBlockMap Sum.inr (joinInr ι₁ ι₂) ∧ joinVec y₁ y₂ ∘ joinInl ι₁ ι₂ = y₁ ∧ joinVec y₁ y₂ ∘ joinInr ι₁ ι₂ = y₂) ∧ (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (Ω : Type) [Field Ω] (y : (Σ k, ι' k) → Ω), IsBlockMap κ v → imageZ v (mCoordIdeal y) = mCoordIdeal (y ∘ v)) ∧ (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (K'' : Type) [Fintype K''] (ι'' : K'' → Type) [∀ k, Fintype (ι'' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (κ' : K' → K'') (v' : (Σ k, ι' k) → Σ k, ι'' k), IsBlockMap κ v → IsBlockMap κ' v' → IsBlockMap (κ' ∘ κ) (v' ∘ v) ∧ ∀ a, pullDeg (κ' ∘ κ) a = pullDeg κ' (pullDeg κ a)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K₁ _ ι₁ _ K₂ _ ι₂ _ Ω y₁ y₂
    refine ⟨⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩, ⟨Sum.inr_injective, ?_, fun _ => rfl, ?_⟩, ?_, ?_⟩
    · rintro ⟨k, i⟩ ⟨k', i'⟩ h
      cases h
      rfl
    · rintro ⟨k', i⟩ ⟨k, rfl⟩
      exact ⟨⟨k, i⟩, rfl⟩
    · rintro ⟨k, i⟩ ⟨k', i'⟩ h
      cases h
      rfl
    · rintro ⟨k', i⟩ ⟨k, rfl⟩
      exact ⟨⟨k, i⟩, rfl⟩
    · funext ⟨k, i⟩
      rfl
    · funext ⟨k, i⟩
      rfl
  · intro K _ ι _ K' _ ι' _ κ v Ω _ y h
    exact imageZ_coord κ v y h.1 h.2.2.1
  · intro K _ ι _ K' _ ι' _ K'' _ ι'' _ κ v κ' v' h h'
    obtain ⟨hκ, hv, hc, hs⟩ := h
    obtain ⟨hκ', hv', hc', hs'⟩ := h'
    refine ⟨⟨hκ'.comp hκ, hv'.comp hv, fun p => ?_, ?_⟩, pullDeg_comp κ κ' hκ hκ'⟩
    · simp [hc', hc]
    · rintro q ⟨k, hk⟩
      obtain ⟨q', rfl⟩ := hs' q ⟨κ k, hk⟩
      have h1 : q'.1 = κ k := hκ' ((hc' q').symm.trans hk.symm)
      obtain ⟨p, rfl⟩ := hs q' ⟨k, h1.symm⟩
      exact ⟨p, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Cmp

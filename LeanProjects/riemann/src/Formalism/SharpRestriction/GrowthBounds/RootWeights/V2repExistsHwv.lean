import Formalism.SharpRestriction.GrowthBounds.RootWeights.HighestWeightModuleBounds

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem v2rep_comp_mem [CharZero K] (E : GLOps n K V) (Z : Submodule K V) (hZ : ∀ a, ∀ x ∈ Z, E a a x ∈ Z)
    (s : Finset (Fin n → ℤ)) : ∀ g : (Fin n → ℤ) → V, (∀ ν ∈ s, g ν ∈ weightSp E ν) → ∑ ν ∈ s, g ν ∈ Z →
      ∀ ν ∈ s, g ν ∈ Z := by
  induction s using Finset.strongInduction with
  | H s ih =>
  intro g hg hsum μ hμ
  by_cases hs : ∃ ν ∈ s, ν ≠ μ
  · obtain ⟨ν, hν, hne⟩ := hs
    obtain ⟨a, ha⟩ : ∃ a, μ a ≠ ν a := by
      by_contra h
      push_neg at h
      exact hne (funext h).symm
    let g' : (Fin n → ℤ) → V := fun ρ => (((ρ a - ν a : ℤ) : K)) • g ρ
    have hZ' : (E a a - (ν a : K) • (1 : Module.End K V)) (∑ ρ ∈ s, g ρ) ∈ Z := by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact Z.sub_mem (hZ a _ hsum) (Z.smul_mem _ hsum)
    have heq : (E a a - (ν a : K) • (1 : Module.End K V)) (∑ ρ ∈ s, g ρ) = ∑ ρ ∈ s.erase ν, g' ρ := by
      rw [map_sum, ← Finset.sum_erase_add _ _ hν]
      have h0 : (E a a - (ν a : K) • (1 : Module.End K V)) (g ν) = 0 := by
        have := (v2rep_mem_weightSp E ν (g ν)).mp (hg ν hν) a
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, this, sub_self]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have := (v2rep_mem_weightSp E ρ (g ρ)).mp (hg ρ (Finset.mem_of_mem_erase hρ)) a
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, this, ← sub_smul]
      simp only [g', Int.cast_sub]
    have hg' : ∀ ρ ∈ s.erase ν, g' ρ ∈ weightSp E ρ := fun ρ hρ =>
      (weightSp E ρ).smul_mem _ (hg ρ (Finset.mem_of_mem_erase hρ))
    have hIH := ih (s.erase ν) (Finset.erase_ssubset hν) g' hg' (heq ▸ hZ') μ
      (Finset.mem_erase.mpr ⟨hne.symm, hμ⟩)
    have hc : (((μ a - ν a : ℤ)) : K) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr ha
    have := Z.smul_mem (((μ a - ν a : ℤ) : K))⁻¹ hIH
    simp only [g'] at this
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  · push_neg at hs
    have : ∑ ν ∈ s, g ν = g μ :=
      Finset.sum_eq_single_of_mem μ hμ (fun ν hν hne => absurd (hs ν hν) hne)
    rw [this] at hsum
    exact hsum

theorem v2rep_graded [CharZero K] (E : GLOps n K V) (Z : Submodule K V) (hZ : ∀ a, ∀ x ∈ Z, E a a x ∈ Z)
    (x : V) (hx : x ∈ Z) (hw : x ∈ ⨆ ν, weightSp E ν) : x ∈ ⨆ ν, weightSp E ν ⊓ Z := by
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hw
  have hsum : ∑ ν ∈ f.support, f ν ∈ Z := by simpa [Finsupp.sum] using hx
  have key := v2rep_comp_mem E Z hZ f.support f (fun ν _ => hf ν) hsum
  show ∑ ν ∈ f.support, f ν ∈ _
  exact Submodule.sum_mem _ fun ν hν => Submodule.mem_iSup_of_mem ν ⟨hf ν, key ν hν⟩

def weightHeight' (ν : Fin n → ℤ) : ℤ := -∑ a : Fin n, (a.val : ℤ) * ν a

theorem v2rep_ht_root (ν : Fin n → ℤ) (a b : Fin n) (h : a < b) : weightHeight' ν < weightHeight' (ν + rootW a b) := by
  have hab : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast h
  simp only [weightHeight', rootW, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  linarith

def heightOperator' (E : GLOps n K V) : Module.End K V := -∑ a : Fin n, ((a.val : ℤ) : K) • E a a

theorem v2rep_H_apply (E : GLOps n K V) (ν : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ν) :
    heightOperator' E x = ((weightHeight' ν : ℤ) : K) • x := by
  rw [v2rep_mem_weightSp] at hx
  have h1 : heightOperator' E x = -∑ a : Fin n, (((a.val : ℤ) : K) * (ν a : K)) • x := by
    simp only [heightOperator', LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      hx, smul_smul]
  rw [h1, ← Finset.sum_smul, ← neg_smul]
  congr 1
  simp only [weightHeight']
  push_cast
  rfl

theorem v2rep_exists_hwv [CharZero K] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Z : Submodule K V)
    [FiniteDimensional K Z] (hZ : IsStableUnderOperators E Z) (hw : Z ≤ ⨆ ν, weightSp E ν) (hne : Z ≠ ⊥) :
    ∃ mu v, v ∈ Z ∧ IsHWV E mu v := by
  have hHZ : ∀ x ∈ Z, heightOperator' E x ∈ Z := by
    intro x hx
    simp only [heightOperator', LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Z.neg_mem (Z.sum_mem fun a _ => Z.smul_mem _ (hZ a a x hx))
  let HZ : Module.End K Z := (heightOperator' E).restrict hHZ
  let S : Set ℤ := {h | ∃ ν v, v ∈ Z ∧ v ≠ 0 ∧ v ∈ weightSp E ν ∧ weightHeight' ν = h}
  have hSeig : ∀ h ∈ S, HZ.HasEigenvalue (h : K) := by
    rintro h ⟨ν, v, hvZ, hv0, hvw, rfl⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvZ⟩) ?_
    rw [Module.End.hasEigenvector_iff]
    refine ⟨Module.End.mem_eigenspace_iff.mpr (Subtype.ext ?_), fun h0 => hv0 (congrArg Subtype.val h0)⟩
    exact v2rep_H_apply E ν v hvw
  have hSfin : S.Finite :=
    ((Module.End.finite_hasEigenvalue HZ).preimage (Int.cast_injective (α := K)).injOn).subset
      fun h hh => hSeig h hh
  obtain ⟨x, hxZ, hx0⟩ := (Submodule.ne_bot_iff Z).mp hne
  have hgr := v2rep_graded E Z (fun a x hx => hZ a a x hx) x hxZ (hw hxZ)
  obtain ⟨ν0, hν0⟩ : ∃ ν, weightSp E ν ⊓ Z ≠ ⊥ := by
    by_contra hc
    push_neg at hc
    simp [hc] at hgr
    exact hx0 hgr
  obtain ⟨v0, hv0m, hv00⟩ := (Submodule.ne_bot_iff _).mp hν0
  have hSne : S.Nonempty := ⟨_, ν0, v0, hv0m.2, hv00, hv0m.1, rfl⟩
  have hTne : hSfin.toFinset.Nonempty := (Set.Finite.toFinset_nonempty hSfin).mpr hSne
  obtain ⟨ν, v, hvZ, hv0, hvw, hht⟩ := (hSfin.mem_toFinset).mp (hSfin.toFinset.max'_mem hTne)
  refine ⟨ν, v, hvZ, hv0, hvw, fun a b hab => ?_⟩
  by_contra hne'
  have hmem : weightHeight' (ν + rootW a b) ∈ S :=
    ⟨ν + rootW a b, E a b v, hZ a b v hvZ, hne', v2rep_shift E hR a b ν v hvw, rfl⟩
  have h1 := hSfin.toFinset.le_max' _ ((hSfin.mem_toFinset).mpr hmem)
  have h2 := v2rep_ht_root ν a b hab
  omega

end Formalism.MainNotions.G.GLWeightTheory

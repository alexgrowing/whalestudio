import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.TameDecomp

theorem exists_frob_pow_mul_pow_mul_inertia : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ φ : Dec (F := F) A, IsFrob (F := F) A (normV v) (φ : G F Ω) → ∀ N : ℕ, 0 < N → ∀ g : Dec (F := F) A, ∃ a < N, ∃ t i : Dec (F := F) A, (i : G F Ω) ∈ Ine (F := F) A ∧ g = φ ^ a * t ^ N * i := by
  intro F Ω _ _ _ _ _ A v hA φ hφ N hN g
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  set I : Subgroup (Dec (F := F) A) := (Ine (F := F) A).subgroupOf (Dec (F := F) A) with hI
  have hIc : IsClosed (I : Set (Dec (F := F) A)) := (isClosed_Ine A).preimage continuous_subtype_val
  let P : Set (Dec (F := F) A) :=
    (fun x : Dec (F := F) A × Dec (F := F) A => x.1 ^ N * x.2) '' (Set.univ ×ˢ (I : Set _))
  have hP : IsCompact P := (isCompact_univ.prod hIc.isCompact).image (by fun_prop)
  let Wd : Set (Dec (F := F) A) := ⋃ a ∈ Finset.range N, (fun x => φ ^ a * x) '' P
  have hW : IsClosed Wd := by
    refine (Finset.isCompact_biUnion _ fun a _ => hP.image (by fun_prop)).isClosed
  have hsub : ((Subgroup.zpowers φ ⊔ I : Subgroup (Dec (F := F) A)) : Set (Dec (F := F) A)) ⊆ Wd := by
    intro x hx
    rw [Subgroup.mul_normal] at hx
    obtain ⟨h, hh, i, hi, rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hN' : (0 : ℤ) < N := by exact_mod_cast hN
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg m hN'.ne')
    have haN : a < N := by
      have := Int.emod_lt_of_pos m hN'
      omega
    have e : φ ^ m = φ ^ a * (φ ^ (m / (N : ℤ))) ^ N := by
      rw [← zpow_natCast (φ ^ (m / (N : ℤ))) N, ← zpow_mul, ← zpow_natCast φ a, ← zpow_add]
      congr 1
      have := Int.emod_add_mul_ediv m N
      rw [ha] at this
      rw [mul_comm (m / (N : ℤ))]
      omega
    refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 haN)) ?_
    exact ⟨_, ⟨(φ ^ (m / (N : ℤ)), i), ⟨Set.mem_univ _, hi⟩, rfl⟩, by
      simp only [e, mul_assoc]⟩
  have hg : g ∈ Wd := by
    have h1 := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hA φ hφ
    have h2 : g ∈ (Subgroup.zpowers φ ⊔ I).topologicalClosure := by rw [hI, h1]; trivial
    exact closure_minimal hsub hW h2
  simp only [Wd, Set.mem_iUnion] at hg
  obtain ⟨a, ha, y, ⟨⟨t, i⟩, ⟨-, hi⟩, rfl⟩, e⟩ := hg
  exact ⟨a, Finset.mem_range.1 ha, t, i, Subgroup.mem_subgroupOf.1 hi, by
    rw [← e, mul_assoc]⟩

end GlobalTheory.CompanionTheory.TameDecomp

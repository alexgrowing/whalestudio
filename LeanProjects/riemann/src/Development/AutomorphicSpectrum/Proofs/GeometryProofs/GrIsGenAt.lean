import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FlagGrGen

theorem exists_coord {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ} {b : Fin r → E}
    (hb : LinearIndependent Ω b) (i : Fin r) :
    ∃ φ : E →ₗ[Ω] Ω, φ (b i) = 1 ∧ ∀ k, k ≠ i → φ (b k) = 0 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hb).coord i)
  have key : ∀ k, g (b k) = Finsupp.single k (1 : Ω) i := by
    intro k
    have hk : (Module.Basis.span hb k : E) = b k := by rw [Module.Basis.span_apply]
    have := LinearMap.congr_fun hg (Module.Basis.span hb k)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply, Module.Basis.repr_self] at this
    rw [hk] at this
    exact this
  refine ⟨g, ?_, ?_⟩
  · rw [key]
    simp
  · intro k hk
    rw [key]
    simp [Ne.symm hk]

theorem gr_isGenAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (b₀ b : Fin r → E) (p : Cpt ξ) (i : Fin r) (t : Ω), LinearIndependent Ω b₀ → (∀ s, flagStep Ω b s = flagStep Ω b₀ s) → L.IsFrameAt b p → b i - t • b₀ i ∈ flagStep Ω b₀ i → (L.gr b₀ i).IsGenAt p t := by
  intro X Ω _ ξ E _ _ L r b₀ b p i t hb₀ hflag hframe hti
  obtain ⟨hb, hLp⟩ := hframe
  obtain ⟨f0, hf0⟩ := exists_coord hb₀ i
  obtain ⟨g, hg⟩ := exists_coord hb i
  have hflag_i : flagStep Ω b₀ (i : ℕ) = flagStep Ω b (i : ℕ) := (hflag (i : ℕ)).symm
  have hf0ker : ∀ v ∈ flagStep Ω b₀ (i : ℕ), f0 v = 0 := by
    intro v hv
    have hle : flagStep Ω b₀ (i : ℕ) ≤ LinearMap.ker f0 := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      have hki : k ≠ i := by
        rintro rfl
        simp at hk
      exact LinearMap.mem_ker.mpr (hf0.2 k hki)
    exact LinearMap.mem_ker.mp (hle hv)
  have hgker : ∀ v ∈ flagStep Ω b (i : ℕ), g v = 0 := by
    intro v hv
    have hle : flagStep Ω b (i : ℕ) ≤ LinearMap.ker g := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      have hki : k ≠ i := by
        rintro rfl
        simp at hk
      exact LinearMap.mem_ker.mpr (hg.2 k hki)
    exact LinearMap.mem_ker.mp (hle hv)
  have hf0bi : f0 (b i) = t := by
    have := hf0ker _ hti
    rw [map_sub, map_smul, hf0.1, smul_eq_mul, _root_.mul_one, sub_eq_zero] at this
    exact this
  have ht0 : t ≠ 0 := by
    rintro rfl
    have hbi : b i ∈ flagStep Ω b (i : ℕ) := by
      rw [← hflag_i]
      simpa using hti
    have := hgker _ hbi
    rw [hg.1] at this
    exact one_ne_zero this
  have hmono : flagStep Ω b (i : ℕ) ≤ flagStep Ω b ((i : ℕ) + 1) :=
    Submodule.span_mono (Set.image_mono (fun k hk => by
      simp only [Set.mem_setOf_eq] at hk ⊢
      omega))
  have hb0i : b₀ i ∈ flagStep Ω b ((i : ℕ) + 1) := by
    rw [hflag]
    exact Submodule.subset_span ⟨i, by simp, rfl⟩
  have hagree : ∀ v ∈ flagStep Ω b ((i : ℕ) + 1), f0 v = t * g v := by
    intro v hv
    have hle : flagStep Ω b ((i : ℕ) + 1) ≤ LinearMap.eqLocus f0 (t • g) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      have hk' : (k : ℕ) < (i : ℕ) + 1 := hk
      rw [SetLike.mem_coe, LinearMap.mem_eqLocus, LinearMap.smul_apply, smul_eq_mul]
      rcases lt_or_eq_of_le (by omega : (k : ℕ) ≤ (i : ℕ)) with hlt | heq
      · have hki : k ≠ i := by
          rintro rfl
          exact lt_irrefl _ hlt
        rw [hg.2 k hki, mul_zero]
        apply hf0ker
        rw [hflag_i]
        exact Submodule.subset_span ⟨k, hlt, rfl⟩
      · have hki : k = i := Fin.ext heq
        rw [hki, hg.1, _root_.mul_one, hf0bi]
    have := hle hv
    rw [LinearMap.mem_eqLocus, LinearMap.smul_apply, smul_eq_mul] at this
    exact this
  have hgO : ∀ v ∈ Submodule.span (regAt ξ p) (Set.range b), g v ∈ regAt ξ p := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      by_cases hki : k = i
      · rw [hki, hg.1]
        exact one_mem _
      · rw [hg.2 k hki]
        exact zero_mem _
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | smul a x _ hx =>
      show g ((a : Ω) • x) ∈ regAt ξ p
      rw [map_smul, smul_eq_mul]
      exact mul_mem a.2 hx
  have hbiL : b i ∈ L p := by
    rw [hLp]
    exact Submodule.subset_span ⟨i, rfl⟩
  show t ≠ 0 ∧ Submodule.span (regAt ξ p) {s | ∃ e ∈ L p, e - s • b₀ i ∈ flagStep Ω b₀ i} = Submodule.span (regAt ξ p) {t}
  refine ⟨ht0, ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro s ⟨e, he, hes⟩
    rw [hLp] at he
    have he_flag : e ∈ flagStep Ω b ((i : ℕ) + 1) := by
      have h1 : e - s • b₀ i ∈ flagStep Ω b ((i : ℕ) + 1) := hmono (by rw [← hflag_i]; exact hes)
      have h2 : s • b₀ i ∈ flagStep Ω b ((i : ℕ) + 1) := Submodule.smul_mem _ s hb0i
      simpa using add_mem h1 h2
    have hs : s = f0 e := by
      have := hf0ker _ hes
      rw [map_sub, map_smul, hf0.1, smul_eq_mul, _root_.mul_one, sub_eq_zero] at this
      exact this.symm
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨⟨g e, hgO e he⟩, ?_⟩
    show g e * t = s
    rw [hs, hagree e he_flag, _root_.mul_comm]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨b i, hbiL, hti⟩

end GlobalTheory.CompanionTheory.Ar.FlagGrGen

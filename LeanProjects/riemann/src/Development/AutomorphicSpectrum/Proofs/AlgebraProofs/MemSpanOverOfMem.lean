import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor

namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeBC

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E] [Module Ω E]

theorem smul_mem_spanOver (R : Subalgebra o Ω) (S : Set E) {a : Ω} (ha : a ∈ R) {e : E}
    (he : e ∈ spanOver R S) : a • e ∈ spanOver R S := by
  unfold spanOver at he ⊢
  induction he using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, y, hy, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * c, R.mul_mem ha hc, y, hy, by rw [mul_smul]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mem_spanOver_of_mem (R : Subalgebra o Ω) {S : Set E} {e : E} (he : e ∈ S) :
    e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨1, R.one_mem, e, he, (one_smul _ _).symm⟩

theorem frac_add (R : Subalgebra o Ω) {f a b : Ω} (hf : f ∈ R) (ha : ∃ n : ℕ, f ^ n * a ∈ R)
    (hb : ∃ n : ℕ, f ^ n * b ∈ R) : ∃ n : ℕ, f ^ n * (a + b) ∈ R := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨n + m, ?_⟩
  have : f ^ (n + m) * (a + b) = f ^ m * (f ^ n * a) + f ^ n * (f ^ m * b) := by ring
  rw [this]
  exact R.add_mem (R.mul_mem (R.pow_mem hf _) hn) (R.mul_mem (R.pow_mem hf _) hm)

theorem loc_add (R : Subalgebra o Ω) (L : AddSubgroup E) (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L)
    {f : Ω} (hf : f ∈ R) {x y : E} (hx : ∃ n : ℕ, f ^ n • x ∈ L) (hy : ∃ n : ℕ, f ^ n • y ∈ L) :
    ∃ n : ℕ, f ^ n • (x + y) ∈ L := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  refine ⟨n + m, ?_⟩
  have : f ^ (n + m) • (x + y) = f ^ m • (f ^ n • x) + f ^ n • (f ^ m • y) := by
    rw [smul_add, ← mul_smul, ← mul_smul, ← pow_add, ← pow_add, add_comm m n]
  rw [this]
  exact L.add_mem (hL _ (R.pow_mem hf _) _ hn) (hL _ (R.pow_mem hf _) _ hm)

theorem locFree_baseChange {o Ω Ω₁ : Type} [CommRing o] [Field Ω] [Field Ω₁] [Algebra o Ω]
    [Algebra o Ω₁] [Algebra Ω Ω₁] [IsScalarTower o Ω Ω₁] (R : Subalgebra o Ω)
    (R₁ : Subalgebra o Ω₁) (hR : ∀ a ∈ R, algebraMap Ω Ω₁ a ∈ R₁)
    {E E₁ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω₁ E₁] [Module Ω E₁]
    [IsScalarTower Ω Ω₁ E₁] (bc : E →ₗ[Ω] E₁) (hbc : IsBaseChange Ω₁ bc) (r : ℕ)
    (L : AddSubgroup E) (h : LocFree R r L) :
    LocFree R₁ r (spanOver R₁ (bc '' (L : Set E))) := by
  classical
  obtain ⟨hst, k, f, c, hf, hc, hsum, hloc⟩ := h
  have hst₁ : ∀ a ∈ R₁, ∀ e ∈ spanOver R₁ (bc '' (L : Set E)),
      a • e ∈ spanOver R₁ (bc '' (L : Set E)) := fun a ha e he => smul_mem_spanOver R₁ _ ha he
  refine ⟨hst₁, k, fun l => algebraMap Ω Ω₁ (f l), fun l => algebraMap Ω Ω₁ (c l),
    fun l => hR _ (hf l), fun l => hR _ (hc l), ?_, fun l => ?_⟩
  · simp only [← map_mul, ← map_sum, hsum, map_one]
  obtain ⟨b, hli, hsp, hb⟩ := hloc l
  beta_reduce
  set F : Ω₁ := algebraMap Ω Ω₁ (f l) with hF
  have hF₁ : F ∈ R₁ := hR _ (hf l)
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hsp.ge
  let B₁ : Module.Basis (Fin r) Ω₁ E₁ := IsBaseChange.basis B hbc
  have hB₁ : (fun q => bc (b q)) = B₁ := by
    funext q
    simp [B₁, B, IsBaseChange.basis_apply]
  have hB₁' : ∀ q, bc (b q) = B₁ q := fun q => congrFun hB₁ q
  refine ⟨B₁, B₁.linearIndependent, B₁.span_eq, fun e => ⟨?_, ?_⟩⟩
  · have key : ∀ x ∈ spanOver R₁ (bc '' (L : Set E)), ∃ a : Fin r → Ω₁,
        (∀ q, ∃ n : ℕ, F ^ n * a q ∈ R₁) ∧ x = ∑ q, a q • B₁ q := by
      intro x hx
      unfold spanOver at hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨t, ht, _, ⟨y, hy, rfl⟩, rfl⟩ := hx
        obtain ⟨a, ha, rfl⟩ := (hb y).1 ⟨0, by simpa using hy⟩
        refine ⟨fun q => t * algebraMap Ω Ω₁ (a q), fun q => ?_, ?_⟩
        · obtain ⟨n, hn⟩ := ha q
          refine ⟨n, ?_⟩
          have := R₁.mul_mem ht (hR _ hn)
          rw [map_mul, map_pow] at this
          convert this using 1
          rw [hF]; ring
        · simp only [map_sum, map_smul, Finset.smul_sum, hB₁', mul_smul, algebraMap_smul]
      | zero => exact ⟨0, fun q => ⟨0, by simp⟩, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨a', ha', rfl⟩ := hy
        exact ⟨a + a', fun q => frac_add R₁ hF₁ (ha q) (ha' q),
          by simp [add_smul, Finset.sum_add_distrib]⟩
      | neg x _ hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        refine ⟨-a, fun q => ?_, by simp⟩
        obtain ⟨n, hn⟩ := ha q
        exact ⟨n, by simpa using R₁.neg_mem hn⟩
    rintro ⟨n, hn⟩
    by_cases h0 : F = 0
    · exact ⟨B₁.repr e, fun q => ⟨1, by simp [h0]⟩, (B₁.sum_repr e).symm⟩
    obtain ⟨a, ha, hea⟩ := key _ hn
    have hFn : F ^ n ≠ 0 := pow_ne_zero _ h0
    refine ⟨fun q => (F ^ n)⁻¹ * a q, fun q => ?_, ?_⟩
    · obtain ⟨m, hm⟩ := ha q
      refine ⟨m + n, ?_⟩
      convert hm using 1
      rw [pow_add]; field_simp
    · simp only [mul_smul, ← Finset.smul_sum]
      rw [← hea, inv_smul_smul₀ hFn]
  · rintro ⟨a, ha, rfl⟩
    refine Finset.sum_induction _
      (fun x : E₁ => ∃ n : ℕ, F ^ n • x ∈ spanOver R₁ (bc '' (L : Set E)))
      (fun x y hx hy => loc_add R₁ _ hst₁ hF₁ hx hy) ⟨0, by simp⟩ (fun q _ => ?_)
    obtain ⟨m, hm⟩ := (hb (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by
      by_cases hq : q' = q
      · subst hq; simp
      · simp [hq]⟩, by simp [Pi.single_apply]⟩
    obtain ⟨n, hn⟩ := ha q
    refine ⟨n + m, ?_⟩
    have h1 : bc (f l ^ m • b q) ∈ spanOver R₁ (bc '' (L : Set E)) :=
      mem_spanOver_of_mem R₁ ⟨_, hm, rfl⟩
    have h2 := hst₁ _ hn _ h1
    rw [map_smul, hB₁', ← algebraMap_smul Ω₁ (f l ^ m), map_pow, ← hF, ← mul_smul] at h2
    rw [← mul_smul]
    convert h2 using 2
    ring

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeBC

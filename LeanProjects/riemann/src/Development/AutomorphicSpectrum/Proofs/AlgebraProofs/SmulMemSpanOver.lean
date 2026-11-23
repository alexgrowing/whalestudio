import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor

namespace GlobalTheory.CompanionTheory.Ar.Num.SpanExact

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω]
  {E E₂ : Type*} [AddCommGroup E] [Module Ω E] [AddCommGroup E₂] [Module Ω E₂]

theorem smul_mem_spanOver (R : Subalgebra o Ω) (S : Set E) {a : Ω} (ha : a ∈ R) {v : E}
    (hv : v ∈ spanOver R S) : a • v ∈ spanOver R S := by
  unfold spanOver at hv ⊢
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, e, he, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * b, R.mul_mem ha hb, e, he, by rw [mul_smul]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem map_spanOver (R : Subalgebra o Ω) (S : Set E) (q : E →ₗ[Ω] E₂) :
    (spanOver R S).map q.toAddMonoidHom = spanOver R (q '' S) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨v, ⟨a, ha, e, he, rfl⟩, rfl⟩
    exact ⟨a, ha, q e, ⟨e, he, rfl⟩, by simp⟩
  · rintro ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨a • e, ⟨a, ha, e, he, rfl⟩, by simp⟩

theorem local_step (R R₁ : Subalgebra o Ω) (hR : R ≤ R₁) (q : E →ₗ[Ω] E₂) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} (f : Ω) (hf : f ∈ R) (b : Fin r → E₂)
    (hb : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = ⊤)
    (hloc : ∀ e, (∃ n : ℕ, f ^ n • e ∈ L.map q.toAddMonoidHom) ↔
        ∃ a : Fin r → Ω, (∀ j, ∃ n : ℕ, f ^ n * a j ∈ R) ∧ e = ∑ j, a j • b j)
    {v : E} (hv : v ∈ spanOver R₁ (L : Set E)) (hq : q v = 0) :
    ∃ m : ℕ, f ^ m • v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := by
  classical
  have h1 : ∀ j, ∃ n : ℕ, ∃ s ∈ L, q s = f ^ n • b j := by
    intro j
    obtain ⟨n, s, hs, hs'⟩ := (hloc (b j)).2 ⟨Pi.single j 1, fun k => ⟨0, by
      by_cases h : k = j
      · subst h; simpa using R.one_mem
      · simpa [h] using R.zero_mem⟩, by simp [Pi.single_apply]⟩
    exact ⟨n, s, hs, hs'⟩
  choose n s hs hqs using h1
  set N := ∑ j, n j with hN
  have hle : ∀ j, n j ≤ N := fun j =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let t : Fin r → E := fun j => f ^ (N - n j) • s j
  have ht : ∀ j, t j ∈ L := fun j => hL _ (R.pow_mem hf _) _ (hs j)
  have hqt : ∀ j, q (t j) = f ^ N • b j := fun j => by
    simp only [t, map_smul, hqs, smul_smul, ← pow_add, Nat.sub_add_cancel (hle j)]
  let B : Module.Basis (Fin r) Ω E₂ := Module.Basis.mk hb hsp.ge
  let σ : E₂ →ₗ[Ω] E := B.constr Ω t
  have hσ : ∀ j, σ (b j) = t j := fun j => by
    have : b j = B j := by simp [B]
    rw [this]; simp [σ]
  set S := spanOver R₁ {e | e ∈ L ∧ q e = 0} with hS
  have hup : ∀ (w : E) (m k : ℕ), f ^ m • w ∈ S → f ^ (k + m) • w ∈ S := fun w m k h => by
    rw [pow_add, mul_smul]
    exact smul_mem_spanOver R₁ _ (R₁.pow_mem (hR hf) _) h
  have key : ∃ m : ℕ, f ^ m • (f ^ N • v - σ (q v)) ∈ S := by
    clear hq
    unfold spanOver at hv
    induction hv using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, e, he, rfl⟩ := hx
      obtain ⟨c, hc, hce⟩ := (hloc (q e)).1 ⟨0, e, he, by simp⟩
      choose p hp using hc
      set M := ∑ j, p j with hM
      have hle' : ∀ j, p j ≤ M := fun j =>
        Finset.single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have hp' : ∀ j, f ^ M * c j ∈ R := fun j => by
        rw [← Nat.sub_add_cancel (hle' j), pow_add, mul_assoc]
        exact R.mul_mem (R.pow_mem hf _) (hp j)
      refine ⟨M, AddSubgroup.subset_closure ⟨a, ha, f ^ M • (f ^ N • e - σ (q e)), ⟨?_, ?_⟩, ?_⟩⟩
      · rw [smul_sub]
        refine sub_mem (hL _ (R.pow_mem hf _) _ (hL _ (R.pow_mem hf _) _ he)) ?_
        rw [hce, map_sum, Finset.smul_sum]
        refine sum_mem fun j _ => ?_
        rw [map_smul, smul_smul, hσ]
        exact hL _ (hp' j) _ (ht j)
      · rw [map_smul, map_sub, map_smul, hce, map_sum, map_sum, Finset.smul_sum]
        simp only [map_smul, hσ, hqt]
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_zero, smul_zero]
        intro j _
        rw [smul_comm, sub_self]
      · simp only [map_smul]
        module
    | zero => exact ⟨0, by simpa using S.zero_mem⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, hm⟩ := hx
      obtain ⟨k, hk⟩ := hy
      refine ⟨k + m, ?_⟩
      have h2 := hup _ _ m hk
      rw [add_comm] at h2
      convert add_mem (hup _ _ k hm) h2 using 1
      simp only [map_add]
      module
    | neg x _ hx =>
      obtain ⟨m, hm⟩ := hx
      refine ⟨m, ?_⟩
      convert neg_mem hm using 1
      simp only [map_neg]
      module
  obtain ⟨m, hm⟩ := key
  refine ⟨m + N, ?_⟩
  simpa [hq, smul_smul, pow_add] using hm

theorem mem_spanOver_ker (R R₁ : Subalgebra o Ω) (hR : R ≤ R₁) (q : E →ₗ[Ω] E₂) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} (hF : LocFree R r (L.map q.toAddMonoidHom))
    {v : E} (hv : v ∈ spanOver R₁ (L : Set E)) (hq : q v = 0) :
    v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := by
  obtain ⟨-, k, f, c, hf, hc, hsum, hl⟩ := hF
  let J : Ideal R :=
    { carrier := {a | (a : Ω) • v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0}}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Subalgebra.coe_add, add_smul] at ha hb ⊢
        exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a b hb => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, MulMemClass.coe_mul, mul_smul] at hb ⊢
        exact smul_mem_spanOver R₁ _ (hR a.2) hb }
  have h1 : (1 : R) ∈ J.radical := by
    have : (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * ⟨f l, hf l⟩ := by
      apply Subtype.ext
      simp [hsum]
    rw [this]
    refine sum_mem fun l _ => Ideal.mul_mem_left _ _ ?_
    obtain ⟨b, hb, hsp, hloc⟩ := hl l
    obtain ⟨m, hm⟩ := local_step R R₁ hR q L hL (f l) (hf l) b hb hsp hloc hv hq
    exact ⟨m, hm⟩
  obtain ⟨m, hm⟩ := h1
  have : ((1 ^ m : R) : Ω) • v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := hm
  simpa using this

theorem span_comap_exact : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R R₁ : Subalgebra o Ω), R ≤ R₁ → ∀ {E E₁ E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] [AddCommGroup E₂] [Module Ω E₂] (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂), Function.Injective i → LinearMap.range i = LinearMap.ker q → ∀ (L : AddSubgroup E) (r₂ : ℕ), (∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) → LocFree R r₂ (L.map q.toAddMonoidHom) → (spanOver R₁ (L : Set E)).comap i.toAddMonoidHom = spanOver R₁ (L.comap i.toAddMonoidHom : Set E₁) ∧ (spanOver R₁ (L : Set E)).map q.toAddMonoidHom = spanOver R₁ (L.map q.toAddMonoidHom : Set E₂) := by
  intro o Ω _ _ _ R R₁ hR E E₁ E₂ _ _ _ _ _ _ i q hi hex L r₂ hL hF
  refine ⟨?_, ?_⟩
  · have himg : i '' (L.comap i.toAddMonoidHom : Set E₁) = {e | e ∈ L ∧ q e = 0} := by
      ext e
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx, by rw [← LinearMap.mem_ker, ← hex]; exact ⟨x, rfl⟩⟩
      · rintro ⟨he, hq⟩
        rw [← LinearMap.mem_ker, ← hex] at hq
        obtain ⟨x, rfl⟩ := hq
        exact ⟨x, he, rfl⟩
    have hmap := map_spanOver R₁ (L.comap i.toAddMonoidHom : Set E₁) i
    rw [himg] at hmap
    ext x
    constructor
    · intro hx
      have hq : q (i x) = 0 := by rw [← LinearMap.mem_ker, ← hex]; exact ⟨x, rfl⟩
      have := mem_spanOver_ker R R₁ hR q L hL hF (v := i x) hx hq
      rw [← hmap] at this
      obtain ⟨y, hy, hxy⟩ := this
      obtain rfl : y = x := hi hxy
      exact hy
    · intro hx
      have h1 : i x ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := by
        rw [← hmap]; exact ⟨x, hx, rfl⟩
      have h2 : spanOver R₁ {e | e ∈ L ∧ q e = 0} ≤ spanOver R₁ (L : Set E) :=
        AddSubgroup.closure_mono fun w ⟨a, ha, e, he, hw⟩ => ⟨a, ha, e, he.1, hw⟩
      exact h2 h1
  · rw [map_spanOver, AddSubgroup.coe_map]
    rfl

end GlobalTheory.CompanionTheory.Ar.Num.SpanExact

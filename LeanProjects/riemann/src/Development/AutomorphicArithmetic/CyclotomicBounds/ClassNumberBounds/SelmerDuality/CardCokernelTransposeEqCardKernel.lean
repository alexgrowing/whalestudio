import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Frobenius

namespace KStar.Selmer

open Matrix Module

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n]

private theorem exists_annihilator_of_maximal [Finite R] (p : Ideal R) (hp : p.IsMaximal) :
    ∃ a : R, a ≠ 0 ∧ ∀ x ∈ p, x * a = 0 := by
  have hfin : Finite (Ideal R) := Finite.of_injective _ SetLike.coe_injective
  obtain ⟨I, hI, hmin⟩ := (wellFounded_lt (α := Ideal R)).has_min
    {I : Ideal R | ∀ t : R, (∀ x ∈ I, t * x = 0) → t ∈ p}
    ⟨⊤, fun t ht => by
      have : t = 0 := by simpa using ht 1 trivial
      simp [this]⟩
  by_cases h : ∀ t : R, (∀ x ∈ p • I, t * x = 0) → t ∈ p
  · exfalso
    have hle : p • I ≤ I := Submodule.smul_le_right
    have heq : p • I = I := by
      by_contra hne
      exact hmin _ h (lt_of_le_of_ne hle hne)
    obtain ⟨e, he1, he⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul p I
      (IsNoetherian.noetherian I) heq.ge
    have hep : e ∈ p := hI e he
    have h1 : (1 : R) ∈ p := by simpa using p.sub_mem hep he1
    exact hp.ne_top ((Ideal.eq_top_iff_one p).2 h1)
  · push Not at h
    obtain ⟨t, ht, htp⟩ := h
    have h2 : ¬ ∀ x ∈ I, t * x = 0 := fun h => htp (hI t h)
    push Not at h2
    obtain ⟨b, hb, hb0⟩ := h2
    refine ⟨t * b, hb0, fun x hx => ?_⟩
    have := ht (x • b) (Submodule.smul_mem_smul hx hb)
    rw [← this, smul_eq_mul]
    ring

private theorem finite_module_dual_of_finite [Finite R] (M : Type*) [AddCommGroup M] [Module R M] [Finite M] :
    Finite (Module.Dual R M) :=
  Finite.of_injective (fun f : Module.Dual R M => (f : M → R)) DFunLike.coe_injective

private theorem card_dual_mul_quotient (hR : Module.Baer R R) {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) : Nat.card (Module.Dual R M) =
      Nat.card (Module.Dual R (M ⧸ N)) * Nat.card (Module.Dual R N) := by
  have hs : Function.Surjective N.dualRestrict := fun g =>
    hR.extension_property N.subtype N.injective_subtype g
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker N.dualRestrict),
    Nat.card_congr (N.dualRestrict.quotKerEquivOfSurjective hs).toEquiv,
    Submodule.dualRestrict_ker_eq_dualAnnihilator,
    Nat.card_congr N.dualQuotEquivDualAnnihilator.toEquiv]

private theorem card_le_card_dual_of_simple [Finite R] (M : Type*) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] : Nat.card M ≤ Nat.card (Module.Dual R M) := by
  obtain ⟨p, hp, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 ‹IsSimpleModule R M›
  rw [Nat.card_congr e.toEquiv, ← Nat.card_congr e.dualMap.toEquiv]
  obtain ⟨a, ha, hpa⟩ := exists_annihilator_of_maximal p hp
  have hle : p ≤ LinearMap.ker (LinearMap.toSpanSingleton R R a) := fun x hx => hpa x hx
  have hge : LinearMap.ker (LinearMap.toSpanSingleton R R a) ≤ p := by
    refine (hp.eq_of_le ?_ hle).ge
    intro h
    have : (1 : R) ∈ LinearMap.ker (LinearMap.toSpanSingleton R R a) := h ▸ trivial
    exact ha (by simpa using this)
  let ι : (R ⧸ p) →ₗ[R] R := Submodule.liftQ p (LinearMap.toSpanSingleton R R a) hle
  have hι : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hge
  have : Finite (R ⧸ p) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  have := finite_module_dual_of_finite (R := R) (R ⧸ p)
  refine Nat.card_le_card_of_injective
    (fun y : R ⧸ p => (ι ∘ₗ LinearMap.mulLeft R y : Module.Dual R (R ⧸ p))) ?_
  intro y z hyz
  simpa using hι (LinearMap.congr_fun hyz 1)

private theorem card_le_card_dual [Finite R] (hR : Module.Baer R R) (k : ℕ) :
    ∀ (M : Type*) [AddCommGroup M] [Module R M] [Finite M], Nat.card M = k →
      Nat.card M ≤ Nat.card (Module.Dual R M) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro M _ _ _ hk
    have := finite_module_dual_of_finite (R := R) M
    rcases subsingleton_or_nontrivial M with hM | hM
    · rw [Nat.card_unique]
      exact Nat.card_pos
    by_cases h : ∀ N : Submodule R M, N = ⊥ ∨ N = ⊤
    · have : IsSimpleModule R M := { eq_bot_or_eq_top := h }
      exact card_le_card_dual_of_simple M
    push Not at h
    obtain ⟨N, h0, h1⟩ := h
    have hq : Finite (M ⧸ N) := Finite.of_surjective _ N.mkQ_surjective
    have hN : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 h0
    have hQ : Nontrivial (M ⧸ N) := Submodule.Quotient.nontrivial_iff.2 h1
    have a1 : 1 < Nat.card N := Finite.one_lt_card
    have a2 : 1 < Nat.card (M ⧸ N) := Finite.one_lt_card
    have hc := Submodule.card_eq_card_quotient_mul_card N
    have b1 := ih (Nat.card N) (by rw [← hk, hc]; nlinarith) N rfl
    have b2 := ih (Nat.card (M ⧸ N)) (by rw [← hk, hc]; nlinarith) (M ⧸ N) rfl
    rw [card_dual_mul_quotient hR N, hc, mul_comm]
    exact Nat.mul_le_mul b2 b1

theorem card_dual_of_baer [Finite R] (hR : Module.Baer R R) (M : Type*) [AddCommGroup M]
    [Module R M] [Finite M] : Nat.card (Module.Dual R M) = Nat.card M := by
  classical
  refine le_antisymm ?_ (card_le_card_dual hR _ M rfl)
  have := Fintype.ofFinite M
  let g : (M → R) →ₗ[R] M := Fintype.linearCombination R id
  have hg : Function.Surjective g := fun x => ⟨Pi.single x 1, by simp [g]⟩
  have e := g.quotKerEquivOfSurjective hg
  have h1 := card_dual_mul_quotient hR (LinearMap.ker g)
  rw [← Nat.card_congr (dotProductEquiv R M).toEquiv,
    Submodule.card_eq_card_quotient_mul_card (LinearMap.ker g), Nat.card_congr e.toEquiv,
    ← Nat.card_congr e.dualMap.toEquiv, mul_comm] at h1
  have h2 := card_le_card_dual hR _ (LinearMap.ker g) rfl
  have h3 : 0 < Nat.card (LinearMap.ker g) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ h3
  rw [h1]
  exact Nat.mul_le_mul_left _ h2

end KStar.Selmer

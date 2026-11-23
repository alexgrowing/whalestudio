import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

def NormalCpt (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Prop :=
  ∀ (p : Cpt ξ) (a : Ω), IsIntegral (regAt ξ p) a → a ∈ regAt ξ p

def zeroSet (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ϖ : Ω) : Set X :=
  {q | ∃ h : genPt ξ ⤳ q, ¬ unitAt ξ ⟨q, h⟩ ϖ}

def TrivMod (L : Lat ξ E) (ϖ : Ω) : Prop :=
  ∃ t : Cpt ξ → E, ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ U : X.Opens, p.1 ∈ U ∧
    ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q ϖ →
      t p ≠ 0 ∧ L q = Submodule.span (regAt ξ q) {t p} ∧ ∃ y ∈ L q, t p - t q = ϖ • y

def TrivRed (L : Lat ξ E) (ϖ : Ω) : Prop :=
  ∃ t : Cpt ξ → E, ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ U : X.Opens, p.1 ∈ U ∧
    ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q ϖ →
      t p ≠ 0 ∧ L q = Submodule.span (regAt ξ q) {t p} ∧
        ∃ c ∈ regAt ξ q, ¬ unitAt ξ q c ∧ t p - t q = c • t p

def OrderAt (L : Lat ξ E) (σ : E) (ϖ : Ω) (M : ℕ) (a : ℤ) (p : Cpt ξ) : Prop :=
  ∃ (e : E) (c : Ω), e ≠ 0 ∧ L p = Submodule.span (regAt ξ p) {e} ∧ σ = c • e ∧ unitAt ξ p (c ^ M / ϖ ^ a)

namespace ZUnit

variable {p : Cpt ξ} {a b : Ω}

theorem one : unitAt ξ p 1 := ⟨one_ne_zero, one_mem _, by simp⟩

theorem mul (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem inv (ha : unitAt ξ p a) : unitAt ξ p a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

theorem pow (ha : unitAt ξ p a) (n : ℕ) : unitAt ξ p (a ^ n) :=
  ⟨pow_ne_zero n ha.1, pow_mem ha.2.1 n, by rw [← inv_pow]; exact pow_mem ha.2.2 n⟩

theorem of_mul (ha : a ∈ regAt ξ p) (hb : b ∈ regAt ξ p) (h : unitAt ξ p (a * b)) : unitAt ξ p a := by
  have ha0 := left_ne_zero_of_mul h.1
  have hb0 := right_ne_zero_of_mul h.1
  refine ⟨ha0, ha, ?_⟩
  have : a⁻¹ = b * (a * b)⁻¹ := by field_simp
  rw [this]
  exact mul_mem hb h.2.2

theorem of_pow (ha : a ∈ regAt ξ p) {n : ℕ} (hn : n ≠ 0) (h : unitAt ξ p (a ^ n)) : unitAt ξ p a := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact of_mul ha (pow_mem ha m) (by rwa [← pow_succ'])

theorem mem_of_pow_mem (hN : NormalCpt ξ) {n : ℕ} (hn : n ≠ 0) (h : a ^ n ∈ regAt ξ p) : a ∈ regAt ξ p :=
  hN p a (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (isIntegral_algebraMap (x := (⟨a ^ n, h⟩ : regAt ξ p))))

theorem of_pow_of_normal (hN : NormalCpt ξ) {n : ℕ} (hn : n ≠ 0) (h : unitAt ξ p (a ^ n)) : unitAt ξ p a :=
  of_pow (mem_of_pow_mem hN hn h.2.1) hn h

theorem exists_of_span_eq {e e' : E} (he : e ≠ 0)
    (h : Submodule.span (regAt ξ p) {e} = Submodule.span (regAt ξ p) {e'}) :
    ∃ u : Ω, unitAt ξ p u ∧ e = u • e' := by
  have h1 : e ∈ Submodule.span (regAt ξ p) {e'} := by
    rw [← h]; exact Submodule.mem_span_singleton_self _
  have h2 : e' ∈ Submodule.span (regAt ξ p) {e} := by
    rw [h]; exact Submodule.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 h2
  replace hu : (u : Ω) • e' = e := hu
  replace hv : (v : Ω) • e = e' := hv
  have huv : (u : Ω) * v = 1 := by
    apply smul_left_injective Ω he
    simp only [mul_smul, hv, hu, one_smul]
  exact ⟨u, of_mul u.2 v.2 (by rw [huv]; exact one), hu.symm⟩

end ZUnit

theorem coe_mem_zeroSet {ϖ : Ω} (p : Cpt ξ) : p.1 ∈ zeroSet ξ ϖ ↔ ¬ unitAt ξ p ϖ :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨p.2, h⟩⟩

theorem TrivMod.of_mul {L : Lat ξ E} {ϖ a : Ω} (hϖ : ∀ p, ϖ ∈ regAt ξ p) (ha : ∀ p, a ∈ regAt ξ p)
    (h : TrivMod L (ϖ * a)) : TrivMod L ϖ := by
  have key : ∀ p, ¬ unitAt ξ p ϖ → ¬ unitAt ξ p (ϖ * a) := fun p hp hu => hp (ZUnit.of_mul (hϖ p) (ha p) hu)
  obtain ⟨t, ht⟩ := h
  refine ⟨t, fun p hp => ?_⟩
  obtain ⟨U, hU, h⟩ := ht p (key p hp)
  refine ⟨U, hU, fun q hq hq' => ?_⟩
  obtain ⟨h0, h1, y, hy, e⟩ := h q hq (key q hq')
  exact ⟨h0, h1, a • y, (L q).smul_mem (⟨a, ha q⟩ : regAt ξ q) hy, by rw [e, mul_smul]⟩

theorem TrivRed.mono {L : Lat ξ E} {ϖ ϖ' : Ω} (h : TrivRed L ϖ) (hs : zeroSet ξ ϖ' ⊆ zeroSet ξ ϖ) :
    TrivRed L ϖ' := by
  have key : ∀ p, ¬ unitAt ξ p ϖ' → ¬ unitAt ξ p ϖ := fun p hp =>
    (coe_mem_zeroSet p).1 (hs ((coe_mem_zeroSet p).2 hp))
  obtain ⟨t, ht⟩ := h
  refine ⟨t, fun p hp => ?_⟩
  obtain ⟨U, hU, H⟩ := ht p (key p hp)
  exact ⟨U, hU, fun q hq hq' => H q hq (key q hq')⟩

section Order

variable {L : Lat ξ E} {σ : E} {ϖ : Ω} {M M' : ℕ} {a a' : ℤ} {p : Cpt ξ}

theorem OrderAt.unitAt (h : OrderAt L σ ϖ M a p) {e : E} {c : Ω} (hL : L p = Submodule.span (regAt ξ p) {e})
    (hσ : σ = c • e) : unitAt ξ p (c ^ M / ϖ ^ a) := by
  obtain ⟨e₀, c₀, he₀, hL₀, hσ₀, h⟩ := h
  obtain ⟨u, hu, e'⟩ := ZUnit.exists_of_span_eq he₀ (hL₀.symm.trans hL)
  have he : e ≠ 0 := by rintro rfl; exact he₀ (by rw [e', smul_zero])
  have hc : c = c₀ * u := by
    apply smul_left_injective Ω he
    simp only [mul_smul, ← e', ← hσ, ← hσ₀]
  have : c ^ M / ϖ ^ a = c₀ ^ M / ϖ ^ a * u ^ M := by rw [hc, mul_pow]; ring
  rw [this]
  exact ZUnit.mul h (ZUnit.pow hu M)

theorem orderAt_iff_of_gen {e : E} {c : Ω} (he : e ≠ 0) (hL : L p = Submodule.span (regAt ξ p) {e})
    (hσ : σ = c • e) : OrderAt L σ ϖ M a p ↔ unitAt ξ p (c ^ M / ϖ ^ a) :=
  ⟨fun h => h.unitAt hL hσ, fun h => ⟨e, c, he, hL, hσ, h⟩⟩

theorem orderAt_iff_div {Λ : Lat ξ Ω} {s e : Ω} (he : e ≠ 0) (hΛ : Λ p = Submodule.span (regAt ξ p) {e}) :
    OrderAt Λ s ϖ M a p ↔ unitAt ξ p ((s / e) ^ M / ϖ ^ a) :=
  orderAt_iff_of_gen he hΛ (by rw [smul_eq_mul, div_mul_cancel₀ _ he])

theorem exists_gen_of_isVB_one {V : Submodule Ω E} (hL : L.IsVB 1 V) (p : Cpt ξ) :
    ∃ e : E, e ≠ 0 ∧ L p = Submodule.span (regAt ξ p) {e} ∧ V = Submodule.span Ω {e} := by
  obtain ⟨U, hU, b, hb, h⟩ := hL p trivial
  obtain ⟨h1, h2⟩ := h p trivial hU
  have hr : Set.range b = {b 0} := by
    ext x
    simp [Fin.exists_fin_one, eq_comm]
  exact ⟨b 0, h1.ne_zero 0, by rw [h2, hr], by rw [← hb, hr]⟩

theorem OrderAt.ne_zero (h : OrderAt L σ ϖ M a p) (hM : M ≠ 0) : σ ≠ 0 := by
  obtain ⟨e, c, he, -, rfl, h⟩ := h
  refine smul_ne_zero ?_ he
  rintro rfl
  exact h.1 (by rw [zero_pow hM, zero_div])

theorem orderAt_one_zero : OrderAt L σ ϖ 1 0 p ↔ σ ≠ 0 ∧ L p = Submodule.span (regAt ξ p) {σ} := by
  refine ⟨fun h => ⟨h.ne_zero one_ne_zero, ?_⟩, fun ⟨h0, h⟩ => ⟨σ, 1, h0, h, (one_smul _ _).symm, by
    simpa using ZUnit.one⟩⟩
  obtain ⟨e, c, -, hL, rfl, h⟩ := h
  rw [pow_one, zpow_zero, div_one] at h
  rw [hL]
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · exact ⟨⟨c⁻¹, h.2.2⟩, by
      change c⁻¹ • c • e = e
      rw [inv_smul_smul₀ h.1]⟩
  · exact ⟨⟨c, h.2.1⟩, rfl⟩

theorem OrderAt.mul_nat (h : OrderAt L σ ϖ M a p) (k : ℕ) : OrderAt L σ ϖ (M * k) (a * k) p := by
  obtain ⟨e, c, he, hL, hσ, h⟩ := h
  refine ⟨e, c, he, hL, hσ, ?_⟩
  rw [pow_mul, zpow_mul, zpow_natCast, ← div_pow]
  exact ZUnit.pow h k

theorem OrderAt.unique (h0 : ϖ ≠ 0) (hϖ : ϖ ∈ regAt ξ p) (hp : ¬ Ar.unitAt ξ p ϖ) (ha : OrderAt L σ ϖ M a p)
    (ha' : OrderAt L σ ϖ M a' p) : a = a' := by
  obtain ⟨e, c, he, hL, hσ, ha⟩ := ha
  replace ha' := ha'.unitAt hL hσ
  have key : ∀ a b : ℤ, Ar.unitAt ξ p (c ^ M / ϖ ^ a) → Ar.unitAt ξ p (c ^ M / ϖ ^ b) → ¬ a < b := by
    intro a b ha hb hlt
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + ((n + 1 : ℕ) : ℤ) := ⟨(b - a - 1).toNat, by omega⟩
    have hc : c ^ M ≠ 0 := fun h => ha.1 (by rw [h, zero_div])
    have hu := ZUnit.mul ha (ZUnit.inv hb)
    have : c ^ M / ϖ ^ a * (c ^ M / ϖ ^ (a + ((n + 1 : ℕ) : ℤ)))⁻¹ = ϖ ^ (n + 1) := by
      have : ϖ ^ a ≠ 0 := zpow_ne_zero a h0
      rw [zpow_add₀ h0, zpow_natCast]
      field_simp
    rw [this] at hu
    exact hp (ZUnit.of_pow hϖ n.succ_ne_zero hu)
  exact le_antisymm (not_lt.1 (key a' a ha' ha)) (not_lt.1 (key a a' ha ha'))

theorem OrderAt.ratio_unique (h0 : ϖ ≠ 0) (hϖ : ϖ ∈ regAt ξ p) (hp : ¬ Ar.unitAt ξ p ϖ)
    (ha : OrderAt L σ ϖ M a p) (ha' : OrderAt L σ ϖ M' a' p) : a * M' = a' * M :=
  OrderAt.unique h0 hϖ hp (ha.mul_nat M') (by rw [mul_comm M M']; exact ha'.mul_nat M)

end Order

example {e : E} (he : e ≠ 0) {ϖ : Ω} (h0 : ϖ ≠ 0) (n : ℤ) (p : Cpt ξ) :
    OrderAt (fun p => Submodule.span (regAt ξ p) {e} : Lat ξ E) (ϖ ^ n • e) ϖ 1 n p :=
  ⟨e, ϖ ^ n, he, rfl, rfl, by rw [pow_one, div_self (zpow_ne_zero n h0)]; exact ZUnit.one⟩

example {e : E} (he : e ≠ 0) {ϖ : Ω} (h0 : ϖ ≠ 0) (p : Cpt ξ) :
    OrderAt (fun p => Submodule.span (regAt ξ p) {e} : Lat ξ E) (ϖ ^ 3 • e) (ϖ ^ 2) 2 3 p :=
  ⟨e, ϖ ^ 3, he, rfl, rfl, by
    rw [show (ϖ ^ 3) ^ 2 / (ϖ ^ 2) ^ (3 : ℤ) = 1 by rw [zpow_ofNat]; field_simp]; exact ZUnit.one⟩

example (σ : E) (ϖ : Ω) (M : ℕ) (a : ℤ) (p : Cpt ξ) : ¬ OrderAt (fun _ => ⊥ : Lat ξ E) σ ϖ M a p :=
  fun ⟨_, _, he, h, _⟩ => he (Submodule.span_singleton_eq_bot.1 h.symm)

example (ϖ : Ω) (M : ℕ) (a : ℤ) (p : Cpt ξ) :
    ¬ OrderAt (fun p => Submodule.span (regAt ξ p) {((1 : Ω), (0 : Ω))} : Lat ξ (Ω × Ω)) (0, 1) ϖ M a p := by
  rintro ⟨e, c, he, h, hσ, -⟩
  obtain ⟨u, -, rfl⟩ := ZUnit.exists_of_span_eq he h.symm
  simpa using congrArg Prod.snd hσ

example {ϖ : Ω} {p : Cpt ξ} (hp : ¬ unitAt ξ p ϖ) : ¬ TrivRed (fun _ => ⊥ : Lat ξ E) ϖ := by
  rintro ⟨t, ht⟩
  obtain ⟨U, hU, h⟩ := ht p hp
  obtain ⟨h0, h1, -⟩ := h p hU hp
  exact h0 (Submodule.span_singleton_eq_bot.1 h1.symm)

example : zeroSet ξ 1 = ∅ ∧ zeroSet ξ 0 = {q | genPt ξ ⤳ q} :=
  ⟨Set.eq_empty_of_forall_notMem fun _ ⟨_, h⟩ => h ZUnit.one,
    Set.ext fun _ => ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, fun hu => hu.1 rfl⟩⟩⟩

end GlobalTheory.CompanionTheory.Ar.Flat

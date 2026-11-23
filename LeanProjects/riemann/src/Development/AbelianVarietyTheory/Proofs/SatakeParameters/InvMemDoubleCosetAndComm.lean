import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.StatementF
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsTail

open Formalism.UG Matrix

noncomputable section

namespace GlobalTheory.UnitarySwap

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_int (x : L) : x ∈ intL L ↔ Valued.v x ≤ 1 := Iff.rfl

theorem inv_one_sub_mem {x : L} (hx : Valued.v x < 1) : (1 - x) ≠ 0 ∧ (1 - x)⁻¹ ∈ intL L := by
  have h : Valued.v (1 - x) = 1 := Valuation.map_one_sub_of_lt _ hx
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, map_zero] at h; exact zero_ne_one h
  · rw [mem_int, map_inv₀, h, inv_one]

theorem mul_lt_one {x y : L} (hx : Valued.v x < 1) (hy : y ∈ intL L) : Valued.v (x * y) < 1 := by
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' hy) hx

section Abstract

variable {V : Type} [AddCommGroup V] [Module L V] {σ : L →+* L}

def SelfDual (B : V →ₛₗ[σ] V →ₗ[L] L) (W : Submodule L V) (Λ : Set V) : Prop :=
  ∀ v, v ∈ Λ ↔ v ∈ W ∧ ∀ w ∈ Λ, B v w ∈ intL L

variable {B : V →ₛₗ[σ] V →ₗ[L] L} {W : Submodule L V} {Λ : Set V}

theorem SelfDual.add (h : SelfDual B W Λ) {u v : V} (hu : u ∈ Λ) (hv : v ∈ Λ) : u + v ∈ Λ := by
  rw [h] at hu hv ⊢
  refine ⟨W.add_mem hu.1 hv.1, fun w hw => ?_⟩
  rw [map_add, LinearMap.add_apply]
  exact add_mem (hu.2 w hw) (hv.2 w hw)

theorem SelfDual.smul (h : SelfDual B W Λ) (hσ : ∀ x ∈ intL L, σ x ∈ intL L) {c : L} (hc : c ∈ intL L)
    {v : V} (hv : v ∈ Λ) : c • v ∈ Λ := by
  rw [h] at hv ⊢
  refine ⟨W.smul_mem c hv.1, fun w hw => ?_⟩
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  exact mul_mem (hσ c hc) (hv.2 w hw)

theorem SelfDual.pair (h : SelfDual B W Λ) {u v : V} (hu : u ∈ Λ) (hv : v ∈ Λ) : B u v ∈ intL L :=
  ((h u).1 hu).2 v hv

theorem SelfDual.decomp (h : SelfDual B W Λ) (hσ : ∀ x ∈ intL L, σ x ∈ intL L)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) (hxy : B x y = 1) (hyx : B y x = 1)
    (hs : Valued.v (B x x * B y y) < 1) {v : V} (hv : v ∈ Λ) :
    ∃ c ∈ intL L, ∃ d ∈ intL L, ∃ v₀ ∈ Λ, B x v₀ = 0 ∧ B y v₀ = 0 ∧ v = c • x + d • y + v₀ := by
  obtain ⟨h0, hi⟩ := inv_one_sub_mem hs
  have hc : (B y v - B y y * B x v) * (1 - B x x * B y y)⁻¹ ∈ intL L :=
    mul_mem (sub_mem (h.pair hy hv) (mul_mem (h.pair hy hy) (h.pair hx hv))) hi
  have hd : (B x v - B x x * B y v) * (1 - B x x * B y y)⁻¹ ∈ intL L :=
    mul_mem (sub_mem (h.pair hx hv) (mul_mem (h.pair hx hx) (h.pair hy hv))) hi
  refine ⟨_, hc, _, hd, v + ((-((B y v - B y y * B x v) * (1 - B x x * B y y)⁻¹)) • x +
    (-((B x v - B x x * B y v) * (1 - B x x * B y y)⁻¹)) • y),
    h.add hv (h.add (h.smul hσ (neg_mem hc) hx) (h.smul hσ (neg_mem hd) hy)), ?_, ?_, ?_⟩
  · simp only [map_add, map_smul, smul_eq_mul, hxy]
    linear_combination (-(B x v)) * mul_inv_cancel₀ h0
  · simp only [map_add, map_smul, smul_eq_mul, hyx]
    linear_combination (-(B y v)) * mul_inv_cancel₀ h0
  · module

def perp (B : V →ₛₗ[σ] V →ₗ[L] L) (W : Submodule L V) (e f : V) : Submodule L V :=
  W ⊓ (LinearMap.ker (B e) ⊓ LinearMap.ker (B f))

theorem mem_perp {e f v : V} : v ∈ perp B W e f ↔ v ∈ W ∧ B e v = 0 ∧ B f v = 0 := by
  simp [perp]

theorem SelfDual.inter (h : SelfDual B W Λ) (hB : ∀ u v, σ (B u v) = B v u) {e f x y : V}
    (hx : ∀ v, B e v = 0 → B x v = 0) (hy : ∀ v, B f v = 0 → B y v = 0)
    (hdec : ∀ v ∈ Λ, ∃ c ∈ intL L, ∃ d ∈ intL L, ∃ v₀ ∈ Λ,
      B e v₀ = 0 ∧ B f v₀ = 0 ∧ v = c • x + d • y + v₀) :
    SelfDual B (perp B W e f) (Λ ∩ (perp B W e f : Set V)) := by
  intro v
  constructor
  · rintro ⟨hv, hv'⟩
    exact ⟨hv', fun w hw => h.pair hv hw.1⟩
  · rintro ⟨hv, hv'⟩
    refine ⟨(h v).2 ⟨(mem_perp.1 hv).1, fun w hw => ?_⟩, hv⟩
    obtain ⟨c, -, d, -, w₀, hw₀, h1, h2, rfl⟩ := hdec w hw
    have e1 : B v x = 0 := by rw [← hB, hx v (mem_perp.1 hv).2.1, map_zero]
    have e2 : B v y = 0 := by rw [← hB, hy v (mem_perp.1 hv).2.2, map_zero]
    simp only [map_add, map_smul, e1, e2, smul_zero, zero_add]
    exact hv' w₀ ⟨hw₀, mem_perp.2 ⟨((h w₀).1 hw₀).1, h1, h2⟩⟩

def refl (B : V →ₛₗ[σ] V →ₗ[L] L) (w : V) (μ : L) : V →ₗ[L] V :=
  LinearMap.id - μ⁻¹ • (B w).smulRight w

theorem refl_apply (w : V) (μ : L) (v : V) : refl B w μ v = v - (μ⁻¹ * B w v) • w := by
  simp [refl, mul_smul]

theorem refl_isom (hB : ∀ u v, σ (B u v) = B v u) (w : V) (μ : L) (hμ : μ ≠ 0)
    (hw : B w w = μ + σ μ) (u v : V) : B (refl B w μ u) (refl B w μ v) = B u v := by
  have hμ' : σ μ ≠ 0 := (map_ne_zero σ).2 hμ
  simp only [refl_apply, map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, map_mul, map_inv₀, hB, hw, RingHom.id_apply]
  field_simp
  ring

theorem exists_refl (hB : ∀ u v, σ (B u v) = B v u) {τ : L} (hτ : τ ∈ intL L)
    (hτ1 : τ + σ τ = 1) {π : L} (hπ0 : π ≠ 0) (hπ : Valued.v π < 1) (hσπ : σ π = π) {e f : V}
    (hef : B e f = π⁻¹) (he : B e e ∈ intL L) (hf : B f f ∈ intL L) :
    ∃ s : V →ₗ[L] V, (∀ u v, B (s u) (s v) = B u v) ∧ (∀ v, B e v = 0 → B f v = 0 → s v = v) ∧
      ∃ r ∈ intL L, ∃ r' ∈ intL L,
        s e = (-r) • (π • e) + (1 + π * r) • f ∧ s f = (1 + π * r') • e + (-r') • (π • f) := by
  have hfe : B f e = π⁻¹ := by rw [← hB, hef, map_inv₀, hσπ]
  have ht : τ * (B e e + B f f) ∈ intL L := mul_mem hτ (add_mem he hf)
  obtain ⟨h0, hi⟩ := inv_one_sub_mem (mul_lt_one hπ ht)
  set t := τ * (B e e + B f f) with htdef
  have hfix : ∀ v, B e v = 0 → B f v = 0 → refl B (e - f) (-(π⁻¹ * (1 - π * t))) v = v := by
    intro v h1 h2
    rw [refl_apply]
    simp [h1, h2]
  refine ⟨refl B (e - f) (-(π⁻¹ * (1 - π * t))), refl_isom hB _ _ ?_ ?_, hfix,
    (t - B e e) * (1 - π * t)⁻¹, mul_mem (sub_mem ht he) hi,
    (t - B f f) * (1 - π * t)⁻¹, mul_mem (sub_mem ht hf) hi, ?_, ?_⟩
  · exact neg_ne_zero.2 (mul_ne_zero (inv_ne_zero hπ0) h0)
  · have : σ τ = 1 - τ := by rw [← hτ1]; ring
    simp only [htdef, map_sub, LinearMap.sub_apply, hef, hfe, map_neg, map_mul, map_inv₀, hσπ, map_one,
      map_add, hB, this]
    field_simp
    ring
  · rw [refl_apply]
    simp only [map_sub, LinearMap.sub_apply, hfe]
    match_scalars <;> field_simp <;> ring
  · rw [refl_apply]
    simp only [map_sub, LinearMap.sub_apply, hef]
    match_scalars <;> field_simp <;> ring

theorem exists_swap [FiniteDimensional L V] (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (hB : ∀ u v, σ (B u v) = B v u) {τ : L} (hτ : τ ∈ intL L) (hτ1 : τ + σ τ = 1) {ϖ : L}
    (hσϖ : σ ϖ = ϖ) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (m : ℕ) :
    ∀ (W : Submodule L V), Module.finrank L W < m → ∀ Λ Λ' : Set V, SelfDual B W Λ → SelfDual B W Λ' →
      (∃ N : ℕ, ∀ v ∈ Λ', ϖ ^ N • v ∈ Λ) →
      ∃ s : V →ₗ[L] V, (∀ u v, B (s u) (s v) = B u v) ∧ (∀ u, (∀ w ∈ W, B w u = 0) → s u = u) ∧
        (∀ v ∈ Λ, s v ∈ Λ') ∧ (∀ v ∈ Λ', s v ∈ Λ) := by
  classical
  have hσO : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => by rw [mem_int, hσ]; exact hx
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hϖ1 : Valued.v ϖ < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  induction m with
  | zero => intro W hW; omega
  | succ m ih =>
  intro W hW Λ Λ' hΛ hΛ' hN
  have hback : ∀ N : ℕ, (∀ v ∈ Λ', ϖ ^ N • v ∈ Λ) → ∀ v ∈ Λ, ϖ ^ N • v ∈ Λ' := by
    intro N h v hv
    refine (hΛ' _).2 ⟨W.smul_mem _ ((hΛ v).1 hv).1, fun w hw => ?_⟩
    have := hΛ.pair hv (h w hw)
    simpa [map_smulₛₗ, hσϖ] using this
  have ha := Nat.find_spec hN
  rcases h0 : Nat.find hN with _ | b
  · rw [h0] at ha
    refine ⟨LinearMap.id, fun _ _ => rfl, fun _ _ => rfl, fun v hv => ?_, fun v hv => ?_⟩
    · simpa using hback 0 ha v hv
    · simpa using ha v hv
  have hb : ¬ ∀ v ∈ Λ', ϖ ^ b • v ∈ Λ := Nat.find_min hN (by omega)
  rw [h0] at ha
  push Not at hb
  obtain ⟨e, he, hne⟩ := hb
  have heW : e ∈ W := ((hΛ' e).1 he).1
  rw [hΛ] at hne
  push Not at hne
  obtain ⟨y, hy, hy'⟩ := hne (W.smul_mem _ heW)
  set π := ϖ ^ (b + 1) with hπdef
  have hπ0 : π ≠ 0 := pow_ne_zero _ hϖ0
  have hσπ : σ π = π := by rw [hπdef, map_pow, hσϖ]
  have hπ1 : Valued.v π < 1 := by
    rw [hπdef, map_pow]; exact pow_lt_one₀ zero_le hϖ1 (by omega)
  have hπO : π ∈ intL L := hπ1.le
  have hπe : π • e ∈ Λ := ha e he
  have hunit : Valued.v (π * B e y) = 1 := by
    have h1 : Valued.v (π * B e y) ≤ 1 := by
      have := hΛ.pair hπe hy
      simpa [map_smulₛₗ, hσπ, mem_int] using this
    refine le_antisymm h1 ?_
    have h2 : 1 < Valued.v (ϖ ^ b * B e y) := by
      rw [mem_int, not_le] at hy'
      simpa [map_smulₛₗ, hσϖ] using hy'
    have h3 : π * B e y = ϖ * (ϖ ^ b * B e y) := by rw [hπdef]; ring
    rw [h3, map_mul, hϖ]
    have h4 : Valued.v (ϖ ^ b * B e y) ≠ 0 := (lt_trans zero_lt_one h2).ne'
    rw [← WithZero.exp_log h4, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
    rw [← WithZero.exp_log h4, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hu0 : π * B e y ≠ 0 := by
    intro h; rw [h, map_zero] at hunit; exact zero_ne_one hunit
  have hey : B e y ≠ 0 := right_ne_zero_of_mul hu0
  obtain ⟨f, hf, hef⟩ : ∃ f ∈ Λ, B e f = π⁻¹ := by
    refine ⟨(π * B e y)⁻¹ • y, hΛ.smul hσO (by rw [mem_int, map_inv₀, hunit, inv_one]) hy, ?_⟩
    rw [map_smul, smul_eq_mul]; field_simp
  have hfe : B f e = π⁻¹ := by rw [← hB, hef, map_inv₀, hσπ]
  have hfW : f ∈ W := ((hΛ f).1 hf).1
  have hπf : π • f ∈ Λ' := hback _ ha f hf
  have hee := hΛ'.pair he he
  have hff := hΛ.pair hf hf
  have hsm : ∀ x v, B (π • x) v = π * B x v := by
    intro x v; simp [map_smulₛₗ, hσπ]
  have hsmall : Valued.v (π * (π * (B e e * B f f))) < 1 :=
    mul_lt_one hπ1 (mul_mem hπO (mul_mem hee hff))
  have hdec : ∀ v ∈ Λ, ∃ c ∈ intL L, ∃ d ∈ intL L, ∃ v₀ ∈ Λ,
      B e v₀ = 0 ∧ B f v₀ = 0 ∧ v = c • (π • e) + d • f + v₀ := by
    intro v hv
    obtain ⟨c, hc, d, hd, v₀, hv₀, h1, h2, h3⟩ := hΛ.decomp hσO hπe hf
      (by rw [hsm, hef, mul_inv_cancel₀ hπ0]) (by rw [map_smul, hfe, smul_eq_mul, mul_inv_cancel₀ hπ0])
      (by convert hsmall using 2; rw [hsm, map_smul, smul_eq_mul]; ring) hv
    rw [hsm] at h1
    exact ⟨c, hc, d, hd, v₀, hv₀, (mul_eq_zero.1 h1).resolve_left hπ0, h2, h3⟩
  have hdec' : ∀ v ∈ Λ', ∃ c ∈ intL L, ∃ d ∈ intL L, ∃ v₀ ∈ Λ',
      B e v₀ = 0 ∧ B f v₀ = 0 ∧ v = c • e + d • (π • f) + v₀ := by
    intro v hv
    obtain ⟨c, hc, d, hd, v₀, hv₀, h1, h2, h3⟩ := hΛ'.decomp hσO he hπf
      (by rw [map_smul, hef, smul_eq_mul, mul_inv_cancel₀ hπ0]) (by rw [hsm, hfe, mul_inv_cancel₀ hπ0])
      (by convert hsmall using 2; rw [hsm, map_smul, smul_eq_mul]; ring) hv
    rw [hsm] at h2
    exact ⟨c, hc, d, hd, v₀, hv₀, h1, (mul_eq_zero.1 h2).resolve_left hπ0, h3⟩
  have hS := hΛ.inter hB (fun v h => by rw [hsm, h, mul_zero]) (fun v h => h) hdec
  have hS' := hΛ'.inter hB (fun v h => h) (fun v h => by rw [hsm, h, mul_zero]) hdec'
  have hlt : perp B W e f < W := by
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    rw [← h] at hfW
    exact inv_ne_zero hπ0 (hef ▸ (mem_perp.1 hfW).2.1)
  obtain ⟨s₀, i₀, f₀, m₀, m₀'⟩ := ih (perp B W e f)
    (by have := Submodule.finrank_lt_finrank_of_lt hlt; omega) _ _ hS hS'
    ⟨b + 1, fun v hv => ⟨ha v hv.1, (perp B W e f).smul_mem _ hv.2⟩⟩
  obtain ⟨s₁, i₁, f₁, r, hr, r', hr', se, sf⟩ := exists_refl hB hτ hτ1 hπ0 hπ1 hσπ hef hee hff
  have s₀e : s₀ e = e := f₀ e fun w hw => by rw [← hB, (mem_perp.1 hw).2.1, map_zero]
  have s₀f : s₀ f = f := f₀ f fun w hw => by rw [← hB, (mem_perp.1 hw).2.2, map_zero]
  have h1r : 1 + π * r ∈ intL L := add_mem (one_mem _) (mul_mem hπO hr)
  have h1r' : 1 + π * r' ∈ intL L := add_mem (one_mem _) (mul_mem hπO hr')
  refine ⟨s₁ ∘ₗ s₀, fun u v => ?_, fun u hu => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · simp only [LinearMap.comp_apply, i₁, i₀]
  · rw [LinearMap.comp_apply, f₀ u fun w hw => hu w (mem_perp.1 hw).1, f₁ u (hu e heW) (hu f hfW)]
  · obtain ⟨c, hc, d, hd, v₀, hv₀, h1, h2, rfl⟩ := hdec v hv
    have h3 := m₀ v₀ ⟨hv₀, mem_perp.2 ⟨((hΛ v₀).1 hv₀).1, h1, h2⟩⟩
    have h4 := mem_perp.1 h3.2
    have : (s₁ ∘ₗ s₀) (c • (π • e) + d • f + v₀) =
        (c * (-r * π * π) + d * (1 + π * r')) • e + (c * (1 + π * r) + d * (-r')) • (π • f) + s₀ v₀ := by
      simp only [LinearMap.comp_apply, map_add, map_smul, s₀e, s₀f, f₁ _ h4.2.1 h4.2.2, se, sf]
      module
    rw [this]
    refine hΛ'.add (hΛ'.add (hΛ'.smul hσO ?_ he) (hΛ'.smul hσO ?_ hπf)) h3.1
    · exact add_mem (mul_mem hc (mul_mem (mul_mem (neg_mem hr) hπO) hπO)) (mul_mem hd h1r')
    · exact add_mem (mul_mem hc h1r) (mul_mem hd (neg_mem hr'))
  · obtain ⟨c, hc, d, hd, v₀, hv₀, h1, h2, rfl⟩ := hdec' v hv
    have h3 := m₀' v₀ ⟨hv₀, mem_perp.2 ⟨((hΛ' v₀).1 hv₀).1, h1, h2⟩⟩
    have h4 := mem_perp.1 h3.2
    have : (s₁ ∘ₗ s₀) (c • e + d • (π • f) + v₀) =
        (c * (-r) + d * (1 + π * r')) • (π • e) + (c * (1 + π * r) + d * (-r' * π * π)) • f + s₀ v₀ := by
      simp only [LinearMap.comp_apply, map_add, map_smul, s₀e, s₀f, f₁ _ h4.2.1 h4.2.2, se, sf]
      module
    rw [this]
    refine hΛ.add (hΛ.add (hΛ.smul hσO ?_ hπe) (hΛ.smul hσO ?_ hf)) h3.1
    · exact add_mem (mul_mem hc (neg_mem hr)) (mul_mem hd h1r')
    · exact add_mem (mul_mem hc h1r) (mul_mem hd (mul_mem (mul_mem (neg_mem hr') hπO) hπO))

end Abstract

section Matrices

variable {n : ℕ} {σ : L →+* L}

def form (σ : L →+* L) (J : Matrix (Fin n) (Fin n) L) : (Fin n → L) →ₛₗ[σ] (Fin n → L) →ₗ[L] L :=
  LinearMap.mk₂'ₛₗ σ (RingHom.id L) (fun u v => (σ ∘ u) ⬝ᵥ (J *ᵥ v))
    (fun u u' v => by
      rw [show σ ∘ (u + u') = σ ∘ u + σ ∘ u' from funext fun i => by simp, add_dotProduct])
    (fun c u v => by
      rw [show σ ∘ (c • u) = σ c • (σ ∘ u) from funext fun i => by simp, smul_dotProduct])
    (fun u v v' => by rw [Matrix.mulVec_add, dotProduct_add])
    (fun c u v => by rw [Matrix.mulVec_smul, dotProduct_smul]; rfl)

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem form_apply (J : Matrix (Fin n) (Fin n) L) (u v : Fin n → L) :
    form σ J u v = (σ ∘ u) ⬝ᵥ (J *ᵥ v) := rfl

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem form_mulVec (J M : Matrix (Fin n) (Fin n) L) (u v : Fin n → L) :
    form σ J (M *ᵥ u) (M *ᵥ v) = form σ (cT σ M * J * M) u v := by
  have : σ ∘ (M *ᵥ u) = (σ ∘ u) ᵥ* cT σ M := by
    funext i
    simp [cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  rw [form_apply, form_apply, this, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem form_single (J : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    form σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have : σ ∘ (Pi.single i 1 : Fin n → L) = Pi.single i 1 := by
    funext k; by_cases h : k = i <;> simp [h]
  rw [form_apply, this]
  simp

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem form_herm (hσσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) L}
    (hJ : ∀ i j, σ (J i j) = J j i) (u v : Fin n → L) : σ (form σ J u v) = form σ J v u := by
  simp only [form_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, Function.comp_apply, hσσ, hJ,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def intVec (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) : Set (Fin n → L) :=
  {v | ∀ i, v i ∈ intL L}

theorem mulVec_mem {M : Matrix (Fin n) (Fin n) L} (hM : ∀ i j, M i j ∈ intL L) {v : Fin n → L}
    (hv : v ∈ intVec L n) : M *ᵥ v ∈ intVec L n := fun i => by
  show ∑ j, M i j * v j ∈ intL L
  exact Subring.sum_mem _ fun j _ => mul_mem (hM i j) (hv j)

theorem single_mem (j : Fin n) : (Pi.single j 1 : Fin n → L) ∈ intVec L n := by
  intro i
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem entries_mem {M : Matrix (Fin n) (Fin n) L} (hM : ∀ v ∈ intVec L n, M *ᵥ v ∈ intVec L n)
    (i j : Fin n) : M i j ∈ intL L := by
  simpa using hM _ (single_mem j) i

theorem selfDual_intVec (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {J : GL (Fin n) L}
    (hJ : J ∈ GLint (Fin n) (intL L)) :
    SelfDual (form σ (J : Matrix (Fin n) (Fin n) L)) ⊤ (intVec L n) := by
  intro v
  constructor
  · intro hv
    refine ⟨trivial, fun w hw => ?_⟩
    rw [form_apply]
    refine Subring.sum_mem _ fun i _ => mul_mem ?_ (mulVec_mem (P.cartan_entries_of_mem _ J hJ) hw i)
    rw [Function.comp_apply, mem_int, hσ]; exact hv i
  · rintro ⟨-, hv⟩ i
    have := hv _ (mulVec_mem (P.cartan_entries_of_mem _ J⁻¹ (inv_mem hJ)) (single_mem i))
    rw [form_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, dotProduct_single, mul_one,
      Function.comp_apply, mem_int, hσ] at this
    exact this

theorem selfDual_image {J : Matrix (Fin n) (Fin n) L} {Λ : Set (Fin n → L)}
    (h : SelfDual (form σ J) ⊤ Λ) {g : GL (Fin n) L} (hg : g ∈ UJ σ J) :
    SelfDual (form σ J) ⊤ {v | (g : Matrix (Fin n) (Fin n) L) *ᵥ v ∈ Λ} := by
  have hg' : ∀ u v, form σ J ((g : Matrix (Fin n) (Fin n) L) *ᵥ u) ((g : Matrix (Fin n) (Fin n) L) *ᵥ v)
      = form σ J u v := fun u v => by rw [form_mulVec, show _ = J from hg]
  intro v
  constructor
  · intro hv
    exact ⟨trivial, fun w hw => by rw [← hg']; exact h.pair hv hw⟩
  · rintro ⟨-, hv⟩
    refine (h _).2 ⟨trivial, fun w hw => ?_⟩
    have e : (g : Matrix (Fin n) (Fin n) L) *ᵥ (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [← e, hg']
    exact hv _ (by show _ ∈ Λ; rw [e]; exact hw)

theorem mem_GLint_of_unitary (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {J : GL (Fin n) L}
    (hJ : J ∈ GLint (Fin n) (intL L)) {k : GL (Fin n) L} (hk : k ∈ UJ σ (J : Matrix (Fin n) (Fin n) L))
    (hi : ∀ i j, (k : Matrix (Fin n) (Fin n) L) i j ∈ intL L) : k ∈ GLint (Fin n) (intL L) := by
  refine P.cartan_mem_of_entries _ k hi ?_
  have hk' : cT σ (k : Matrix (Fin n) (Fin n) L) * J * k = J := hk
  have : ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      ((J⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (cT σ (k : Matrix (Fin n) (Fin n) L) * J) := by
    apply Units.inv_eq_of_mul_eq_one_left
    rw [Matrix.mul_assoc, hk', Units.inv_mul]
  rw [this]
  intro i j
  rw [Matrix.mul_apply]
  refine Subring.sum_mem _ fun a _ => mul_mem (P.cartan_entries_of_mem _ _ (inv_mem hJ) _ _) ?_
  rw [Matrix.mul_apply]
  refine Subring.sum_mem _ fun b _ => mul_mem ?_ (P.cartan_entries_of_mem _ _ hJ _ _)
  show σ _ ∈ _
  rw [mem_int, hσ]; exact hi _ _

theorem exists_pow_mem {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (M : Matrix (Fin n) (Fin n) L) :
    ∃ N : ℕ, ∀ i j, ϖ ^ N * M i j ∈ intL L := by
  first
  | exact @_root_.GlobalTheory.MatrixEntryBound.main
  | exact _root_.GlobalTheory.MatrixEntryBound.main
  | (apply _root_.GlobalTheory.MatrixEntryBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.MatrixEntryBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MatrixEntryBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MatrixEntryBound.main ..)

theorem inv_mem_doubleCoset {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {J : GL (Fin n) L}
    (hJ : J ∈ GLint (Fin n) (intL L))
    (hh : ∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i)
    {g : GL (Fin n) L} (hg : g ∈ UJ σ (J : Matrix (Fin n) (Fin n) L)) :
    ∃ k₁ ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L),
      ∃ k₂ ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L), g⁻¹ = k₁ * g * k₂ := by
  obtain ⟨hσσ, hσ, hσϖ, hϖ, ⟨x, hx, hx1⟩, -, -⟩ := hU
  have hx0 : σ x - x ≠ 0 := by
    intro h; rw [h, map_zero] at hx1; exact zero_ne_one hx1
  have hτ : σ x * (σ x - x)⁻¹ ∈ intL L :=
    mul_mem (by rw [mem_int, hσ]; exact hx) (by rw [mem_int, map_inv₀, hx1, inv_one])
  have hτ1 : σ x * (σ x - x)⁻¹ + σ (σ x * (σ x - x)⁻¹) = 1 := by
    rw [map_mul, map_inv₀, map_sub, hσσ, ← neg_sub (σ x) x, inv_neg]
    linear_combination mul_inv_cancel₀ hx0
  have hΛ := selfDual_intVec hσ hJ
  have hΛ' := selfDual_image hΛ hg
  obtain ⟨N, hN⟩ := exists_pow_mem hϖ ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  obtain ⟨s, hs, -, h1, h2⟩ := exists_swap hσ (form_herm hσσ hh) hτ hτ1 hσϖ hϖ _ ⊤ (Nat.lt_succ_self _)
    _ _ hΛ hΛ' ⟨N, fun v hv => by
      have := mulVec_mem (M := ϖ ^ N • ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) hN hv
      rwa [Matrix.smul_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this⟩
  obtain ⟨S, rfl⟩ : ∃ S : Matrix (Fin n) (Fin n) L, Matrix.toLin' S = s := Matrix.toLin'.surjective s
  simp only [Matrix.toLin'_apply] at hs h1 h2
  have hS : cT σ S * J * S = J := by
    ext i j
    rw [← form_single (σ := σ) (cT σ S * (J : Matrix (Fin n) (Fin n) L) * S), ← form_mulVec, hs, form_single]
  have hSi : (((J⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (cT σ S * J)) * S = 1 := by
    rw [Matrix.mul_assoc, hS, Units.inv_mul]
  let S' : GL (Fin n) L := ⟨S, _, mul_eq_one_comm.mp hSi, hSi⟩
  have hS' : S' ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) := hS
  have k1 : g * S' ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L) := by
    refine ⟨mul_mem hg hS', mem_GLint_of_unitary hσ hJ (mul_mem hg hS') (entries_mem fun v hv => ?_)⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact h1 v hv
  have k2 : S' * g⁻¹ ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L) := by
    refine ⟨(UJ σ (J : Matrix (Fin n) (Fin n) L)).mul_mem hS' (inv_mem hg),
      mem_GLint_of_unitary hσ hJ (mul_mem hS' (inv_mem hg)) (entries_mem fun v hv => ?_)⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    apply h2
    show _ ∈ intVec L n
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact hv
  exact ⟨_, k2, _, inv_mem k1, by group⟩

theorem antiJ_mul_self : antiJ L n * antiJ L n = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · have := i.2
    have := j.2
    simp only [antiJ, Fin.val_rev, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · intro b _ hb
    have : ¬ (i.val + b.val + 1 = n) := fun h => hb (Fin.ext (by rw [Fin.val_rev]; omega))
    simp [antiJ, this]
  · simp

theorem heckeCommU : HeckeCommU := by
  intro L _ _ _ ϖ σ q n k _ hU f₁ hf₁ f₂ hf₂
  have hint : ∀ i j, antiJ L n i j ∈ intL L := by
    intro i j; unfold antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨J, hJ, hJe⟩ := P.cartan_exists_glint (intL L) _ _ (antiJ_mul_self (L := L) (n := n)) hint hint
  refine P.heckecomm_gelfand (KU σ n) (fun g => g⁻¹) (fun x y => mul_inv_rev x y) (fun x => inv_inv x)
    (fun x hx => inv_mem hx) (fun g => ?_) f₁ f₂ hf₁.1 hf₂.1
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := inv_mem_doubleCoset hU hJ (g := (g : GL (Fin n) L)) (by
    intro i j
    rw [hJe]
    simp only [antiJ, add_comm i.val j.val]
    split_ifs <;> simp) (by rw [hJe]; exact g.2)
  rw [hJe] at hk₁ hk₂
  exact ⟨⟨⟨k₁, hk₁.1⟩, hk₁⟩, ⟨⟨k₂, hk₂.1⟩, hk₂⟩, Subtype.ext e⟩

end Matrices

theorem inv_mem_doubleCoset_and_comm : (∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (J : GL (Fin n) L), IsUnramInv ϖ σ q → J ∈ GLint (Fin n) (intL L) → (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) → ∀ g ∈ UJ σ (J : Matrix (Fin n) (Fin n) L), ∃ k₁ ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L), ∃ k₂ ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L), g⁻¹ = k₁ * g * k₂) ∧ HeckeCommU :=
  ⟨fun _ _ _ _ _ _ _ _ _ hU hJ hh _ hg => inv_mem_doubleCoset hU hJ hh hg, heckeCommU⟩

end GlobalTheory.UnitarySwap

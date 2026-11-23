import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

namespace TorusAtAssembly

section Form

variable {ι : Type} [Fintype ι]

open NumberField in
variable {ι : Type} [Fintype ι] in
theorem _root_.GlobalTheory.TorusAtAssembly.im_Hf_add_left (x y z : EuclideanSpace ℂ ι) :
    (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (x + y) z).im = (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x z).im + (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf y z).im := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf, add_mul, Finset.sum_add_distrib]

open NumberField in
variable {ι : Type} [Fintype ι] in
theorem _root_.GlobalTheory.TorusAtAssembly.im_Hf_add_right (x y z : EuclideanSpace ℂ ι) :
    (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x (y + z)).im = (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x y).im + (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x z).im := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf, mul_add, Finset.sum_add_distrib]

theorem im_Hf_neg_left (x z : EuclideanSpace ℂ ι) :
    (Hf (-x) z).im = -(Hf x z).im := by
  simp [Hf, Finset.sum_neg_distrib]

open NumberField in
variable {ι : Type} [Fintype ι] in
theorem _root_.GlobalTheory.TorusAtAssembly.im_Hf_swap (x y : EuclideanSpace ℂ ι) :
    (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf y x).im = -(_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x y).im := by
  have h : _root_.ReciprocityTheory.ChartRestriction.G.I2.Hf y x = (starRingEnd ℂ) (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x y) := by
    simp [_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf, map_sum, mul_comm]
  rw [h, Complex.conj_im]

end Form

variable {E : Type} [Field E] [NumberField E]

open NumberField in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.TorusAtAssembly.act_add {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (x y : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.act α (x + y) = _root_.ReciprocityTheory.ChartRestriction.G.I2.act α x + _root_.ReciprocityTheory.ChartRestriction.G.I2.act α y := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.act
  ext i
  simp [mul_add]

open NumberField in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.TorusAtAssembly.Hf_act_conj [IsCMField E] {dim : (E →+* ℂ) → ℕ} (α β : 𝓞 E)
    (h : (β : E) = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (α : E))
    (x y : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim) : _root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x (_root_.ReciprocityTheory.ChartRestriction.G.I2.act β y) = _root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (_root_.ReciprocityTheory.ChartRestriction.G.I2.act α x) y := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Hf _root_.ReciprocityTheory.ChartRestriction.G.I2.act
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : (starRingEnd ℂ) (i.fst (β : E)) = i.fst (α : E) := by
    rw [h]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
    rw [IsCMField.complexEmbedding_complexConj, Complex.conj_conj]
  simp only [map_mul, hc]
  ring

noncomputable def sgnFloor (t : ℝ) : ℤ := ((Int.negOnePow ⌊t⌋ : ℤˣ) : ℤ)

open NumberField in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.TorusAtAssembly.sgnFloor_pm (t : ℝ) :
    _root_.GlobalTheory.TorusAtAssembly.sgnFloor t = 1 ∨ _root_.GlobalTheory.TorusAtAssembly.sgnFloor t = -1 := by
  rcases Int.units_eq_one_or (Int.negOnePow ⌊t⌋) with h | h <;> simp [_root_.GlobalTheory.TorusAtAssembly.sgnFloor, h]

open NumberField in
variable {E : Type} [Field E] [NumberField E] in
private theorem sgnFloor_intCast_eq_negOnePow (k : ℤ) :
    _root_.GlobalTheory.TorusAtAssembly.sgnFloor (k : ℝ) = ((Int.negOnePow k : ℤˣ) : ℤ) := by
  simp [_root_.GlobalTheory.TorusAtAssembly.sgnFloor]

open NumberField in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.TorusAtAssembly.sgnFloor_cos (k : ℤ) :
    (_root_.GlobalTheory.TorusAtAssembly.sgnFloor (k : ℝ) : ℝ) = Real.cos (Real.pi * k) := by
  rw [sgnFloor_intCast_eq_negOnePow, mul_comm, Real.cos_int_mul_pi, Int.cast_negOnePow]

open NumberField in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.TorusAtAssembly.sgnFloor_add (a b c k : ℤ) :
    (_root_.GlobalTheory.TorusAtAssembly.sgnFloor ((a : ℝ) + b + c + 2 * k) : ℝ) =
      _root_.GlobalTheory.TorusAtAssembly.sgnFloor (a : ℝ) * _root_.GlobalTheory.TorusAtAssembly.sgnFloor (b : ℝ) * Real.cos (Real.pi * c) := by
  rw [← _root_.GlobalTheory.TorusAtAssembly.sgnFloor_cos]
  have h : ((a : ℝ) + b + c + 2 * k) = ((a + b + c + 2 * k : ℤ) : ℝ) := by push_cast; ring
  rw [h, sgnFloor_intCast_eq_negOnePow, sgnFloor_intCast_eq_negOnePow, sgnFloor_intCast_eq_negOnePow,
    sgnFloor_intCast_eq_negOnePow, Int.negOnePow_add, Int.negOnePow_add, Int.negOnePow_add,
    Int.negOnePow_two_mul]
  push_cast
  ring

section Build

variable [IsCMField E] {dim : (E →+* ℂ) → ℕ}
  {b : Module.Basis (Fin (2 * Fintype.card (Idx dim))) ℝ (Vsp dim)} {w w' : 𝓞 E}

open NumberField in
variable {E : Type} [Field E] [NumberField E] in
variable [IsCMField E] {dim : (E →+* ℂ) → ℕ}
  {b : Module.Basis (Fin (2 * Fintype.card (_root_.ReciprocityTheory.ChartRestriction.G.I2.Idx dim))) ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim)} {w w' : 𝓞 E} in

theorem _root_.GlobalTheory.TorusAtAssembly.integral_of_parity (hw : (w' : E) = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (w : E))
    (par : ∀ x ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat b, ∀ y ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat b, ∃ k : ℤ,
      (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x (_root_.ReciprocityTheory.ChartRestriction.G.I2.act w y)).im - (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x (_root_.ReciprocityTheory.ChartRestriction.G.I2.act w' y)).im - (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x y).im = 2 * k) :
    ∀ x y : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim, x ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat b → y ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat b → ∃ k : ℤ, (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x y).im = k := by
  have hQ : ∀ x ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat b, ∃ k : ℤ, (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x (_root_.ReciprocityTheory.ChartRestriction.G.I2.act w x)).im = k := by
    intro x hx
    obtain ⟨k, hk⟩ := par x hx x hx
    rw [_root_.GlobalTheory.TorusAtAssembly.Hf_act_conj w w' hw,
      _root_.GlobalTheory.TorusAtAssembly.im_Hf_swap x (_root_.ReciprocityTheory.ChartRestriction.G.I2.act w x)] at hk
    have h0 : (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x x).im = 0 := by
      have := _root_.GlobalTheory.TorusAtAssembly.im_Hf_swap x x
      linarith
    exact ⟨k, by linarith⟩
  intro x y hx hy
  obtain ⟨k, hk⟩ := par x hx y hy
  rw [_root_.GlobalTheory.TorusAtAssembly.Hf_act_conj w w' hw,
    _root_.GlobalTheory.TorusAtAssembly.im_Hf_swap y (_root_.ReciprocityTheory.ChartRestriction.G.I2.act w x)] at hk
  obtain ⟨a, ha⟩ := hQ x hx
  obtain ⟨a', ha'⟩ := hQ y hy
  obtain ⟨s, hs⟩ := hQ (x + y) (Submodule.add_mem _ hx hy)
  rw [_root_.GlobalTheory.TorusAtAssembly.act_add, _root_.GlobalTheory.TorusAtAssembly.im_Hf_add_left, _root_.GlobalTheory.TorusAtAssembly.im_Hf_add_right,
    _root_.GlobalTheory.TorusAtAssembly.im_Hf_add_right] at hs
  refine ⟨s - a - a' - 2 * k, ?_⟩
  push_cast
  linarith

noncomputable def torus (r : ℕ)
    (hdim : ∀ τ, dim τ + dim (NumberField.ComplexEmbedding.conjugate τ) = r)
    (hw : (w' : E) = cc (w : E))
    (stable : ∀ (α : 𝓞 E) (x : Vsp dim), x ∈ lat b → act α x ∈ lat b)
    (par : ∀ x ∈ lat b, ∀ y ∈ lat b, ∃ k : ℤ,
      (Hf x (act w y)).im - (Hf x (act w' y)).im - (Hf x y).im = 2 * k)
    (perfect : ∀ φ : lat b →+ ℤ, ∃ x ∈ lat b, ∀ y : lat b, (φ y : ℝ) = (Hf x (y : Vsp dim)).im) :
    PT E where
  dim := dim
  r := r
  dim_conj := hdim
  b := b
  stable := stable
  integral := integral_of_parity hw par
  perfect := perfect
  eps y := sgnFloor (Hf y (act w y)).im
  eps_pm x _ := sgnFloor_pm _
  eps_add x hx y hy := by
    obtain ⟨a, ha⟩ := integral_of_parity hw par x (act w x) hx (stable w x hx)
    obtain ⟨a', ha'⟩ := integral_of_parity hw par y (act w y) hy (stable w y hy)
    obtain ⟨c, hc⟩ := integral_of_parity hw par x y hx hy
    obtain ⟨k, hk⟩ := par x hx y hy
    rw [Hf_act_conj w w' hw] at hk
    rw [ha, ha', hc, ← sgnFloor_add a a' c k]
    congr 2
    rw [act_add, im_Hf_add_left, im_Hf_add_right, im_Hf_add_right, im_Hf_swap (act w x) y]
    linarith
  eps_iso x _ h := by
    rw [im_Hf_swap, h w]
    simp [sgnFloor]

end Build

end TorusAtAssembly

open NumberField in
variable {E : Type} [Field E] [NumberField E] in

theorem _root_.GlobalTheory.torusAtExists_of_parts :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∀ x ∈ X.dom, ∃ e : X.Ψ → Fin r → (Fin r → ℂ), (∀ τ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (e τ a) (e τ b) = if a = b then ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0) ∧ ∀ τ (i : ℕ) (hi : i ≤ r), Submodule.span ℂ (Set.range fun a : Fin i => e τ (Fin.castLE hi a)) = Submodule.span ℂ (Set.range fun a : Fin i => _root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (Fin.castLE hi a))) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ b : Module.Basis (Fin (2 * (X.Ψ.card * r))) ℝ (X.Ψ → Fin r → ℂ), ∀ y, y ∈ Submodule.span ℤ (Set.range b) ↔ ∃ v ∈ X.Λ, (fun τ : X.Ψ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v) = y) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧ ∀ u v : Fin r → E, ∑ τ : X.Ψ, X.c τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 u) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)).im = sg * ((Algebra.trace ℚ E (X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) : ℚ) : ℝ)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)), (∀ τ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (e τ a) (e τ b) = if a = b then ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0) → ∃ (dim : (E →+* ℂ) → ℕ) (hp : ∀ τ : X.Ψ, dim τ.1 = X.p0) (hn : ∀ τ : X.Ψ, dim (ComplexEmbedding.conjugate τ.1) = r - X.p0) (Φ : (X.Ψ → Fin r → ℂ) ≃ₗ[ℝ] _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim), Fintype.card (_root_.ReciprocityTheory.ChartRestriction.G.I2.Idx dim) = X.Ψ.card * r ∧ (∀ τ, dim τ + dim (ComplexEmbedding.conjugate τ) = r) ∧ (∀ y (τ : X.Ψ) (a : Fin (dim τ.1)), (Φ y) ⟨τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ (Fin.castLE (by rw [hp τ]; exact X.p0_le) a))) ∧ (∀ y (τ : X.Ψ) (a : Fin (dim (ComplexEmbedding.conjugate τ.1))), (Φ y) ⟨ComplexEmbedding.conjugate τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) * (starRingEnd ℂ) (-_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ ⟨X.p0 + a.1, by have h1 : a.1 < r - X.p0 := lt_of_lt_of_eq a.2 (hn τ); have := X.p0_le; omega⟩))) ∧ (∀ (α : 𝓞 E) y, Φ (fun τ => τ.1 (α : E) • y τ) = _root_.ReciprocityTheory.ChartRestriction.G.I2.act α (Φ y)) ∧ ∀ y y', (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (Φ y) (Φ y')).im = ∑ τ : X.Ψ, X.c τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (y' τ)).im) → (∀ (E : Type) [Field E] [NumberField E] (X : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT E), ∃ s ∈ X.Sec 1 1, s ≠ 0) → _root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtExistsStatement := by
  intro hframe hbasis hsign hiso hsec
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtExistsStatement
  intro E _ _ _ r X hperf w0 hpar x hx
  obtain ⟨e, he_orth, he_flag⟩ := hframe E r X x hx
  obtain ⟨bas, hbas⟩ := hbasis E r X
  obtain ⟨sg, hsg, hsgeq⟩ := hsign E r X
  obtain ⟨dim, hp, hn, Φ, hcard, hdim, hpos, hneg, hact, him⟩ := hiso E r X e he_orth
  have hint : IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E)) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
    exact map_isIntegral_int (IsCMField.complexConj E) w0.isIntegral_coe
  let w' : 𝓞 E := ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E), hint⟩
  have hw' : (w' : E) = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E) := rfl
  let φ : (Fin r → E) →+ _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim :=
    { toFun := fun v => Φ (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)
      map_zero' := by
        have h : (fun τ : X.Ψ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (0 : Fin r → E)) = 0 := by
          funext τ a
          simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
        simp only [h, map_zero]
      map_add' := fun u v => by
        have h : (fun τ : X.Ψ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (u + v)) =
            (fun τ : X.Ψ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 u) + (fun τ : X.Ψ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v) := by
          funext τ a
          simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
        simp only [h, map_add] }
  have hφ : ∀ v, φ v = Φ (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v) := fun v => rfl
  have hsmul : ∀ (α : 𝓞 E) (v : Fin r → E), α • v = (α : E) • v := fun α v => by
    funext i
    rfl
  have hφactE : ∀ (α : 𝓞 E) (v : Fin r → E), φ ((α : E) • v) = _root_.ReciprocityTheory.ChartRestriction.G.I2.act α (φ v) := by
    intro α v
    rw [hφ, hφ, ← hact]
    congr 1
    funext τ a
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, map_mul]
  have hφact : ∀ (α : 𝓞 E) (v : Fin r → E), φ (α • v) = _root_.ReciprocityTheory.ChartRestriction.G.I2.act α (φ v) := by
    intro α v
    rw [hsmul, hφactE]
  have himφ : ∀ u v, (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (φ u) (φ v)).im =
      sg * ((Algebra.trace ℚ E (X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) : ℚ) : ℝ) := fun u v =>
    (him _ _).trans (hsgeq u v)
  let bT : Module.Basis (Fin (2 * Fintype.card (_root_.ReciprocityTheory.ChartRestriction.G.I2.Idx dim))) ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim) :=
    (bas.map Φ).reindex (finCongr (by rw [hcard]))
  have hL : ∀ y, y ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT ↔ ∃ v ∈ X.Λ, φ v = y := by
    intro y
    have hrange : Set.range bT = (Φ.toLinearMap.restrictScalars ℤ) '' Set.range bas := by
      ext z
      simp only [bT, Module.Basis.range_reindex, Set.mem_range, Set.mem_image,
        Module.Basis.map_apply, exists_exists_eq_and, LinearMap.coe_restrictScalars,
        LinearEquiv.coe_coe]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.lat
    rw [hrange, Submodule.span_image, Submodule.mem_map]
    constructor
    · rintro ⟨y0, hy0, rfl⟩
      obtain ⟨v, hv, rfl⟩ := (hbas y0).1 hy0
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨_, (hbas _).2 ⟨v, hv, rfl⟩, rfl⟩
  have hmem : ∀ v ∈ X.Λ, φ v ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT := fun v hv => (hL _).2 ⟨v, hv, rfl⟩
  have stable : ∀ (α : 𝓞 E) (y : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim), y ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT → _root_.ReciprocityTheory.ChartRestriction.G.I2.act α y ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT := by
    intro α y hy
    obtain ⟨v, hv, rfl⟩ := (hL y).1 hy
    rw [← hφact]
    exact hmem _ (X.Λ.smul_mem α hv)
  have par : ∀ y ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT, ∀ z ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT, ∃ k : ℤ,
      (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf y (_root_.ReciprocityTheory.ChartRestriction.G.I2.act w0 z)).im - (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf y (_root_.ReciprocityTheory.ChartRestriction.G.I2.act w' z)).im - (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf y z).im = 2 * k := by
    intro y hy z hz
    obtain ⟨u, hu, rfl⟩ := (hL y).1 hy
    obtain ⟨v, hv, rfl⟩ := (hL z).1 hz
    obtain ⟨k, hk⟩ := hpar u hu v hv
    have hsub : (w0 - w') • v = ((w0 : E) - _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E)) • v := by
      rw [hsmul]
      rfl
    have hsplit : φ (w0 • v) = φ ((w0 - w') • v) + φ (w' • v) := by
      rw [← map_add, ← add_smul, sub_add_cancel]
    rw [← hφact, ← hφact, hsplit, _root_.GlobalTheory.TorusAtAssembly.im_Hf_add_right, himφ, himφ, himφ, hsub]
    have hkR := congrArg (fun q : ℚ => (q : ℝ)) hk
    push_cast at hkR
    rcases hsg with rfl | rfl
    · exact ⟨k, by linarith⟩
    · exact ⟨-k, by push_cast; linarith⟩
  have hneg0 : ∀ y z : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim, (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (-y) z).im = -(_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf y z).im := by
    intro y z
    have h := _root_.GlobalTheory.TorusAtAssembly.im_Hf_add_left y (-y) z
    rw [add_neg_cancel] at h
    have h0 : (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (0 : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim) z).im = 0 := by simp [_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf]
    linarith
  have perfect : ∀ ψ : _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT →+ ℤ, ∃ y ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT, ∀ z : _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT,
      (ψ z : ℝ) = (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf y (z : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim)).im := by
    intro ψ
    let g : X.Λ →+ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT :=
      (φ.comp X.Λ.subtype.toAddMonoidHom).codRestrict (_root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT) (fun v => hmem v v.2)
    obtain ⟨u, hu, hχ⟩ := hperf (ψ.comp g)
    have hval : ∀ v (hv : v ∈ X.Λ), (ψ ⟨φ v, hmem v hv⟩ : ℝ) =
        ((Algebra.trace ℚ E (X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) : ℚ) : ℝ) := by
      intro v hv
      have h := congrArg (fun q : ℚ => (q : ℝ)) (hχ ⟨v, hv⟩)
      push_cast at h
      exact h
    rcases hsg with rfl | rfl
    · refine ⟨φ u, hmem u hu, fun z => ?_⟩
      obtain ⟨v, hv, hvz⟩ := (hL z).1 z.2
      obtain rfl : z = ⟨φ v, hmem v hv⟩ := Subtype.ext hvz.symm
      rw [hval v hv]
      show _ = (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (φ u) (φ v)).im
      rw [himφ]
      ring
    · refine ⟨-φ u, neg_mem (hmem u hu), fun z => ?_⟩
      obtain ⟨v, hv, hvz⟩ := (hL z).1 z.2
      obtain rfl : z = ⟨φ v, hmem v hv⟩ := Subtype.ext hvz.symm
      rw [hval v hv]
      show _ = (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (-φ u) (φ v)).im
      rw [hneg0, himφ]
      ring
  let T : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT E := _root_.GlobalTheory.TorusAtAssembly.torus (dim := dim) (b := bT) (w := w0) (w' := w')
    r hdim hw' stable par perfect
  obtain ⟨s, hs, hs0⟩ := hsec E T
  refine ⟨
    { T := T
      φ := φ
      sg := sg
      sg_pm := hsg
      dim_pos := hp
      dim_neg := hn
      e := e
      e_orth := he_orth
      e_flag := he_flag
      coord_pos := fun τ a v => hpos _ τ a
      coord_neg := fun τ a v => hneg _ τ a
      w0 := w0
      act_eq := hφactE
      lat := hL
      im_eq := fun u _ v _ => himφ u v
      eps_eq := ?_
      s := s
      s_mem := hs
      s_ne := hs0 }, rfl⟩
  intro v hv
  have hv' : (w0 : E) • v ∈ X.Λ := by
    rw [← hsmul]
    exact X.Λ.smul_mem w0 hv
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.TorusAtAssembly.integral_of_parity hw' par (φ v) (φ ((w0 : E) • v))
    (hmem v hv) (hmem _ hv')
  show ((_root_.GlobalTheory.TorusAtAssembly.sgnFloor (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (φ v) (_root_.ReciprocityTheory.ChartRestriction.G.I2.act w0 (φ v))).im : ℤ) : ℝ) = _
  rw [← hφactE, hk, _root_.GlobalTheory.TorusAtAssembly.sgnFloor_cos]
  congr 2
  exact hk.symm

end GlobalTheory

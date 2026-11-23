import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsNearlyPrimitive
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsUnitaryExt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsShortIso

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.ShortStep

open MinkowskiProductBounds

theorem quot_maj {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {G H : Matrix n n ℂ} {V w : Matrix (Fin 1) n ℂ} {B : Matrix m n ℂ} {S : Matrix n m ℂ}
    (hG : Gᴴ = G) (h0 : G.det ≠ 0) (hH : H.PosDef) (hm : H * G⁻¹ * H = G)
    (hw : V * G * wᴴ = 1) (hV : V * G * Vᴴ = 0) (hB : B * G * Vᴴ = 0)
    (hS : S * B = 1 - G * wᴴ * V - G * Vᴴ * w) (hd : (B * G * Bᴴ).det ≠ 0) :
    ∃ L : Matrix m (Fin 1) ℂ, ((B - L * V) * H * (B - L * V)ᴴ).PosDef ∧
      (B - L * V) * H * (B - L * V)ᴴ * (B * G * Bᴴ)⁻¹ * ((B - L * V) * H * (B - L * V)ᴴ) =
        B * G * Bᴴ := by
  have inj : ∀ {k : Type} [Fintype k] [DecidableEq k] (A : Matrix k n ℂ) (R : Matrix n k ℂ),
      A * R = 1 → Function.Injective A.vecMul := fun A R h x y e => by
    have := congrArg (fun z => z ᵥ* R) e
    simpa [vecMul_vecMul, h] using this
  have hh : (V * H * Vᴴ).PosDef :=
    hH.mul_mul_conjTranspose_same (inj V (G * wᴴ) (by rw [← Matrix.mul_assoc, hw]))
  have hu : IsUnit (V * H * Vᴴ).det := hh.det_pos.ne'.isUnit
  refine ⟨B * H * Vᴴ * (V * H * Vᴴ)⁻¹, ?_⟩
  generalize hL : B * H * Vᴴ * (V * H * Vᴴ)⁻¹ = L
  have e1 : (B - L * V) * H * Vᴴ = 0 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc L, Matrix.mul_assoc L, ← hL,
      nonsing_inv_mul_cancel_right _ _ hu, sub_self]
  have e2 : (B - L * V) * G * Vᴴ = 0 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc L, Matrix.mul_assoc L, hB, hV]; simp
  have hB' : V * G * Bᴴ = 0 := by
    simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using congrArg conjTranspose hB
  have e3 : (B - L * V) * G * (B - L * V)ᴴ = B * G * Bᴴ := by
    rw [conjTranspose_sub, conjTranspose_mul, Matrix.mul_sub, ← Matrix.mul_assoc, e2,
      Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc L, Matrix.mul_assoc L, hB']
    simp
  have e4 : S * (B - L * V) = 1 - (G * wᴴ + S * L) * V - G * Vᴴ * w := by
    rw [Matrix.mul_sub, hS, Matrix.add_mul, Matrix.mul_assoc S]; abel
  generalize B - L * V = P at e1 e2 e3 e4
  refine ⟨hH.mul_mul_conjTranspose_same (inj P (G * Pᴴ * (B * G * Bᴴ)⁻¹) ?_), ?_⟩
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e3, mul_nonsing_inv _ hd.isUnit]
  obtain ⟨Y, hY⟩ : ∃ Y, Y = P * H * G⁻¹ := ⟨_, rfl⟩
  have y1 : Y * G = P * H := by rw [hY, nonsing_inv_mul_cancel_right _ _ h0.isUnit]
  have y2 : Y * H = P * G := by
    rw [hY]; conv_rhs => rw [← hm]
    simp only [Matrix.mul_assoc]
  have y3 : Y * S * P = Y - Y * (G * wᴴ + S * L) * V := by
    rw [Matrix.mul_assoc, e4, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc Y (G * Vᴴ),
      ← Matrix.mul_assoc Y G, y1, e1, Matrix.mul_assoc]
    simp
  have y4 : Y * (G * wᴴ + S * L) = 0 := by
    have := congrArg (fun Z => Z * H * Vᴴ * (V * H * Vᴴ)⁻¹) y3
    simp only [Matrix.sub_mul] at this
    rw [y2, e2, Matrix.mul_assoc _ P, Matrix.mul_assoc _ (P * H), e1, Matrix.mul_assoc _ V,
      Matrix.mul_assoc _ (V * H), mul_nonsing_inv_cancel_right _ _ hu] at this
    simpa using this
  rw [y4, Matrix.zero_mul, sub_zero] at y3
  have y5 : P * H * Pᴴ = Y * S * (B * G * Bᴴ) := by
    rw [← e3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, y3, y1]
  nth_rewrite 1 [y5]
  rw [mul_nonsing_inv_cancel_right _ _ hd.isUnit, ← Matrix.mul_assoc, ← Matrix.mul_assoc, y3, y2, e3]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}

theorem exists_close (h : IsType Ψ) : ∃ C : ℝ, ∀ x : Ψ → ℂ, ∃ a : E, IsIntegral ℤ a ∧
    ∀ τ : Ψ, ‖τ.1 a + x τ‖ ≤ C := by
  obtain ⟨b, hb⟩ := basis_one h
  refine ⟨∑ i, ‖b i‖, fun x => ?_⟩
  obtain ⟨a, ha, e⟩ := (hb _).1 (ZSpan.floor b x).2
  refine ⟨-a, ha.neg, fun τ => le_trans ?_ (ZSpan.norm_fract_le b x)⟩
  refine le_trans (le_of_eq ?_) (norm_le_pi_norm _ τ)
  rw [ZSpan.fract_apply, e]
  simp [neg_add_eq_sub]

theorem quot_iso {N : ℕ} {n m : ℕ} {G : Matrix (Fin n) (Fin n) E} {V w : Matrix (Fin 1) (Fin n) E}
    {B : Matrix (Fin m) (Fin n) E} {S : Matrix (Fin n) (Fin m) E} (hG : Gᴴ = G)
    (hV : V * G * Vᴴ = 0) (hB : B * G * Vᴴ = 0)
    (hS : S * B = 1 - G * wᴴ * V - G * Vᴴ * w) {W : Matrix (Fin (N + 1)) (Fin n) E}
    (hW : IsoRows G W) : ∃ T : Matrix (Fin N) (Fin m) E, IsoRows (B * G * Bᴴ) T := by
  classical
  have hiso : W * G * Wᴴ = 0 := hW.2
  have hWi := Matrix.vecMul_injective_iff.2 hW.1
  have key : ∃ z : Matrix (Fin 1) (Fin n) E, ∀ t : Fin (N + 1) → E, t ᵥ* (W * G * zᴴ) = 0 →
      t ᵥ* (W * G * Vᴴ) = 0 ∧ (t ᵥ* (W * S) = 0 → t = 0) := by
    have main : ∀ t : Fin (N + 1) → E, t ᵥ* (W * G * Vᴴ) = 0 → t ᵥ* (W * S) = 0 →
        t ᵥ* W = (t ᵥ* (W * G * wᴴ)) ᵥ* V := fun t h1 h2 => by
      have h3 : W * S * B = W - W * G * wᴴ * V - W * G * Vᴴ * w := by
        rw [Matrix.mul_assoc, hS]; simp [Matrix.mul_sub, Matrix.mul_assoc]
      have := congrArg (fun Z => t ᵥ* Z) h3
      simp only [vecMul_sub] at this
      rw [← vecMul_vecMul t (W * S), h2, ← vecMul_vecMul t (W * G * Vᴴ), h1,
        ← vecMul_vecMul t (W * G * wᴴ)] at this
      simp only [zero_vecMul, sub_zero] at this
      exact sub_eq_zero.1 this.symm
    by_cases hv : ∃ s : Matrix (Fin 1) (Fin (N + 1)) E, s * W = V
    · obtain ⟨s, rfl⟩ := hv
      have h1 : W * G * (s * W)ᴴ = 0 := by
        rw [conjTranspose_mul, ← Matrix.mul_assoc, hiso, Matrix.zero_mul]
      refine ⟨w, fun t ht => ⟨by rw [h1, vecMul_zero], fun h2 => hWi ?_⟩⟩
      have := main t (by rw [h1, vecMul_zero]) h2
      simpa [ht] using this
    · refine ⟨V, fun t ht => ⟨ht, fun h2 => hWi ?_⟩⟩
      have h3 := main t ht h2
      generalize t ᵥ* (W * G * wᴴ) = α at h3
      by_cases hα : α 0 = 0
      · have : α = 0 := by ext i; rw [Subsingleton.elim i 0]; exact hα
        simpa [this] using h3
      · refine (hv ⟨Matrix.of fun _ => (α 0)⁻¹ • t, ?_⟩).elim
        ext i j
        have := congrFun h3 j
        rw [Subsingleton.elim i 0]
        change (((α 0)⁻¹ • t) ᵥ* W) j = _
        rw [smul_vecMul, Pi.smul_apply, this]
        simp [vecMul, dotProduct, hα]
  obtain ⟨z, hz⟩ := key
  have hr : N ≤ Module.finrank E (LinearMap.ker (W * G * zᴴ).vecMulLinear) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (W * G * zᴴ).vecMulLinear
    have h2 := Submodule.finrank_le (LinearMap.range (W * G * zᴴ).vecMulLinear)
    simp only [Module.finrank_fin_fun] at h1 h2
    omega
  obtain ⟨u, hu⟩ := exists_linearIndependent_of_le_finrank hr
  have hu' := hu.map' _ (Submodule.ker_subtype _)
  let U : Matrix (Fin N) (Fin (N + 1)) E := Matrix.of fun i => (u i).1
  have hUi : Function.Injective U.vecMul := Matrix.vecMul_injective_iff.2 hu'
  have hU : U * (W * G * zᴴ) = 0 := by ext i j; exact congrFun (u i).2 j
  have hUV : U * (W * G * Vᴴ) = 0 := by ext i j; exact congrFun (hz _ (u i).2).1 j
  refine ⟨U * (W * S), Matrix.vecMul_injective_iff.1 ?_, ?_⟩
  · change Function.Injective (U * (W * S)).vecMulLinear
    rw [injective_iff_map_eq_zero]
    intro c hc
    refine hUi ?_
    have := (hz (c ᵥ* U) (by rw [vecMul_vecMul, hU, vecMul_zero])).2
      (by rw [vecMul_vecMul]; exact hc)
    simpa using this
  · have h3 : U * (W * S) * B = U * W - U * W * G * wᴴ * V := by
      have : U * (W * (G * (Vᴴ * w))) = 0 := by
        simpa [Matrix.mul_assoc] using congrArg (fun Z => Z * w) hUV
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hS]; simp [Matrix.mul_sub, Matrix.mul_assoc, this]
    have h4 : U * (W * S) * B * G * Vᴴ = 0 := by
      rw [Matrix.mul_assoc _ B, Matrix.mul_assoc _ (B * G), hB, Matrix.mul_zero]
    have h5 : V * G * (U * W)ᴴ = 0 := by
      simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using congrArg conjTranspose hUV
    have h6 : U * W * G * (U * W)ᴴ = 0 := by
      rw [conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc U, Matrix.mul_assoc U, hiso]; simp
    have h7 : U * (W * S) * (B * G * Bᴴ) * (U * (W * S))ᴴ =
        U * (W * S) * B * G * (U * (W * S) * B)ᴴ := by
      rw [conjTranspose_mul _ B]; simp only [Matrix.mul_assoc]
    refine h7.trans ?_
    nth_rewrite 2 [h3]
    rw [conjTranspose_sub, conjTranspose_mul _ V, Matrix.mul_sub, ← Matrix.mul_assoc _ Vᴴ, h4, h3,
      Matrix.sub_mul, Matrix.sub_mul, h6, Matrix.mul_assoc _ V, Matrix.mul_assoc _ (V * G), h5]
    simp

omit [IsCMField E] in
theorem den_mul {α β γ : Type} [Fintype β] {a b : ℕ} {A : Matrix α β E} {B : Matrix β γ E}
    (hA : Den a A) (hB : Den b B) : Den (a * b) (A * B) := by
  have := intM_mul hA hB
  rwa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Nat.cast_mul] at this

omit [IsCMField E] in
theorem den_one {α β : Type} {A : Matrix α β E} (hA : IntM A) : Den 1 A := by
  simpa [Den] using hA

omit [IsCMField E] in
theorem den_dvd {α β : Type} {a b : ℕ} {A : Matrix α β E} (hA : Den a A) (h : a ∣ b) :
    Den b A := by
  obtain ⟨c, rfl⟩ := h
  have := RowExt.intM_nat c hA
  rwa [smul_smul, ← Nat.cast_mul, mul_comm] at this

omit [IsCMField E] in
theorem den_sub {α β : Type} {a : ℕ} {A B : Matrix α β E} (hA : Den a A) (hB : Den a B) :
    Den a (A - B) := fun i j => by
  rw [smul_sub]; exact (hA i j).sub (hB i j)

theorem den_conj {α β : Type} {a : ℕ} {A : Matrix α β E} (hA : Den a A) : Den a Aᴴ := by
  have := RowExt.intM_conj hA
  rwa [conjTranspose_smul, star_natCast] at this

omit [IsCMField E] in
theorem den_inv_smul {α β : Type} {a c : ℕ} (hc : 0 < c) {A : Matrix α β E} (hA : Den a A) :
    Den (a * c) ((c : E)⁻¹ • A) := by
  have hc0 : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  unfold Den
  rwa [smul_smul, Nat.cast_mul, mul_inv_cancel_right₀ hc0]

theorem exists_dual {n D c : ℕ} (hc : 0 < c) {G : Matrix (Fin n) (Fin n) E}
    {V : Matrix (Fin 1) (Fin n) E} {X : Matrix (Fin n) (Fin 1) E} (hG : Gᴴ = G) (h0 : G.det ≠ 0)
    (hD1 : Den D G) (hD2 : Den D G⁻¹) (hVi : IntM V) (hX : IntM X) (hVX : V * X = (c : E) • 1)
    (hV : V * G * Vᴴ = 0) : ∃ w : Matrix (Fin 1) (Fin n) E, Den (D * c * D * (D * c) * 2) w ∧
      V * G * wᴴ = 1 ∧ w * G * Vᴴ = 1 ∧ w * G * wᴴ = 0 := by
  have hc0 : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  obtain ⟨u, hu⟩ : ∃ u, u = ((c : E)⁻¹ • (G⁻¹ * X))ᴴ := ⟨_, rfl⟩
  have hud : Den (D * c) u := by
    have := den_conj (den_inv_smul hc (den_mul hD2 (den_one hX)))
    rwa [mul_one, ← hu] at this
  have h1 : V * G * uᴴ = 1 := by
    rw [hu, conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.mul_assoc,
      mul_nonsing_inv_cancel_left _ _ h0.isUnit, hVX, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have h2 : u * G * Vᴴ = 1 := by
    simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using congrArg conjTranspose h1
  obtain ⟨s, hs⟩ : ∃ s, s = ((2 : ℕ) : E)⁻¹ • (u * G * uᴴ) := ⟨_, rfl⟩
  have hsc : sᴴ = s := by
    simp [hs, conjTranspose_mul, hG, Matrix.mul_assoc]
  have hsd : Den (D * c * D * (D * c) * 2) s :=
    hs ▸ den_inv_smul two_pos (den_mul (den_mul hud hD1) (den_conj hud))
  have h3 : (u - s * V) * G * Vᴴ = 1 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, h2, Matrix.mul_assoc s, Matrix.mul_assoc s, hV]; simp
  refine ⟨u - s * V, den_sub (den_dvd hud ⟨D * (D * c) * 2, by ring⟩)
    (by simpa using den_mul hsd (den_one hVi)), ?_, h3, ?_⟩
  · simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using congrArg conjTranspose h3
  · rw [conjTranspose_sub, conjTranspose_mul, Matrix.mul_sub, ← Matrix.mul_assoc, h3, hsc,
      Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc s, Matrix.mul_assoc s, h1,
      Matrix.mul_one, Matrix.one_mul, hs, sub_sub, ← add_smul]
    norm_num

omit [NumberField E] [IsCMField E] in
theorem li_of_mul' {m n : ℕ} {B : Matrix (Fin m) (Fin n) E} (h : LinearIndependent E fun i => B i)
    {k : E} (hk : k ≠ 0) : LinearIndependent E fun i => (k • B) i := by
  refine li_of_mul (R := k⁻¹ • (1 : Matrix (Fin n) (Fin n) E)) ?_
  rwa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hk, one_smul, Matrix.mul_one]

omit [IsCMField E] in

theorem exists_span {n m : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
    (hn : n = m + Fintype.card κ) (R : Matrix κ (Fin n) E) (F : Matrix (Fin n) κ E)
    (h : R * F = 1) : ∃ (B : Matrix (Fin m) (Fin n) E) (S : Matrix (Fin n) (Fin m) E), IntM B ∧
      LinearIndependent E (fun i => B i) ∧ B * F = 0 ∧ S * B = 1 - F * R := by
  classical
  have hsurj : LinearMap.range F.vecMulLinear = ⊤ :=
    LinearMap.range_eq_top.2 fun y => ⟨y ᵥ* R, by simp [vecMul_vecMul, h]⟩
  have hr : Module.finrank E (LinearMap.ker F.vecMulLinear) = m := by
    have h1 := LinearMap.finrank_range_add_finrank_ker F.vecMulLinear
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card] at h1
    omega
  have hP : (1 - F * R) * F = 0 := by rw [Matrix.sub_mul, Matrix.mul_assoc, h]; simp
  generalize 1 - F * R = P at hP
  have hmem : ∀ i, P i ∈ LinearMap.ker F.vecMulLinear := fun i =>
    LinearMap.mem_ker.2 (congrFun hP i)
  have hker : ∀ x ∈ LinearMap.ker F.vecMulLinear, x ᵥ* F = 0 := fun x hx => LinearMap.mem_ker.1 hx
  generalize LinearMap.ker F.vecMulLinear = K at hr hmem hker
  let b := Module.finBasisOfFinrankEq E K hr
  let B : Matrix (Fin m) (Fin n) E := Matrix.of fun i => (b i).1
  have hBi : LinearIndependent E (fun i => B i) := by
    have := b.linearIndependent.map' K.subtype K.ker_subtype
    exact this
  have hBF : B * F = 0 := by ext i j; exact congrFun (hker _ (b i).2) j
  have hSB : (Matrix.of fun i j => b.repr ⟨_, hmem i⟩ j) * B = P := by
    ext i j
    have := congrFun (congrArg Subtype.val (b.sum_repr ⟨_, hmem i⟩)) j
    rw [Submodule.coe_sum, Finset.sum_apply] at this
    exact this
  generalize (Matrix.of fun i j => b.repr ⟨_, hmem i⟩ j) = S at hSB
  clear_value B
  obtain ⟨k, hk, hint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Fin m × Fin n => B p.1 p.2)
  have hk' : (k : E) ≠ 0 := by exact_mod_cast hk
  refine ⟨(k : E) • B, (k : E)⁻¹ • S, fun i j => ?_, ?_,
    by rw [Matrix.smul_mul, hBF, smul_zero], ?_⟩
  · simpa using hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
  · refine li_of_mul' hBi hk'
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hk', one_smul, hSB]

theorem exists_compl (m D b : ℕ) (hD : 0 < D) (hb : 0 < b) : ∃ D' : ℕ, 0 < D' ∧
    ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) E) (V w : Matrix (Fin 1) (Fin n) E), n = m + 2 →
    Gᴴ = G → G.det ≠ 0 → Den D G → Den D G⁻¹ → IntM V → Den b w → V * G * Vᴴ = 0 →
    V * G * wᴴ = 1 → w * G * Vᴴ = 1 → w * G * wᴴ = 0 →
    ∃ (B : Matrix (Fin m) (Fin n) E) (S : Matrix (Fin n) (Fin m) E), IntM B ∧ V * S = 0 ∧
      B * S = 1 ∧ B * G * Vᴴ = 0 ∧ S * B = 1 - G * wᴴ * V - G * Vᴴ * w ∧
      (B * G * Bᴴ).det ≠ 0 ∧ Den D' (B * G * Bᴴ) ∧ Den D' (B * G * Bᴴ)⁻¹ := by
  obtain ⟨c, C, hc, hprim⟩ := exists_nearly_primitive E m
  have hc0 : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨D * b * c * D * (D * b * c), by positivity,
    fun n G V w hn hG h0 hD1 hD2 hVi hw h1 h2 h3 h4 => ?_⟩
  obtain ⟨B₀, S₀, hB₀, hli, hBF, hSB⟩ := exists_span (E := E) (m := m) (by simpa using hn)
    (fromRows V w) (fromCols (G * wᴴ) (G * Vᴴ)) (by
      rw [fromRows_mul_fromCols]
      simp only [← Matrix.mul_assoc, h1, h2, h3, h4, fromBlocks_one])
  rw [fromCols_mul_fromRows, ← sub_sub] at hSB
  obtain ⟨a, ha, -, hBi, hpr⟩ := hprim _ B₀ hB₀ hli
  have hBF' : a * B₀ * fromCols (G * wᴴ) (G * Vᴴ) = 0 := by
    rw [Matrix.mul_assoc, hBF, Matrix.mul_zero]
  have hli' : LinearIndependent E fun i => (a * B₀) i := by
    refine Matrix.vecMul_injective_iff.1 fun x y e => ?_
    refine Matrix.vecMul_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det a).2 ha.isUnit) ?_
    refine Matrix.vecMul_injective_iff.2 hli ?_
    simpa [vecMul_vecMul] using e
  have hSB' : S₀ * a⁻¹ * (a * B₀) = 1 - G * wᴴ * V - G * Vᴴ * w := by
    rw [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ ha.isUnit, hSB]
  generalize a * B₀ = B at hBi hpr hBF' hli' hSB'
  generalize S₀ * a⁻¹ = S at hSB'
  obtain ⟨X, hX, hBX⟩ := RowExt.exists_right_inv (c : E) B hBi hli' hpr
  rw [mul_fromCols, ← fromCols_zero] at hBF'
  obtain ⟨e1, e2⟩ := (fromCols_ext_iff _ _ _ _).1 hBF'
  obtain ⟨P, hP⟩ : ∃ P, P = 1 - G * wᴴ * V - G * Vᴴ * w := ⟨_, rfl⟩
  have hPd : Den (D * b) P := by
    rw [hP]
    refine den_sub (den_sub (den_dvd (den_one fun i j => ?_) (one_dvd _)) ?_) ?_
    · rw [Matrix.one_apply]; split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    · simpa using den_mul (den_mul hD1 (den_conj hw)) (den_one hVi)
    · simpa using den_mul (den_mul hD1 (den_conj (den_one hVi))) hw
  have hBP : B * P = B := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc B (G * wᴴ),
      ← Matrix.mul_assoc B (G * Vᴴ), e1, e2]; simp
  have hVP : V * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub]
    simp only [← Matrix.mul_assoc, h1, h2]; simp
  have hPG : G * Pᴴ = P * G := by
    simp [hP, conjTranspose_mul, hG, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, sub_right_comm]
  rw [← hP] at hSB'
  have hS : S = (c : E)⁻¹ • (P * X) := by
    rw [← hSB', Matrix.mul_assoc, hBX]; simp [smul_smul, hc0]
  have hSd : Den (D * b * c) S := by
    have := den_inv_smul hc (den_mul hPd (den_one hX))
    rwa [mul_one, ← hS] at this
  have hBS : B * S = 1 := by
    rw [hS, Matrix.mul_smul, ← Matrix.mul_assoc, hBP, hBX]; simp [smul_smul, hc0]
  have hinv : B * G * Bᴴ * (Sᴴ * G⁻¹ * S) = 1 := by
    have : B * G * Bᴴ * (Sᴴ * G⁻¹ * S) = B * (G * (S * B)ᴴ) * G⁻¹ * S := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hSB', hPG, ← Matrix.mul_assoc, hBP, mul_nonsing_inv_cancel_right _ _ h0.isUnit, hBS]
  refine ⟨B, S, hBi, ?_, hBS, by rw [Matrix.mul_assoc, e2], by rw [hSB', hP],
    (isUnit_det_of_right_inverse hinv).ne_zero, ?_, ?_⟩
  · rw [hS, Matrix.mul_smul, ← Matrix.mul_assoc, hVP]; simp
  · exact den_dvd (den_mul (den_mul (den_one hBi) hD1) (den_conj (den_one hBi)))
      ⟨b * c * D * (D * b * c), by ring⟩
  · rw [inv_eq_right_inv hinv]
    exact den_mul (den_mul (den_conj hSd) hD2) hSd

theorem map_conj {α β : Type} (τ : E →+* ℂ) (A : Matrix α β E) : Aᴴ.map τ = (A.map τ)ᴴ :=
  Base.ccT_map τ A

omit [IsCMField E] in
theorem det_map_ne {α : Type} [Fintype α] [DecidableEq α] (τ : E →+* ℂ) {A : Matrix α α E}
    (h : A.det ≠ 0) : (A.map τ).det ≠ 0 := by
  rw [show (A.map τ).det = τ A.det from (RingHom.map_det _ _).symm]
  simpa using h

theorem map_proj {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (V w : Matrix (Fin 1) (Fin n) E) : (1 - G * wᴴ * V - G * Vᴴ * w).map τ =
      1 - G.map τ * (w.map τ)ᴴ * V.map τ - G.map τ * (V.map τ)ᴴ * w.map τ := by
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul,
    Matrix.map_mul, Matrix.map_mul, map_conj, map_conj, Matrix.map_one _ (map_zero _) (map_one _)]

theorem iso_of_short (h : IsType Ψ) {n D : ℕ} (hD : 0 < D) {G : Matrix (Fin n) (Fin n) E}
    {H : CM Ψ n n} (hG : Gᴴ = G) (h0 : G.det ≠ 0) (hD1 : Den D G) (hH : IsMaj Ψ G H)
    {V : Matrix (Fin 1) (Fin n) E} (hV : IntM V) (hs : ∀ τ, hval Ψ H τ (V 0) < 1 / D) :
    V * G * Vᴴ = 0 := by
  have hi := den_mul (den_mul (den_one hV) hD1) (den_conj (den_one hV)) 0 0
  have hD' : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  have hD'' : (0 : ℝ) < D := by exact_mod_cast hD
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  by_contra hne
  simp only [one_mul, mul_one, Matrix.smul_apply, smul_eq_mul] at hi
  have hne' := mul_ne_zero hD' hne
  have h1 := one_le_prod h hi hne'
  have hΨ : Nonempty Ψ := by
    have := card_type h
    have h2 := Module.finrank_pos (R := ℚ) (M := E)
    exact (Finset.card_pos.1 (by omega)).to_subtype
  have h2 : ∏ τ : Ψ, ‖τ.1 (D * (V * G * Vᴴ) 0 0)‖ < ∏ _τ : Ψ, (1 : ℝ) := by
    refine Finset.prod_lt_prod_of_nonempty (fun τ _ => norm_pos_iff.2 ((_root_.map_ne_zero _).2 hne')) (fun τ _ => ?_)
      Finset.univ_nonempty
    have h3 := gram_le (hH τ).1 (by rw [← map_conj, hG]) (det_map_ne τ.1 h0) (hH τ).2 _ _
      (le_of_eq (hval_eq H τ (V 0)).symm) (le_of_eq (hval_eq H τ (V 0)).symm)
    have h4 : τ.1 ((V * G * Vᴴ) 0 0) = ((fun a => τ.1 (V 0 a)) ⬝ᵥ G.map τ.1 *ᵥ
        star fun a => τ.1 (V 0 a)) := by
      rw [← Matrix.map_apply (f := τ.1), Matrix.map_mul, Matrix.map_mul, map_conj, Matrix.mul_assoc]
      rfl
    rw [map_mul, norm_mul, h4, map_natCast, Complex.norm_natCast]
    have := h3.trans_lt (hs τ)
    rwa [lt_div_iff₀' hD''] at this
  rw [Finset.prod_const_one] at h2
  exact absurd h1 h2.not_ge

theorem lift_le {n m : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef)
    (V : Matrix (Fin 1) (Fin n) ℂ) (B : Matrix (Fin m) (Fin n) ℂ) (L : Matrix (Fin m) (Fin 1) ℂ)
    (t : Fin m → ℂ) (α : ℂ) {C M : ℝ} (hM : 1 ≤ M) (h1 : (V 0 ⬝ᵥ H *ᵥ star (V 0)).re ≤ C)
    (h2 : (t ⬝ᵥ ((B - L * V) * H * (B - L * V)ᴴ) *ᵥ star t).re ≤ C)
    (h3 : ‖α + (t ᵥ* L) 0‖ ≤ M) :
    ((t ᵥ* B + α • V 0) ⬝ᵥ H *ᵥ star (t ᵥ* B + α • V 0)).re ≤ (2 * (M * √C)) ^ 2 := by
  have e : t ᵥ* B + α • V 0 = ∑ j, ![1, α + (t ᵥ* L) 0] j • ![t ᵥ* (B - L * V), V 0] j := by
    have : (t ᵥ* L) ᵥ* V = (t ᵥ* L) 0 • V 0 := by
      ext j; simp [vecMul, dotProduct]
    rw [Fin.sum_univ_two, vecMul_sub, ← vecMul_vecMul, this]
    simp [add_smul]
  rw [e]
  refine comb_le hH _ _ (fun j => ?_) fun j => ?_
  · fin_cases j
    · rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_vecMul] at h2
      exact h2
    · exact h1
  · fin_cases j
    · simpa using hM
    · exact h3

end GlobalTheory.SW.ShortStep

open GlobalTheory.SW.MinkowskiProductBounds GlobalTheory.SW.ShortStep in

theorem GlobalTheory.SW.shortIso_step : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N : ℕ, (∀ D : ℕ, 0 < D → ∃ C : ℝ, ShortIso Ψ N D 0 C) → (∀ (D : ℕ) (ε : ℝ), 0 < D → 0 < ε → ∃ C : ℝ, ShortIso Ψ (N + 1) D ε C) → ∀ D : ℕ, 0 < D → ∃ C : ℝ, ShortIso Ψ (N + 1) D 0 C := by
  intro E _ _ _ Ψ h N ih hth D hD
  classical
  obtain ⟨C₀, hC₀⟩ := hth D (1 / D) hD (by positivity)
  obtain ⟨c, C₁, hc, hprim⟩ := exists_nearly_primitive E 1
  obtain ⟨D', hD', hcompl⟩ := exists_compl (E := E) (2 * N) D (D * c * D * (D * c) * 2) hD
    (by positivity)
  obtain ⟨C₂, hC₂⟩ := ih D' hD'
  obtain ⟨C₃, hC₃⟩ := exists_close h
  set C₄ := max (((1 : ℕ) * (C₁ * √(1 / D))) ^ 2) C₂ with hC₄
  refine ⟨max (max C₀ C₄) ((2 * (max 1 C₃ * √C₄)) ^ 2),
    fun G H hG h0 hD1 hD2 ⟨W, hW⟩ hH _ => ?_⟩
  by_cases hmin : ∀ v : Fin (2 * (N + 1)) → E, v ≠ 0 → (∀ a, IsIntegral ℤ (v a)) →
      1 / (D : ℝ) ≤ ∑ τ, hval Ψ H τ v
  · obtain ⟨W', h1, h2, h3⟩ := hC₀ G H hG h0 hD1 hD2 ⟨W, hW⟩ hH hmin
    exact ⟨W', h1, h2, fun i τ => (h3 i τ).trans ((le_max_left _ _).trans (le_max_left _ _))⟩
  push Not at hmin
  obtain ⟨v, hv0, hvi, hvs⟩ := hmin
  have hG' : Gᴴ = G := hG
  have hnn : ∀ {k : ℕ} {K : CM Ψ k k}, (∀ τ, (K τ).PosDef) → ∀ τ x, 0 ≤ hval Ψ K τ x := by
    intro k K hK τ x
    obtain ⟨B, -, -, h3⟩ := fac (hK τ)
    rw [hval_eq, h3]; positivity
  let V₀ : Matrix (Fin 1) (Fin (2 * (N + 1))) E := Matrix.of fun _ => v
  have hs : ∀ τ, hval Ψ H τ (V₀ 0) < 1 / D := fun τ =>
    (Finset.single_le_sum (f := fun τ => hval Ψ H τ v)
      (fun τ _ => hnn (fun τ => (hH τ).1) τ v) (Finset.mem_univ τ)).trans_lt hvs
  have hV₀ := iso_of_short h hD hG' h0 hD1 hH (V := V₀) (fun _ a => hvi a) hs
  obtain ⟨a, ha, haC, hVi, hpr⟩ := hprim _ V₀ (fun _ a => hvi a)
    (linearIndependent_unique_iff.2 hv0)
  have hV : a * V₀ * G * (a * V₀)ᴴ = 0 := by
    rw [conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc a, Matrix.mul_assoc a, hV₀]; simp
  have hVne : (a * V₀) 0 ≠ 0 := by
    rw [det_fin_one] at ha
    have : (a * V₀) 0 = a 0 0 • v := by ext j; simp [Matrix.mul_apply, V₀]
    rw [this]
    exact smul_ne_zero ha hv0
  have hVC : ∀ τ, hval Ψ H τ ((a * V₀) 0) ≤ C₄ := fun τ => by
    have h1 : (fun j => τ.1 ((a * V₀) 0 j)) = ∑ j, τ.1 (a 0 j) • fun b => τ.1 (V₀ j b) := by
      ext j
      simp [Matrix.mul_apply]
    rw [hval_eq, h1]
    exact (comb_le (hH τ).1 _ _ (fun j => (hs τ).le) fun j => haC _ _ _).trans (le_max_left _ _)
  generalize a * V₀ = V at hVi hpr hV hVne hVC
  obtain ⟨X, hX, hVX⟩ := RowExt.exists_right_inv (c : E) V hVi
    (linearIndependent_unique_iff.2 hVne) hpr
  obtain ⟨w, hw, w1, w2, w3⟩ := exists_dual hc hG' h0 hD1 hD2 hVi hX hVX hV
  obtain ⟨B, S, hBi, hVS, hBS, hBV, hSB, hd, d1, d2⟩ :=
    hcompl _ G V w (by ring) hG' h0 hD1 hD2 hVi hw hV w1 w2 w3
  have hq := fun τ : Ψ => quot_maj (G := G.map τ.1) (H := H τ) (V := V.map τ.1) (w := w.map τ.1)
    (B := B.map τ.1) (S := S.map τ.1) (by rw [← map_conj, hG']) (det_map_ne τ.1 h0) (hH τ).1
    (hH τ).2
    (by rw [← map_conj, ← Matrix.map_mul, ← Matrix.map_mul, w1,
      Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [← map_conj, ← Matrix.map_mul, ← Matrix.map_mul, hV, Matrix.map_zero _ (map_zero _)])
    (by rw [← map_conj, ← Matrix.map_mul, ← Matrix.map_mul, hBV, Matrix.map_zero _ (map_zero _)])
    (by rw [← Matrix.map_mul, hSB, map_proj])
    (by rw [← map_conj, ← Matrix.map_mul, ← Matrix.map_mul]; exact det_map_ne τ.1 hd)
  choose L hL1 hL2 using hq
  obtain ⟨T, hTi, ⟨hT1, hT2⟩, hTC⟩ := hC₂ (B * G * Bᴴ)
    (fun τ => (B.map τ.1 - L τ * V.map τ.1) * H τ * (B.map τ.1 - L τ * V.map τ.1)ᴴ)
    (by
      rw [RowExt.ccT_eq, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG',
        Matrix.mul_assoc])
    hd d1 d2 (quot_iso hG' hV hBV hSB hW)
    (fun τ => ⟨hL1 τ, by rw [Matrix.map_mul, Matrix.map_mul, map_conj]; exact hL2 τ⟩)
    (fun x _ _ => Finset.sum_nonneg fun τ _ => hnn hL1 τ x)
  choose α hα hαC using fun i => hC₃ fun τ => ((fun j => τ.1 (T i j)) ᵥ* L τ) 0
  let T' : Matrix (Fin (N + 1)) (Fin (2 * N)) E := Matrix.of (Fin.cons 0 fun i => T i)
  let A : Matrix (Fin (N + 1)) (Fin 1) E := Matrix.of (Fin.cons 1 fun i _ => α i)
  have r0 : (T' * B + A * V) 0 = V 0 := by
    ext j; simp [T', A, Matrix.mul_apply]
  have r1 : ∀ i : Fin N, (T' * B + A * V) i.succ = T i ᵥ* B + α i • V 0 := fun i => by
    ext j; simp [T', A, Matrix.mul_apply, vecMul, dotProduct]
  refine ⟨T' * B + A * V, fun i j => ?_, ⟨?_, ?_⟩, fun i τ => ?_⟩
  · refine (intM_mul (A := T') (fun i j => ?_) hBi i j).add
      (intM_mul (A := A) (fun i j => ?_) hVi i j)
    · cases i using Fin.cases
      · exact isIntegral_zero
      · exact hTi _ _
    · cases i using Fin.cases
      · exact isIntegral_one
      · exact hα _
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_succ, r0] at hg
    simp only [r1] at hg
    have hVS' : V 0 ᵥ* S = 0 := congrFun hVS 0
    have h1 := congrArg (fun x => x ᵥ* S) hg
    simp only [add_vecMul, sum_vecMul, smul_vecMul, vecMul_vecMul, hBS, hVS', vecMul_one,
      smul_zero, add_zero, zero_add, zero_vecMul] at h1
    have h2 := Fintype.linearIndependent_iff.1 hT1 _ h1
    simp only [h2, zero_smul, Finset.sum_const_zero, add_zero] at hg
    intro i
    cases i using Fin.cases
    · exact (smul_eq_zero.1 hg).resolve_right hVne
    · exact h2 _
  · have hVB : V * G * Bᴴ = 0 := by
      simpa [conjTranspose_mul, hG', Matrix.mul_assoc] using congrArg conjTranspose hBV
    have h1 : T' * (B * G * Bᴴ) * T'ᴴ = 0 := by
      generalize B * G * Bᴴ = G' at hT2
      ext i j
      cases i using Fin.cases
      · simp [T', Matrix.mul_apply]
      cases j using Fin.cases
      · simp [T', Matrix.mul_apply]
      · exact congrFun (congrFun hT2 _) _
    have h2 : (T' * B + A * V) * G * (T' * B + A * V)ᴴ = T' * (B * G * Bᴴ) * T'ᴴ +
        T' * (B * G * Vᴴ) * Aᴴ + A * (V * G * Bᴴ) * T'ᴴ + A * (V * G * Vᴴ) * Aᴴ := by
      simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add,
        Matrix.mul_assoc]
      abel
    refine h2.trans ?_
    rw [h1, hBV, hVB, hV]; simp
  · cases i using Fin.cases with
    | zero => rw [r0]; exact (hVC τ).trans ((le_max_right _ _).trans (le_max_left _ _))
    | succ i =>
      refine le_trans ?_ (le_max_right _ _)
      have e : (fun j => τ.1 ((T i ᵥ* B + α i • V 0) j)) =
          (fun j => τ.1 (T i j)) ᵥ* B.map τ.1 + τ.1 (α i) • V.map τ.1 0 := by
        ext j; simp [vecMul, dotProduct]
      rw [r1, hval_eq, e]
      exact lift_le (hH τ).1 _ _ (L τ) _ _ (le_max_left _ _) (hVC τ)
        ((hTC i τ).trans (le_max_right _ _)) ((hαC i τ).trans (le_max_right _ _))

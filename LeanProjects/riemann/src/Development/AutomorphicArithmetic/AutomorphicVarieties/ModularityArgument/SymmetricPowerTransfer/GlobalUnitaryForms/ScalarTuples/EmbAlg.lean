import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open Matrix

section Coord

variable {K : Type} [Field K] {Δ : K}

private def Q (Δ a b c d : K) : Matrix (Fin 2) (Fin 2) (Lsq K Δ) :=
  !![⟨a, b⟩, ⟨c, d⟩; ⟨-c, d⟩, ⟨a, -b⟩]

private theorem Q_mul (a b c d a' b' c' d' : K) :
    Q Δ a b c d * Q Δ a' b' c' d' =
      Q Δ (a * a' + Δ * b * b' - c * c' + Δ * d * d') (a * b' + b * a' - d * c' + c * d')
        (a * c' + Δ * b * d' + c * a' - Δ * d * b') (a * d' + b * c' + d * a' - c * b') := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> ext <;> simp [Q, Matrix.mul_apply] <;> ring

private theorem Q_det (a b c d : K) :
    (Q Δ a b c d).det = algebraMap K _ (a ^ 2 - Δ * b ^ 2 + c ^ 2 - Δ * d ^ 2) := by
  rw [Matrix.det_fin_two]
  ext <;> simp [Q, pow_two] <;> ring

private theorem Q_trace (a b c d : K) : (Q Δ a b c d).trace = algebraMap K _ (2 * a) := by
  rw [Matrix.trace_fin_two]
  ext <;> simp [Q] <;> ring

private theorem Q_inj {a b c d a' b' c' d' : K} (h : Q Δ a b c d = Q Δ a' b' c' d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 0) 1
  simp [Q] at h0 h1
  exact ⟨h0.1, h0.2, h1.1, h1.2⟩

private theorem mem_DX_iff (g : GL (Fin 2) (Lsq K Δ)) :
    g ∈ DX Δ ↔ ∃ a b c d, (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = Q Δ a b c d := by
  have key : g ∈ DX Δ ↔ ∀ i j, star ((g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j) =
      ((((wJ Δ)⁻¹ * g * ((wJ Δ)⁻¹)⁻¹ : GL (Fin 2) (Lsq K Δ))) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j := by
    constructor
    · intro h i j
      exact congrArg (fun x : GL (Fin 2) (Lsq K Δ) => (x : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j) h
    · intro h
      show GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g = (MulAut.conj (wJ Δ)⁻¹).toMonoidHom g
      exact Units.ext (Matrix.ext fun i j => h i j)
  rw [key]
  have winv : (((wJ Δ)⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![0, -1; 1, 0] := rfl
  have w : ((wJ Δ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![0, 1; -1, 0] := rfl
  have hg := Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ))
  simp only [inv_inv, Units.val_mul, winv, w]
  rw [hg]
  simp only [Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, zero_mul, one_mul, neg_mul, mul_zero, mul_one, mul_neg,
    zero_add, add_zero, neg_zero, neg_neg]
  set p := (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0
  set q := (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 1
  set r := (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 1 0
  set s := (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 1 1
  constructor
  · intro h
    have h00 := h 0 0
    have h01 := h 0 1
    simp at h00 h01
    have hr : r = -star q := by rw [h01, neg_neg]
    refine ⟨p.re, p.im, q.re, q.im, ?_⟩
    rw [hr, ← h00]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> ext <;> simp [Q]
  · rintro ⟨a, b, c, d, e⟩ i j
    have ep := congrFun (congrFun e 0) 0
    have eq := congrFun (congrFun e 0) 1
    have er := congrFun (congrFun e 1) 0
    have es := congrFun (congrFun e 1) 1
    simp [Q] at ep eq er es
    rw [ep, eq, er, es]
    fin_cases i <;> fin_cases j <;> ext <;> simp

private theorem Q_one : Q Δ 1 0 0 0 = 1 := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> ext <;> simp [Q, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem Q_lin (x y a b c d : K) :
    x • (1 : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) + y • Q Δ a b c d =
      Q Δ (x + y * a) (y * b) (y * c) (y * d) := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> ext <;> simp [Q, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> ring

private theorem DX_ext {g h : DX Δ} (e : mt g = mt h) : g = h := Subtype.ext (Units.ext e)

private theorem DX_of {a b c d : K} (h : a ^ 2 - Δ * b ^ 2 + c ^ 2 - Δ * d ^ 2 ≠ 0) :
    ∃ g : DX Δ, mt g = Q Δ a b c d := by
  have h1 : Q Δ a b c d * Q Δ (a / (a ^ 2 - Δ * b ^ 2 + c ^ 2 - Δ * d ^ 2)) (-b / (a ^ 2 - Δ * b ^ 2 + c ^ 2 - Δ * d ^ 2))
      (-c / (a ^ 2 - Δ * b ^ 2 + c ^ 2 - Δ * d ^ 2)) (-d / (a ^ 2 - Δ * b ^ 2 + c ^ 2 - Δ * d ^ 2)) = 1 := by
    rw [Q_mul, ← Q_one]
    congr 1 <;> field_simp <;> ring
  have h2 : Q Δ (a / (a ^ 2 - Δ * b ^ 2 + c ^ 2 - Δ * d ^ 2)) (-b / (a ^ 2 - Δ * b ^ 2 + c ^ 2 - Δ * d ^ 2))
      (-c / (a ^ 2 - Δ * b ^ 2 + c ^ 2 - Δ * d ^ 2)) (-d / (a ^ 2 - Δ * b ^ 2 + c ^ 2 - Δ * d ^ 2)) * Q Δ a b c d = 1 := by
    rw [Q_mul, ← Q_one]
    congr 1 <;> field_simp <;> ring
  let g : GL (Fin 2) (Lsq K Δ) := ⟨_, _, h1, h2⟩
  have hg : g ∈ DX Δ := (mem_DX_iff g).2 ⟨a, b, c, d, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

private theorem alg_inj {x y : K} (h : algebraMap K (Lsq K Δ) x = algebraMap K (Lsq K Δ) y) : x = y := by
  simpa using congrArg QuadraticAlgebra.re h

private theorem coords {τ : K} {γ : DX Δ} (h : HasTr γ τ) :
    ∃ a b c d, mt γ = Q Δ a b c d ∧ 2 * a = τ ∧ a ^ 2 - Δ * b ^ 2 + c ^ 2 - Δ * d ^ 2 = 1 := by
  obtain ⟨a, b, c, d, e⟩ := (mem_DX_iff γ.1).1 γ.2
  have e' : mt γ = Q Δ a b c d := e
  refine ⟨a, b, c, d, e', ?_, ?_⟩
  · have := h.2
    rw [e', Q_trace] at this
    exact alg_inj this
  · have := h.1
    rw [e', Q_det, ← map_one (algebraMap K (Lsq K Δ))] at this
    exact alg_inj this

private theorem mul_pure_eq_zero {n b c d i : K} (hn : n ≠ 0) (h : Δ * b ^ 2 - c ^ 2 + Δ * d ^ 2 = n)
    (hb : i * b = 0) (hc : i * c = 0) (hd : i * d = 0) : i = 0 := by
  have hz : i * n = 0 := by
    rw [← h]
    linear_combination (Δ * b) * hb - c * hc + (Δ * d) * hd
  exact (mul_eq_zero.1 hz).resolve_right hn

private theorem exists_emb {τ : K} {γ : DX Δ} (h : HasTr γ τ) : ∃ j, IsEmb τ γ j := by
  obtain ⟨a, b, c, d, e, hτ, hN⟩ := coords h
  have hu : Q Δ a b c d * Q Δ a b c d = (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) + τ • Q Δ a b c d := by
    rw [Q_mul, Q_lin]
    congr 1
    · linear_combination (-1) * hN + a * hτ
    · linear_combination b * hτ
    · linear_combination c * hτ
    · linear_combination d * hτ
  let φ : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) (Lsq K Δ) := QuadraticAlgebra.lift ⟨Q Δ a b c d, hu⟩
  have hφ : ∀ z : Etau K τ, φ z = z.re • (1 : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) + z.im • Q Δ a b c d := by
    intro z
    simp [φ]
  let j : (Etau K τ)ˣ →* DX Δ := (Units.map (φ : Etau K τ →* Matrix (Fin 2) (Fin 2) (Lsq K Δ))).codRestrict (DX Δ)
    (fun z => (mem_DX_iff _).2 ⟨_, _, _, _, by
      show φ (z : Etau K τ) = _
      rw [hφ, Q_lin]⟩)
  refine ⟨j, fun z => ?_⟩
  show φ (z : Etau K τ) = _
  rw [hφ, show mt γ = Q Δ a b c d from e]

private theorem Q_congr {a b c d a' b' c' d' : K} (h0 : a = a') (h1 : b = b') (h2 : c = c') (h3 : d = d') :
    Q Δ a b c d = Q Δ a' b' c' d' := by
  subst h0 h1 h2 h3
  rfl

private theorem emb_coord {τ a b c d : K} {γ : DX Δ} {j : (Etau K τ)ˣ →* DX Δ} (e : mt γ = Q Δ a b c d)
    (hj : IsEmb τ γ j) (z : (Etau K τ)ˣ) :
    mt (j z) = Q Δ ((z : Etau K τ).re + (z : Etau K τ).im * a) ((z : Etau K τ).im * b)
      ((z : Etau K τ).im * c) ((z : Etau K τ).im * d) := by
  rw [hj z, e, Q_lin]

private theorem emb_inj {τ : K} (hτ : τ ^ 2 - 4 ≠ 0) {γ : DX Δ} (h : HasTr γ τ)
    {j : (Etau K τ)ˣ →* DX Δ} (hj : IsEmb τ γ j) : Function.Injective j := by
  obtain ⟨a, b, c, d, e, ha, hN⟩ := coords h
  have hn : a ^ 2 - 1 ≠ 0 := fun h0 => hτ (by rw [← ha]; linear_combination 4 * h0)
  intro z w hzw
  have hz := emb_coord e hj z
  rw [hzw, emb_coord e hj w] at hz
  obtain ⟨h0, h1, h2', h3⟩ := Q_inj hz
  have hi : (w : Etau K τ).im - (z : Etau K τ).im = 0 :=
    mul_pure_eq_zero (Δ := Δ) (b := b) (c := c) (d := d) hn (by linear_combination -hN)
      (by linear_combination h1) (by linear_combination h2') (by linear_combination h3)
  have hi' : (w : Etau K τ).im = (z : Etau K τ).im := sub_eq_zero.1 hi
  rw [hi'] at h0
  exact Units.ext (QuadraticAlgebra.ext (add_right_cancel h0).symm hi'.symm)

private theorem cent_coord {n b c d x1 x2 x3 : K} (hn : n ≠ 0) (hnn : Δ * b ^ 2 - c ^ 2 + Δ * d ^ 2 = n)
    (hΔ : Δ * (x1 * d - x3 * b) = 0) (e1 : x2 * d - x3 * c = 0) (e3 : x1 * c - x2 * b = 0) :
    ∃ β, x1 = β * b ∧ x2 = β * c ∧ x3 = β * d := by
  subst hnn
  refine ⟨(Δ * x1 * b - x2 * c + Δ * x3 * d) / (Δ * b ^ 2 - c ^ 2 + Δ * d ^ 2), ?_, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, eq_div_iff hn]
    linear_combination (-c) * e3 + d * hΔ
  · rw [div_mul_eq_mul_div, eq_div_iff hn]
    linear_combination (-Δ * b) * e3 + (Δ * d) * e1
  · rw [div_mul_eq_mul_div, eq_div_iff hn]
    linear_combination (-b) * hΔ + c * e1

private theorem emb_range {τ : K} (hτ : τ ^ 2 - 4 ≠ 0) (h2 : (2 : K) ≠ 0) {γ : DX Δ} (h : HasTr γ τ)
    {j : (Etau K τ)ˣ →* DX Δ} (hj : IsEmb τ γ j) (x : DX Δ) : x ∈ j.range ↔ x * γ = γ * x := by
  obtain ⟨a, b, c, d, e, ha, hN⟩ := coords h
  have hn : a ^ 2 - 1 ≠ 0 := by
    intro h0
    apply hτ
    rw [← ha]
    linear_combination 4 * h0
  have hnn : Δ * b ^ 2 - c ^ 2 + Δ * d ^ 2 = a ^ 2 - 1 := by linear_combination (-1) * hN
  constructor
  · rintro ⟨z, rfl⟩
    apply DX_ext
    show mt (j z) * mt γ = mt γ * mt (j z)
    rw [emb_coord e hj, e, Q_mul, Q_mul]
    congr 1 <;> ring
  · intro hx
    obtain ⟨x0, x1, x2, x3, ex⟩ := (mem_DX_iff x.1).1 x.2
    have hm : mt x * mt γ = mt γ * mt x := congrArg mt hx
    rw [show mt x = Q Δ x0 x1 x2 x3 from ex, e, Q_mul, Q_mul] at hm
    obtain ⟨k0, k1, k2, k3⟩ := Q_inj hm
    have e1 : x2 * d - x3 * c = 0 := mul_left_cancel₀ h2 (by linear_combination k1)
    have eΔ : Δ * (x1 * d - x3 * b) = 0 := mul_left_cancel₀ h2 (by linear_combination k2)
    have e3 : x1 * c - x2 * b = 0 := mul_left_cancel₀ h2 (by linear_combination k3)
    obtain ⟨β, hx1, hx2, hx3⟩ := cent_coord hn hnn eΔ e1 e3
    have hdet : IsUnit (mt x).det := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.isUnit _
    rw [show mt x = Q Δ x0 x1 x2 x3 from ex, Q_det] at hdet
    have hNx : x0 ^ 2 - Δ * x1 ^ 2 + x2 ^ 2 - Δ * x3 ^ 2 ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hdet
      exact not_isUnit_zero hdet
    let zz : Etau K τ := ⟨x0 - β * a, β⟩
    have hnorm : QuadraticAlgebra.norm zz = x0 ^ 2 - Δ * x1 ^ 2 + x2 ^ 2 - Δ * x3 ^ 2 := by
      simp only [QuadraticAlgebra.norm, MonoidHom.coe_mk, OneHom.coe_mk, zz]
      rw [hx1, hx2, hx3]
      linear_combination β ^ 2 * hnn - ((x0 - β * a) * β) * ha
    have hu : IsUnit zz := QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (by rw [hnorm]; exact hNx.isUnit)
    refine ⟨hu.unit, ?_⟩
    apply DX_ext
    rw [emb_coord e hj, show mt x = Q Δ x0 x1 x2 x3 from ex]
    simp only [IsUnit.unit_spec, zz]
    rw [hx1, hx2, hx3]
    congr 1
    ring

private theorem scal_val (u : Kˣ) :
    ((((GeneralLinearGroup.scalar (Fin 2)).comp (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ))) u :
      GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = Q Δ u 0 0 0 := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> ext <;> simp [Q]

private theorem emb_centre {τ : K} (hτ : τ ^ 2 - 4 ≠ 0) {γ : DX Δ} (h : HasTr γ τ)
    {j : (Etau K τ)ˣ →* DX Δ} (hj : IsEmb τ γ j) : (ZD Δ).comap j = scalE τ := by
  obtain ⟨a, b, c, d, e, ha, hN⟩ := coords h
  have hn : a ^ 2 - 1 ≠ 0 := fun h0 => hτ (by rw [← ha]; linear_combination 4 * h0)
  ext z
  rw [Subgroup.mem_comap]
  constructor
  · intro hz
    obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.1 hz
    have hm : mt (j z) = Q Δ u 0 0 0 := by
      rw [← scal_val u]
      exact (congrArg Units.val hu).symm
    rw [emb_coord e hj z] at hm
    obtain ⟨h0, h1, h2, h3⟩ := Q_inj hm
    have hi : (z : Etau K τ).im = 0 :=
      mul_pure_eq_zero (Δ := Δ) (b := b) (c := c) (d := d) hn (by linear_combination -hN) h1 h2 h3
    rw [hi, zero_mul, add_zero] at h0
    refine ⟨u, Units.ext ?_⟩
    ext
    · simpa using h0.symm
    · simpa using hi.symm
  · rintro ⟨u, rfl⟩
    refine Subgroup.mem_subgroupOf.2 ⟨u, Units.ext ?_⟩
    change _ = mt (j _)
    rw [scal_val, emb_coord e hj]
    refine Q_congr ?_ ?_ ?_ ?_ <;> simp

private theorem exists_orth (h2 : (2 : K) ≠ 0) (hΔ : Δ ≠ 0) {b c d n : K} (hn : n ≠ 0)
    (hu : Δ * b ^ 2 - c ^ 2 + Δ * d ^ 2 = n) :
    ∃ p q r, Δ * b * p - c * q + Δ * d * r = 0 ∧ -Δ * p ^ 2 + q ^ 2 - Δ * r ^ 2 ≠ 0 := by
  by_contra H
  push_neg at H
  have E1 := H c (Δ * b) 0 (by ring)
  have E2 := H d 0 (-b) (by ring)
  have E3 := H 0 (Δ * d) c (by ring)
  have E23 := H d (Δ * d) (c - b) (by ring)
  have hc1 : Δ * (c ^ 2 - Δ * b ^ 2) = 0 := by linear_combination -E1
  have hc1' : c ^ 2 - Δ * b ^ 2 = 0 := (mul_eq_zero.1 hc1).resolve_left hΔ
  have hc3 : Δ * (Δ * d ^ 2 - c ^ 2) = 0 := by linear_combination E3
  have hc3' : Δ * d ^ 2 - c ^ 2 = 0 := (mul_eq_zero.1 hc3).resolve_left hΔ
  have hbc : (2 * Δ) * (b * c) = 0 := by linear_combination E23 - E2 - E3
  have hbc' : b * c = 0 := (mul_eq_zero.1 hbc).resolve_left (mul_ne_zero h2 hΔ)
  have hc4 : c ^ 4 = 0 := by linear_combination c ^ 2 * hc1' + (Δ * b * c) * hbc'
  have hc0 : c = 0 := pow_eq_zero_iff (by norm_num) |>.1 hc4
  apply hn
  linear_combination -hu - hc1' + hc3' + c * hc0

private theorem conj_core (h2 : (2 : K) ≠ 0) (hΔ : Δ ≠ 0) {b c d b' c' d' n : K} (hn : n ≠ 0)
    (hu : Δ * b ^ 2 - c ^ 2 + Δ * d ^ 2 = n) (hv : Δ * b' ^ 2 - c' ^ 2 + Δ * d' ^ 2 = n) :
    ∃ x0 x1 x2 x3, x0 ^ 2 - Δ * x1 ^ 2 + x2 ^ 2 - Δ * x3 ^ 2 ≠ 0 ∧
      Q Δ 0 b c d * Q Δ x0 x1 x2 x3 = Q Δ x0 x1 x2 x3 * Q Δ 0 b' c' d' := by
  by_cases hs : (0 : K) ^ 2 - Δ * (b + b') ^ 2 + (c + c') ^ 2 - Δ * (d + d') ^ 2 = 0
  · obtain ⟨p, q, r, horth, hY⟩ := exists_orth h2 hΔ hn hv
    have hX1 : (0 : K) ^ 2 - Δ * (b - b') ^ 2 + (c - c') ^ 2 - Δ * (d - d') ^ 2 ≠ 0 := by
      intro h0
      apply hn
      have h4 : (2 * 2 : K) * n = 0 := by linear_combination -hs - h0 - 2 * hu - 2 * hv
      exact (mul_eq_zero.1 h4).resolve_left (mul_ne_zero h2 h2)
    have hA : Q Δ 0 b c d * Q Δ 0 (b - b') (c - c') (d - d') =
        Q Δ 0 (b - b') (c - c') (d - d') * Q Δ 0 (-b') (-c') (-d') := by
      rw [Q_mul, Q_mul]
      congr 1
      · linear_combination hu - hv
      · ring
      · ring
      · ring
    have hB : Q Δ 0 (-b') (-c') (-d') * Q Δ 0 p q r = Q Δ 0 p q r * Q Δ 0 b' c' d' := by
      rw [Q_mul, Q_mul]
      congr 1
      · linear_combination -2 * horth
      · ring
      · ring
      · ring
    refine ⟨0 * 0 + Δ * (b - b') * p - (c - c') * q + Δ * (d - d') * r,
      0 * p + (b - b') * 0 - (d - d') * q + (c - c') * r,
      0 * q + Δ * (b - b') * r + (c - c') * 0 - Δ * (d - d') * p,
      0 * r + (b - b') * q + (d - d') * 0 - (c - c') * p, ?_, ?_⟩
    · have e : (0 * 0 + Δ * (b - b') * p - (c - c') * q + Δ * (d - d') * r) ^ 2 -
          Δ * (0 * p + (b - b') * 0 - (d - d') * q + (c - c') * r) ^ 2 +
          (0 * q + Δ * (b - b') * r + (c - c') * 0 - Δ * (d - d') * p) ^ 2 -
          Δ * (0 * r + (b - b') * q + (d - d') * 0 - (c - c') * p) ^ 2 =
          ((0 : K) ^ 2 - Δ * (b - b') ^ 2 + (c - c') ^ 2 - Δ * (d - d') ^ 2) *
          (-Δ * p ^ 2 + q ^ 2 - Δ * r ^ 2) := by ring
      rw [e]
      exact mul_ne_zero hX1 hY
    · rw [← Q_mul, ← mul_assoc, hA, mul_assoc, hB, ← mul_assoc]
  · refine ⟨0, b + b', c + c', d + d', hs, ?_⟩
    rw [Q_mul, Q_mul]
    congr 1
    · linear_combination hu - hv
    · ring
    · ring
    · ring

private theorem conj_main {τ : K} (hτ : τ ^ 2 - 4 ≠ 0) (h2 : (2 : K) ≠ 0) (hΔ : Δ ≠ 0) {γ γ' : DX Δ}
    (h : HasTr γ τ) (h' : HasTr γ' τ) : ∃ x, γ' = x⁻¹ * γ * x := by
  obtain ⟨a, b, c, d, e, ha, hN⟩ := coords h
  obtain ⟨a', b', c', d', e', ha', hN'⟩ := coords h'
  obtain rfl : a' = a := mul_left_cancel₀ h2 (ha'.trans ha.symm)
  have hn : a' ^ 2 - 1 ≠ 0 := fun h0 => hτ (by rw [← ha]; linear_combination 4 * h0)
  obtain ⟨x0, x1, x2, x3, hx, hm⟩ := conj_core h2 hΔ hn (b := b) (c := c) (d := d) (b' := b') (c' := c')
    (d' := d') (by linear_combination -hN) (by linear_combination -hN')
  obtain ⟨x, ex⟩ := DX_of hx
  refine ⟨x, ?_⟩
  have hc : γ * x = x * γ' := by
    apply DX_ext
    change mt γ * mt x = mt x * mt γ'
    rw [e, e', ex, Q_mul, Q_mul]
    rw [Q_mul, Q_mul] at hm
    obtain ⟨q0, q1, q2, q3⟩ := Q_inj hm
    refine Q_congr ?_ ?_ ?_ ?_
    · linear_combination q0
    · linear_combination q1
    · linear_combination q2
    · linear_combination q3
  rw [mul_assoc, hc, inv_mul_cancel_left]

end Coord

end UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Glob.embAlg :
    UpperTheory.V.Z.Sym.Glob.EmbAlg := by
  intro K _ _ Δ τ hΔ hτ γ hγ
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  exact ⟨exists_emb hγ, fun j hj => ⟨emb_inj hτ hγ hj, emb_range hτ h2 hγ hj, emb_centre hτ hγ hj⟩,
    fun γ' hγ' => conj_main hτ h2 hΔ hγ hγ'⟩

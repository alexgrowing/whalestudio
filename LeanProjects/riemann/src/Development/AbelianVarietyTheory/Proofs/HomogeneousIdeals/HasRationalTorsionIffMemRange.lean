import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsLineOfAddAddEqZero

namespace GlobalTheory

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

section Def

variable {K : Type*} [Field K]

open scoped Classical in

def HasRationalTorsion (W : WeierstrassCurve K) (L : Type*) [Field L] [Algebra K L] (n : ℕ) :
    Prop :=
  ∀ (x y : L) (h : (W.baseChange L).toAffine.Nonsingular x y), n • Point.some x y h = 0 →
    x ∈ (algebraMap K L).range ∧ y ∈ (algebraMap K L).range

variable {W : WeierstrassCurve K} {L : Type*} [Field L] [Algebra K L] {m n : ℕ}

theorem hasRationalTorsion_iff [DecidableEq L] : HasRationalTorsion W L n ↔
    ∀ (x y : L) (h : (W.baseChange L).toAffine.Nonsingular x y), n • Point.some x y h = 0 →
      x ∈ (algebraMap K L).range ∧ y ∈ (algebraMap K L).range := by
  unfold HasRationalTorsion
  convert Iff.rfl

theorem HasRationalTorsion.of_dvd (h : HasRationalTorsion W L n) (hmn : m ∣ n) :
    HasRationalTorsion W L m := by
  classical
  obtain ⟨k, rfl⟩ := hmn
  rw [hasRationalTorsion_iff] at h ⊢
  intro x y hP h0
  exact h x y hP (by rw [mul_nsmul, h0, nsmul_zero])

theorem HasRationalTorsion.variableChange (h : HasRationalTorsion W L n) (C : VariableChange K) :
    HasRationalTorsion (C • W) L n := by
  classical
  rw [hasRationalTorsion_iff] at h ⊢
  intro x y hP h0
  have e : (C.map (algebraMap K L)) • (W.baseChange L) = (C • W).baseChange L := map_variableChange ..
  have h1 := congrArg (variableChangePoint _ e) h0
  rw [map_nsmul, map_zero, variableChangePoint_some] at h1
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h _ _ _ h1
  have hu : algebraMap K L C.u ≠ 0 := by simp
  simp only [VariableChange.map, Units.coe_map, MonoidHom.coe_coe] at ha hb
  have hx : algebraMap K L ((a - C.r) / C.u ^ 2) = x := by
    simp only [map_div₀, map_sub, map_pow, ha]
    field_simp
    ring
  refine ⟨⟨_, hx⟩, ⟨(b - C.s * (a - C.r) - C.t) / C.u ^ 3, ?_⟩⟩
  simp only [map_div₀, map_sub, map_mul, map_pow, ha, hb]
  field_simp
  ring

end Def

def splitCurve {R : Type*} [CommRing R] (A B : R) : WeierstrassCurve R :=
  ⟨0, -(A + B), 0, A * B, 0⟩

def legendreCurve {R : Type*} [CommRing R] (l : R) : WeierstrassCurve R :=
  ⟨0, -(1 + l), 0, l, 0⟩

def deuringCurve {R : Type*} [CommRing R] (a b : R) : WeierstrassCurve R :=
  ⟨a, 0, b, 0, 0⟩

section Invariants

variable {R : Type*} [CommRing R]

theorem splitCurve_Δ (A B : R) : (splitCurve A B).Δ = 16 * A ^ 2 * B ^ 2 * (A - B) ^ 2 := by
  simp only [splitCurve, Δ, b₂, b₄, b₆, b₈]; ring

theorem splitCurve_c₄ (A B : R) : (splitCurve A B).c₄ = 16 * (A ^ 2 - A * B + B ^ 2) := by
  simp only [splitCurve, c₄, b₂, b₄]; ring

theorem legendreCurve_Δ (l : R) : (legendreCurve l).Δ = 16 * l ^ 2 * (l - 1) ^ 2 := by
  simp only [legendreCurve, Δ, b₂, b₄, b₆, b₈]; ring

theorem legendreCurve_c₄ (l : R) : (legendreCurve l).c₄ = 16 * (l ^ 2 - l + 1) := by
  simp only [legendreCurve, c₄, b₂, b₄]; ring

theorem deuringCurve_Δ (a b : R) : (deuringCurve a b).Δ = b ^ 3 * (a ^ 3 - 27 * b) := by
  simp only [deuringCurve, Δ, b₂, b₄, b₆, b₈]; ring

theorem deuringCurve_c₄ (a b : R) : (deuringCurve a b).c₄ = a * (a ^ 3 - 24 * b) := by
  simp only [deuringCurve, c₄, b₂, b₄]; ring

theorem deuringCurve_map {S : Type*} [CommRing S] (f : R →+* S) (a b : R) :
    (deuringCurve a b).map f = deuringCurve (f a) (f b) := by
  simp [deuringCurve, WeierstrassCurve.map]

end Invariants

theorem nonsingular_baseChange_iff {K : Type*} [Field K] {W : WeierstrassCurve K} [W.IsElliptic]
    {L : Type*} [Field L] [Algebra K L] {x y : L} :
    (W.baseChange L).toAffine.Nonsingular x y ↔ (W.baseChange L).toAffine.Equation x y :=
  haveI : (W.baseChange L).IsElliptic := inferInstanceAs (W.map (algebraMap K L)).IsElliptic
  equation_iff_nonsingular.symm

section Roots

variable {L : Type*} [Field L] [IsAlgClosed L]

theorem exists_root_quadratic (b c : L) : ∃ x : L, x ^ 2 + b * x + c = 0 := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ 2 + C b * X + C c : L[X])
    (by rw [show (X ^ 2 + C b * X + C c : L[X]).degree = 2 by compute_degree!]; decide)
  exact ⟨x, by simpa using hx⟩

theorem exists_root_cubic {a : L} (ha : a ≠ 0) (b c d : L) :
    ∃ x : L, a * x ^ 3 + b * x ^ 2 + c * x + d = 0 := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d : L[X])
    (by rw [degree_cubic ha]; decide)
  exact ⟨x, by simpa using hx⟩

theorem exists_equation (W : WeierstrassCurve L) (x : L) : ∃ y, W.toAffine.Equation x y := by
  obtain ⟨y, hy⟩ := exists_root_quadratic (W.a₁ * x + W.a₃)
    (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
  exact ⟨y, (equation_iff ..).mpr (by linear_combination hy)⟩

end Roots

section Flex

variable {F : Type*} [Field F] {W : WeierstrassCurve F}

theorem exists_flex_slope {x y : F} (h : W.toAffine.Nonsingular x y) (h3 : W.Ψ₃.eval x = 0) :
    ∃ l : F, l * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y ∧
      l ^ 2 + W.a₁ * l - W.a₂ = 3 * x := by
  rw [nonsingular_iff', equation_iff'] at h
  obtain ⟨hE, hN⟩ := h
  simp only [Ψ₃, b₂, b₄, b₆, b₈, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat] at h3
  have hη : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    intro h0
    refine hN.elim (fun h => h ?_) (fun h => h h0)
    refine pow_eq_zero_iff (two_ne_zero) |>.mp ?_
    linear_combination -h3 - (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) * hE
      - (W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
        - (W.a₂ + 3 * x) * (2 * y + W.a₁ * x + W.a₃)) * h0
  obtain ⟨l, hl⟩ : ∃ l : F,
      l * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y :=
    ⟨_, div_mul_cancel₀ _ hη⟩
  refine ⟨l, hl, mul_left_cancel₀ (pow_ne_zero 2 hη) ?_⟩
  linear_combination -h3 - (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) * hE
    + (l * (2 * y + W.a₁ * x + W.a₃) + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
      + W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * hl

theorem three_nsmul_eq_zero_iff [DecidableEq F] {x y : F} (h : W.toAffine.Nonsingular x y) :
    3 • Point.some x y h = 0 ↔ W.Ψ₃.eval x = 0 := by
  rw [three'_nsmul]
  constructor
  · intro h0
    obtain ⟨l, n, e, -, -, s₁, s₂, s₃⟩ := exists_line_of_add_add_eq_zero h0
    simp only [Ψ₃, b₂, b₄, b₆, b₈, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]
    have h2 : W.a₂ = l ^ 2 + W.a₁ * l - 3 * x := by linear_combination s₁
    have h4 : W.a₄ = 3 * x ^ 2 + 2 * l * n + W.a₁ * n + W.a₃ * l := by linear_combination -s₂
    have h6 : W.a₆ = n ^ 2 + W.a₃ * n - x ^ 3 := by linear_combination s₃
    rw [h2, h4, h6]
    ring
  · intro h3
    obtain ⟨l, h₁, h₂⟩ := exists_flex_slope h h3
    exact add_add_eq_zero_of_line h h h l (y - l * x) (by ring) (by ring) (by ring)
      (by linear_combination -h₂) (by linear_combination h₁ - 2 * x * h₂)

end Flex

section Forms

variable {K : Type*} [Field K] [CharZero K] {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
  {W : WeierstrassCurve K} [W.IsElliptic]

omit [CharZero K] in

theorem HasRationalTorsion.exists_point_of_root (h : HasRationalTorsion W L 3) {x : L}
    (hx : (W.baseChange L).Ψ₃.eval x = 0) :
    ∃ x₀ y₀ : K, algebraMap K L x₀ = x ∧ W.toAffine.Nonsingular x₀ y₀ ∧ W.Ψ₃.eval x₀ = 0 := by
  classical
  obtain ⟨y, hy⟩ := exists_equation (W.baseChange L) x
  have hy' : (W.baseChange L).toAffine.Nonsingular x y := nonsingular_baseChange_iff.mpr hy
  obtain ⟨⟨x₀, rfl⟩, ⟨y₀, rfl⟩⟩ :=
    hasRationalTorsion_iff.mp h x y hy' ((three_nsmul_eq_zero_iff hy').mpr hx)
  refine ⟨x₀, y₀, rfl, (W.toAffine.map_nonsingular (algebraMap K L).injective x₀ y₀).mp hy', ?_⟩
  rw [WeierstrassCurve.baseChange, map_Ψ₃, eval_map_apply] at hx
  exact (map_eq_zero _).mp hx

theorem HasRationalTorsion.exists_deuringCurve (h : HasRationalTorsion W L 3) :
    ∃ (C : VariableChange K) (a b d : K), C.u = 1 ∧ C • W = deuringCurve a b ∧
      d ^ 3 = a ^ 3 - 27 * b := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (W.baseChange L).Ψ₃
    (degree_ne_of_natDegree_ne ((W.baseChange L).natDegree_Ψ₃_pos three_ne_zero).ne')
  obtain ⟨x₀, y₀, -, h₀, h₃⟩ := h.exists_point_of_root hx
  obtain ⟨l, h₁, h₂⟩ := exists_flex_slope h₀ h₃
  have hE := (equation_iff' ..).mp h₀.1
  obtain ⟨a, b, e⟩ : ∃ a b : K,
      (⟨1, x₀, l, y₀⟩ : VariableChange K) • W = deuringCurve a b := by
    refine ⟨W.a₁ + 2 * l, 2 * y₀ + W.a₁ * x₀ + W.a₃, ?_⟩
    simp only [variableChange_def, deuringCurve, inv_one, Units.val_one]
    ext <;> dsimp only
    · ring
    · linear_combination -h₂
    · ring
    · linear_combination -h₁
    · linear_combination -hE
  have h' := h.variableChange ⟨1, x₀, l, y₀⟩
  have hell : ((⟨1, x₀, l, y₀⟩ : VariableChange K) • W).IsElliptic := inferInstance
  rw [e] at h' hell
  have hb : b ≠ 0 := by
    intro hb
    have := (deuringCurve a b).isUnit_Δ.ne_zero
    rw [deuringCurve_Δ, hb] at this
    simp at this
  obtain ⟨z, hz⟩ := exists_root_cubic (three_ne_zero : (3 : L) ≠ 0) (algebraMap K L a ^ 2)
    (3 * algebraMap K L a * algebraMap K L b) (3 * algebraMap K L b ^ 2)
  obtain ⟨z₀, -, rfl, -, -⟩ := h'.exists_point_of_root (x := z) (by
    simp only [WeierstrassCurve.baseChange, deuringCurve_map]
    simp only [deuringCurve, Ψ₃, b₂, b₄, b₆, b₈, eval_add, eval_mul, eval_pow, eval_C, eval_X,
      eval_ofNat]
    linear_combination z * hz)
  have hz₀ : 3 * z₀ ^ 3 + a ^ 2 * z₀ ^ 2 + 3 * a * b * z₀ + 3 * b ^ 2 = 0 := by
    apply (algebraMap K L).injective
    simpa [map_ofNat] using hz
  have hz0 : z₀ ≠ 0 := by
    rintro rfl
    simp [hb] at hz₀
  refine ⟨_, a, b, a + 3 * b / z₀, rfl, e, ?_⟩
  field_simp
  linear_combination 9 * b * hz₀

omit [CharZero K] [IsAlgClosed L] in

theorem HasRationalTorsion.mem_range_of_root (h : HasRationalTorsion W L 2) (h₁ : W.a₁ = 0)
    (h₃ : W.a₃ = 0) {x : L} (hx : x ^ 3 + algebraMap K L W.a₂ * x ^ 2 + algebraMap K L W.a₄ * x
      + algebraMap K L W.a₆ = 0) : x ∈ (algebraMap K L).range := by
  classical
  have hy : (W.baseChange L).toAffine.Equation x 0 := by
    rw [equation_iff]
    simp only [WeierstrassCurve.baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
    linear_combination -hx
  refine (hasRationalTorsion_iff.mp h x 0 (nonsingular_baseChange_iff.mpr hy) ?_).1
  rw [two_nsmul]
  apply Point.add_self_of_Y_eq
  simp [WeierstrassCurve.baseChange, h₁, h₃]

theorem HasRationalTorsion.exists_splitCurve (h : HasRationalTorsion W L 2) :
    ∃ (C : VariableChange K) (A B : K), C.u = 1 ∧ C • W = splitCurve A B := by
  set C₁ : VariableChange K := ⟨1, 0, -W.a₁ / 2, -W.a₃ / 2⟩ with hC₁
  have h₁ : (C₁ • W).a₁ = 0 := by simp only [hC₁, variableChange_a₁]; ring
  have h₃ : (C₁ • W).a₃ = 0 := by simp only [hC₁, variableChange_a₃]; ring
  have h' := h.variableChange C₁
  obtain ⟨e, he⟩ := exists_root_cubic (one_ne_zero : (1 : L) ≠ 0) (algebraMap K L (C₁ • W).a₂)
    (algebraMap K L (C₁ • W).a₄) (algebraMap K L (C₁ • W).a₆)
  rw [one_mul] at he
  obtain ⟨e, rfl⟩ := h'.mem_range_of_root h₁ h₃ he
  obtain ⟨f, hf⟩ := exists_root_quadratic (algebraMap K L ((C₁ • W).a₂ + e))
    (algebraMap K L ((C₁ • W).a₄ + (C₁ • W).a₂ * e + e ^ 2))
  obtain ⟨f, rfl⟩ := h'.mem_range_of_root h₁ h₃ (x := f) (by
    simp only [map_add, map_mul, map_pow] at hf
    linear_combination he + (f - algebraMap K L e) * hf)
  have he' : e ^ 3 + (C₁ • W).a₂ * e ^ 2 + (C₁ • W).a₄ * e + (C₁ • W).a₆ = 0 := by
    apply (algebraMap K L).injective
    simpa using he
  have hf' : f ^ 2 + ((C₁ • W).a₂ + e) * f + ((C₁ • W).a₄ + (C₁ • W).a₂ * e + e ^ 2) = 0 := by
    apply (algebraMap K L).injective
    simpa using hf
  refine ⟨⟨1, e, 0, 0⟩ * C₁, f - e, -(C₁ • W).a₂ - 2 * e - f, by simp [VariableChange.mul_def, hC₁],
    ?_⟩
  rw [mul_smul]
  generalize C₁ • W = W₁ at *
  simp only [variableChange_def, splitCurve, inv_one, Units.val_one]
  ext <;> dsimp only
  · linear_combination h₁
  · ring
  · linear_combination h₃ + e * h₁
  · linear_combination hf'
  · linear_combination he'

omit [CharZero K] in

theorem HasRationalTorsion.isSquare_neg {A B : K} [(splitCurve A B).IsElliptic]
    (h : HasRationalTorsion (splitCurve A B) L 4) : ∃ a : K, a ^ 2 = -A := by
  classical
  have hΔ := (splitCurve A B).isUnit_Δ.ne_zero
  rw [splitCurve_Δ] at hΔ
  have hA : A ≠ 0 := by rintro rfl; simp at hΔ
  have hB : B ≠ 0 := by rintro rfl; simp at hΔ
  have hAB : A ≠ B := by rintro rfl; simp at hΔ
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (-algebraMap K L A) two_pos
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (-algebraMap K L B) two_pos
  have hP : ((splitCurve A B).baseChange L).toAffine.Nonsingular (α * β) (α * β * (α + β)) := by
    rw [nonsingular_baseChange_iff, equation_iff]
    simp only [WeierstrassCurve.baseChange, splitCurve, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
      map_zero, map_neg, map_add, map_mul]
    rw [← neg_neg (algebraMap K L A), ← hα, ← neg_neg (algebraMap K L B), ← hβ]
    ring
  have hT : ((splitCurve A B).baseChange L).toAffine.Nonsingular 0 0 := by
    rw [nonsingular_baseChange_iff, equation_iff]
    simp [WeierstrassCurve.baseChange, splitCurve]
  have h2 : Point.some _ _ hT + Point.some _ _ hT = 0 := by
    apply Point.add_self_of_Y_eq
    simp [WeierstrassCurve.baseChange, splitCurve]
  have h3 : Point.some _ _ hP + Point.some _ _ hP + Point.some _ _ hT = 0 := by
    refine add_add_eq_zero_of_line hP hP hT (α + β) 0 (by ring) (by ring) (by ring) ?_ ?_
    all_goals
      simp only [WeierstrassCurve.baseChange, splitCurve, map_a₁, map_a₂, map_a₃, map_a₄,
        map_zero, map_neg, map_add, map_mul]
      rw [← neg_neg (algebraMap K L A), ← hα, ← neg_neg (algebraMap K L B), ← hβ]
      ring
  have h4 : 4 • Point.some _ _ hP = 0 := by
    have : 4 • Point.some _ _ hP = 2 • (Point.some _ _ hP + Point.some _ _ hP + Point.some _ _ hT)
      - (Point.some _ _ hT + Point.some _ _ hT) := by abel
    rw [this, h2, h3, smul_zero, sub_zero]
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hasRationalTorsion_iff.mp h _ _ hP h4
  have hα0 : α ≠ 0 := by rintro rfl; simp [hA] at hα
  have hβ0 : β ≠ 0 := by rintro rfl; simp [hB] at hβ
  have hαβ : α + β ≠ 0 := by
    intro h0
    apply hAB
    apply (algebraMap K L).injective
    linear_combination hα - hβ - (α - β) * h0
  refine ⟨(p - A) * p / q, (algebraMap K L).injective ?_⟩
  rw [map_pow, map_neg, ← hα]
  congr 1
  rw [map_div₀, map_mul, map_sub, hp, hq, ← neg_neg (algebraMap K L A), ← hα]
  field_simp
  ring

theorem HasRationalTorsion.exists_splitCurve_sq (h : HasRationalTorsion W L 4) :
    ∃ (C : VariableChange K) (A B a c : K), C.u = 1 ∧ C • W = splitCurve A B ∧ a ^ 2 = A ∧
      c ^ 2 = A * B * (A - B) := by
  obtain ⟨C, A, B, hu, e⟩ := (h.of_dvd (by norm_num : 2 ∣ 4)).exists_splitCurve
  have e₁ : C • W = splitCurve B A := by
    rw [e, splitCurve, splitCurve, add_comm, mul_comm]
  have e₂ : ((⟨1, A, 0, 0⟩ : VariableChange K) * C) • W = splitCurve (-A) (B - A) := by
    rw [mul_smul, e]
    simp only [variableChange_def, splitCurve, inv_one, Units.val_one]
    ext <;> dsimp only <;> ring
  have e₃ : ((⟨1, A, 0, 0⟩ : VariableChange K) * C) • W = splitCurve (B - A) (-A) := by
    rw [e₂, splitCurve, splitCurve, add_comm, mul_comm (B - A)]
  have key : ∀ {C : VariableChange K} {A B : K}, C • W = splitCurve A B → ∃ a : K, a ^ 2 = -A := by
    intro C A B e
    have : (splitCurve A B).IsElliptic := e ▸ inferInstance
    exact HasRationalTorsion.isSquare_neg (L := L) (B := B) (e ▸ h.variableChange C)
  obtain ⟨a₀, h₀⟩ := key e
  obtain ⟨a₁, h₁⟩ := key e₁
  obtain ⟨a₂, h₂⟩ := key e₂
  obtain ⟨a₃, h₃⟩ := key e₃
  refine ⟨C, A, B, a₂, a₀ * a₁ * a₃, hu, e, by rw [h₂, neg_neg], ?_⟩
  rw [mul_pow, mul_pow, h₀, h₁, h₃]
  ring

theorem HasRationalTorsion.exists_pow_twelve_eq_Δ (h : HasRationalTorsion W L 12) :
    ∃ δ : K, δ ^ 12 = W.Δ := by
  obtain ⟨C, A, B, -, c, hu, e, -, hc⟩ := (h.of_dvd (by norm_num : 4 ∣ 12)).exists_splitCurve_sq
  obtain ⟨C', a, b, d, hu', e', hd⟩ := (h.of_dvd (by norm_num : 3 ∣ 12)).exists_deuringCurve
  have h4 : (2 * c) ^ 4 = W.Δ := by
    have := congrArg WeierstrassCurve.Δ e
    rw [variableChange_Δ, hu, splitCurve_Δ] at this
    simp only [inv_one, Units.val_one, one_pow, one_mul] at this
    rw [this]
    linear_combination 16 * (c ^ 2 + A * B * (A - B)) * hc
  have h3 : (b * d) ^ 3 = W.Δ := by
    have := congrArg WeierstrassCurve.Δ e'
    rw [variableChange_Δ, hu', deuringCurve_Δ] at this
    simp only [inv_one, Units.val_one, one_pow, one_mul] at this
    rw [this, mul_pow, hd]
  refine ⟨b * d / (2 * c), ?_⟩
  have hΔ := W.isUnit_Δ.ne_zero
  rw [div_pow, show 12 = 3 * 4 by rfl, pow_mul, h3, mul_comm 3 4, pow_mul, h4]
  field_simp

end Forms

end GlobalTheory

import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DiagSplit

section Algebra

variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem baer (V : Type) [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] :
    Module.Baer R V := by
  intro I g
  by_cases hI : ∃ a ∈ I, a ≠ 0
  · obtain ⟨a, ha, ha0⟩ := hI
    have hA : algebraMap R K a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha0
    refine ⟨LinearMap.toSpanSingleton R V ((algebraMap R K a)⁻¹ • g ⟨a, ha⟩), fun x hx => ?_⟩
    have key : a • g ⟨x, hx⟩ = x • g ⟨a, ha⟩ := by
      rw [← LinearMap.map_smul, ← LinearMap.map_smul]
      congr 1
      exact Subtype.ext (show a * x = x * a from mul_comm a x)
    rw [LinearMap.toSpanSingleton_apply, ← algebraMap_smul K x, smul_comm, algebraMap_smul,
      ← key, ← algebraMap_smul K a, smul_smul, inv_mul_cancel₀ hA, one_smul]
  · simp only [not_exists, not_and, not_not] at hI
    refine ⟨0, fun x hx => ?_⟩
    have hx0 : (⟨x, hx⟩ : I) = 0 := Subtype.ext (hI x hx)
    rw [hx0, map_zero, LinearMap.zero_apply]

theorem exists_matrix {r : ℕ} (M : Submodule R (Fin r → K)) (f : M →ₗ[R] (Fin r → K)) :
    ∃ A : Matrix (Fin r) (Fin r) K, ∀ d : M, (d : Fin r → K) ᵥ* A = f d := by
  obtain ⟨F, hF⟩ := (baer (R := R) (K := K) (Fin r → K)).extension_property M.subtype
    Subtype.val_injective f
  have hK : ∀ (c : K) (v : Fin r → K), F (c • v) = c • F v := by
    intro c v
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) c
    have hs' : algebraMap R K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have hmul : algebraMap R K s * (algebraMap R K a / algebraMap R K s) = algebraMap R K a := by
      field_simp
    have h1 : s • F ((algebraMap R K a / algebraMap R K s) • v) = a • F v := by
      conv_lhs => rw [← F.map_smul]
      rw [← algebraMap_smul K s ((algebraMap R K a / algebraMap R K s) • v), smul_smul, hmul,
        algebraMap_smul, F.map_smul]
    calc F ((algebraMap R K a / algebraMap R K s) • v)
        = (algebraMap R K s)⁻¹ • (s • F ((algebraMap R K a / algebraMap R K s) • v)) := by
          rw [← algebraMap_smul K s (F _), smul_smul, inv_mul_cancel₀ hs', one_smul]
      _ = (algebraMap R K a / algebraMap R K s) • F v := by
          rw [h1, ← algebraMap_smul K a (F v), smul_smul, div_eq_mul_inv, mul_comm]
  let Fk : (Fin r → K) →ₗ[K] (Fin r → K) :=
    { toFun := F, map_add' := F.map_add, map_smul' := hK }
  refine ⟨(LinearMap.toMatrix' Fk)ᵀ, fun d => ?_⟩
  rw [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  exact LinearMap.congr_fun hF d

end Algebra

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem exists_section (L₁ L₂ : Lt E r) (h₁ : L₁.FG) (h₂ : L₂.FG) :
    ∃ A : Matrix (Fin r) (Fin r) E, ∀ d ∈ L₁ ⊔ L₂, d ᵥ* A ∈ L₁ ∧ d ᵥ* A - d ∈ L₂ := by
  classical
  have hP : (L₁ ⊔ L₂).FG := Submodule.FG.sup h₁ h₂
  have : Module.Finite (𝓞 E) (L₁ ⊔ L₂ : Lt E r) := Module.Finite.iff_fg.mpr hP
  have : Module.FinitePresentation (𝓞 E) (L₁ ⊔ L₂ : Lt E r) := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) (L₁ ⊔ L₂ : Lt E r) := Module.Flat.projective_of_finitePresentation
  let f : L₁ →ₗ[𝓞 E] (Fin r → E) ⧸ L₂ := L₂.mkQ ∘ₗ L₁.subtype
  let g : (L₁ ⊔ L₂ : Lt E r) →ₗ[𝓞 E] LinearMap.range f :=
    LinearMap.codRestrict (LinearMap.range f) (L₂.mkQ ∘ₗ (L₁ ⊔ L₂).subtype) (by
      intro d
      obtain ⟨y₁, hy₁, y₂, hy₂, hd⟩ := Submodule.mem_sup.mp d.2
      refine ⟨⟨y₁, hy₁⟩, ?_⟩
      simp only [f, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq, ← hd]
      simpa using L₂.neg_mem hy₂)
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f.rangeRestrict g
    (LinearMap.surjective_rangeRestrict f)
  obtain ⟨A, hA⟩ := exists_matrix (R := 𝓞 E) (K := E) (L₁ ⊔ L₂) (L₁.subtype ∘ₗ h)
  refine ⟨A, fun d hd => ?_⟩
  have e1 := hA ⟨d, hd⟩
  have e2 := congrArg Subtype.val (LinearMap.congr_fun hh ⟨d, hd⟩)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at e1
  simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, LinearMap.rangeRestrict,
    f, Submodule.subtype_apply, Submodule.mkQ_apply, g] at e2
  rw [e1]
  exact ⟨(h ⟨d, hd⟩).2, (Submodule.Quotient.eq L₂).mp e2⟩

variable [IsCMField E]

noncomputable def pair (x y : Fin r → E) : E := ∑ a, x a * cc (y a)

def intTr (E : Type) [Field E] [NumberField E] : AddSubgroup E where
  carrier := {e | ∃ k : ℤ, Algebra.trace ℚ E e = k}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k + l, by simp [hk, hl]⟩
  neg_mem' := by
    rintro a ⟨k, hk⟩
    exact ⟨-k, by simp [hk]⟩

theorem pair_add_left (x x' y : Fin r → E) : pair (x + x') y = pair x y + pair x' y := by
  simp only [pair, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem pair_sub_left (x x' y : Fin r → E) : pair (x - x') y = pair x y - pair x' y := by
  simp only [pair, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem pair_add_right (x y y' : Fin r → E) : pair x (y + y') = pair x y + pair x y' := by
  simp only [pair, cc, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem pair_sub_right (x y y' : Fin r → E) : pair x (y - y') = pair x y - pair x y' := by
  simp only [pair, cc, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem pair_vecMul (x y : Fin r → E) (M : Matrix (Fin r) (Fin r) E) :
    pair (x ᵥ* M) y = pair x (y ᵥ* ccT M) := by
  simp only [pair, Matrix.vecMul, dotProduct, ccT, Matrix.transpose_apply, Matrix.map_apply, cc,
    map_sum, map_mul, IsCMField.complexConj_apply_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem ccT_add (A B : Matrix (Fin r) (Fin r) E) : ccT (A + B) = ccT A + ccT B := by
  ext i j
  simp [ccT, cc, map_add]

theorem ccT_sub (A B : Matrix (Fin r) (Fin r) E) : ccT (A - B) = ccT A - ccT B := by
  ext i j
  simp [ccT, cc, map_sub]

theorem ccT_smul (c : E) (A : Matrix (Fin r) (Fin r) E) : ccT (c • A) = cc c • ccT A := by
  ext i j
  simp [ccT, cc, map_mul]

variable (X : Data E r)

noncomputable def skew : Matrix (Fin r) (Fin r) E := (X.κ0 / 2) • X.Gm

theorem ccT_skew : ccT (skew X) = -skew X := by
  have hξ : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
  have hκ : IsCMField.complexConj E X.κ0 = -X.κ0 := by
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [hξ]
  have hG : ∀ a b, IsCMField.complexConj E (X.Gm a b) = X.Gm b a := X.Gm_herm
  ext i j
  simp only [ccT, skew, cc, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    map_mul, map_div₀, hκ, hG, Matrix.neg_apply, map_ofNat]
  ring

theorem isUnit_det_skew : IsUnit (skew X).det := by
  have hξ := X.ξ0_ne
  have hκ : X.κ0 ≠ 0 := by
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [hξ]
  rw [isUnit_iff_ne_zero, skew, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (div_ne_zero hκ two_ne_zero)) X.Gm_det

theorem EF_mem (x y : Fin r → E) :
    (∃ k : ℤ, EF X x y = k) ↔ pair (x ᵥ* skew X) y ∈ intTr E := by
  have hp : pair (x ᵥ* skew X) y = (X.κ0 / 2) * herm X.Gm x y := by
    simp only [pair, skew, Matrix.smul_apply, smul_eq_mul, herm, Matrix.vecMul,
      dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hm : pair (x ᵥ* skew X) y ∈ intTr E ↔
      ∃ k : ℤ, Algebra.trace ℚ E (pair (x ᵥ* skew X) y) = k := Iff.rfl
  rw [EF_def, hm, hp]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    rw [neg_mul, map_neg] at hk
    push_cast
    linarith
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    rw [neg_mul, map_neg, hk]
    push_cast
    ring

variable {X}

theorem mem_iff {L : Lt E r} (hL : SelfD X L) (x : Fin r → E) :
    x ∈ L ↔ ∀ y ∈ L, pair (x ᵥ* skew X) y ∈ intTr E := by
  rw [hL.2 x]
  exact forall₂_congr fun y _ => EF_mem X x y

theorem mem_inf_iff {L₁ L₂ : Lt E r} (h₁ : SelfD X L₁) (h₂ : SelfD X L₂) (x : Fin r → E) :
    (x ∈ L₁ ∧ x ∈ L₂) ↔ ∀ y ∈ L₁ ⊔ L₂, pair (x ᵥ* skew X) y ∈ intTr E := by
  constructor
  · rintro ⟨hx₁, hx₂⟩ y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    rw [pair_add_right]
    exact add_mem ((mem_iff h₁ x).mp hx₁ y₁ hy₁) ((mem_iff h₂ x).mp hx₂ y₂ hy₂)
  · intro h
    exact ⟨(mem_iff h₁ x).mpr fun y hy => h y (Submodule.mem_sup_left hy),
      (mem_iff h₂ x).mpr fun y hy => h y (Submodule.mem_sup_right hy)⟩

theorem vecMul_dblT (y₁ y₂ : Fin r → E) : Sum.elim y₁ y₂ ᵥ* dblT X =
    Sum.elim (y₁ - y₂) ((1 / 2 : E) • ((y₁ + y₂) ᵥ* skew X)) := by
  rw [dblT, Matrix.vecMul_fromBlocks]
  congr 1
  · funext i
    simp [sub_eq_add_neg, Matrix.vecMul_neg]
  · funext i
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, skew, Matrix.vecMul_smul, Matrix.add_vecMul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

private theorem ccT_mul_siegel_theta_transformation (M N : Matrix (Fin r) (Fin r) E) : ccT (M * N) = ccT N * ccT M := by
  ext i j
  simp [ccT, cc, Matrix.mul_apply, map_sum, map_mul, mul_comm]

private theorem ccT_one_fin_r : ccT (1 : Matrix (Fin r) (Fin r) E) = 1 := by
  simp only [ccT]
  rw [Matrix.map_one _ (by simp [cc]) (by simp [cc]), Matrix.transpose_one]

private theorem ccT_ccT_siegel_theta_transformation (M : Matrix (Fin r) (Fin r) E) : ccT (ccT M) = M := by
  ext i j
  simp [ccT, cc]

private theorem pair_smul_left_eq_mul (c : E) (x y : Fin r → E) : pair (c • x) y = c * pair x y := by
  simp only [pair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem pair_vecMul_right_eq_ccT (x y : Fin r → E) (N : Matrix (Fin r) (Fin r) E) :
    pair x (y ᵥ* N) = pair (x ᵥ* ccT N) y := by
  rw [pair_vecMul, ccT_ccT_siegel_theta_transformation]

theorem doubled_lattice_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L₁ L₂ : Lt E r, SelfD X L₁ → SelfD X L₂ → ∃ β : Matrix (Fin r) (Fin r) E, ccT β = β ∧ ∀ d b : Fin r → E, ((∃ y₁ ∈ L₁, ∃ y₂ ∈ L₂, Sum.elim y₁ y₂ ᵥ* dblT X = Sum.elim d b) ↔ (d ∈ L₁ ⊔ L₂ ∧ ∀ d' ∈ L₁ ⊔ L₂, ∃ k : ℤ, Algebra.trace ℚ E (∑ a, (b - d ᵥ* β) a * cc (d' a)) = k)) := by
  intro E _ _ _ r X w hw hw1 L₁ L₂ h₁ h₂
  obtain ⟨A, hA⟩ := exists_section L₁ L₂ h₁.1 h₂.1
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : Matrix (Fin r) (Fin r) E, β₀ = (A - (1 / 2 : E) • 1) * skew X :=
    ⟨_, rfl⟩
  have hwcc : cc w = 1 - w := eq_sub_of_add_eq' hw1
  have hcc1 : cc (1 - w) = w := by
    have h := hwcc
    simp only [cc] at h ⊢
    rw [map_sub, map_one, h]
    ring
  have hhalf : cc (1 / 2 : E) = 1 / 2 := by simp [cc]
  have hD : ccT β₀ - β₀ = (A - 1) * skew X * ccT (A - 1) - A * skew X * ccT A := by
    rw [hβ₀]
    simp only [ccT_mul_siegel_theta_transformation, ccT_skew, ccT_sub, ccT_smul, ccT_one_fin_r, hhalf, sub_mul, mul_sub,
      Matrix.smul_mul, one_mul, mul_one, neg_mul]
    module
  have hvA : ∀ d : Fin r → E, d ᵥ* β₀ = (d ᵥ* A - (1 / 2 : E) • d) ᵥ* skew X := by
    intro d
    rw [hβ₀, ← Matrix.vecMul_vecMul, Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one]
  have hsmul : ∀ {L : Lt E r} {y : Fin r → E}, y ∈ L → w • y ∈ L := by
    intro L y hy
    exact L.smul_mem (⟨w, hw⟩ : 𝓞 E) hy
  have hA1 : ∀ z : Fin r → E, z ᵥ* (A - 1) = z ᵥ* A - z := fun z => by
    rw [Matrix.vecMul_sub, Matrix.vecMul_one]
  have hcorr : ∀ d ∈ L₁ ⊔ L₂, ∀ d' ∈ L₁ ⊔ L₂,
      pair (d ᵥ* ((1 - w) • β₀ + w • ccT β₀) - d ᵥ* β₀) d' ∈ intTr E := by
    intro d hd d' hd'
    have e1 : d ᵥ* ((1 - w) • β₀ + w • ccT β₀) - d ᵥ* β₀ = w • (d ᵥ* (ccT β₀ - β₀)) := by
      rw [Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_smul, Matrix.vecMul_sub]
      module
    have e2 : ∀ N : Matrix (Fin r) (Fin r) E, pair (d ᵥ* (N * skew X * ccT N)) d' =
        pair ((d ᵥ* N) ᵥ* skew X) (d' ᵥ* N) := by
      intro N
      rw [pair_vecMul_right_eq_ccT, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]
    rw [e1, pair_smul_left_eq_mul, hD, Matrix.vecMul_sub, pair_sub_left, e2, e2, mul_sub,
      ← pair_smul_left_eq_mul, ← pair_smul_left_eq_mul, ← Matrix.smul_vecMul, ← Matrix.smul_vecMul,
      hA1, hA1]
    have m₂ : (w • d) ᵥ* A - w • d ∈ L₂ := by
      rw [Matrix.smul_vecMul, ← smul_sub]
      exact hsmul (hA d hd).2
    have m₁ : (w • d) ᵥ* A ∈ L₁ := by
      rw [Matrix.smul_vecMul]
      exact hsmul (hA d hd).1
    have k₂ := (mem_iff h₂ _).mp m₂ (d' ᵥ* A - d') (hA d' hd').2
    have k₁ := (mem_iff h₁ _).mp m₁ (d' ᵥ* A) (hA d' hd').1
    simp only [Matrix.smul_vecMul] at k₁ k₂ ⊢
    exact sub_mem k₂ k₁
  refine ⟨(1 - w) • β₀ + w • ccT β₀, ?_, fun d b => ?_⟩
  · rw [ccT_add, ccT_smul, ccT_smul, ccT_ccT_siegel_theta_transformation, hcc1, hwcc, add_comm]
  have hmem : (∀ d' ∈ L₁ ⊔ L₂, ∃ k : ℤ, Algebra.trace ℚ E
      (∑ a, (b - d ᵥ* ((1 - w) • β₀ + w • ccT β₀)) a * cc (d' a)) = k) ↔
      ∀ d' ∈ L₁ ⊔ L₂, pair (b - d ᵥ* ((1 - w) • β₀ + w • ccT β₀)) d' ∈ intTr E := Iff.rfl
  rw [hmem]
  constructor
  · rintro ⟨y₁, hy₁, y₂, hy₂, hyb⟩
    rw [vecMul_dblT] at hyb
    have hd : y₁ - y₂ = d := funext fun i => congrFun hyb (Sum.inl i)
    have hb : (1 / 2 : E) • ((y₁ + y₂) ᵥ* skew X) = b := funext fun i => congrFun hyb (Sum.inr i)
    have hdm : d ∈ L₁ ⊔ L₂ :=
      hd ▸ sub_mem (Submodule.mem_sup_left hy₁) (Submodule.mem_sup_right hy₂)
    refine ⟨hdm, fun d' hd' => ?_⟩
    have hz₁ : y₁ - d ᵥ* A ∈ L₁ := sub_mem hy₁ (hA d hdm).1
    have hz₂ : y₁ - d ᵥ* A ∈ L₂ := by
      have e : y₁ - d ᵥ* A = y₂ - (d ᵥ* A - d) := by
        rw [← hd]
        abel
      rw [e]
      exact sub_mem hy₂ (hA d hdm).2
    have hzS : b - d ᵥ* β₀ = (y₁ - d ᵥ* A) ᵥ* skew X := by
      rw [← hb, hvA, ← hd, ← Matrix.smul_vecMul, ← Matrix.sub_vecMul]
      congr 1
      module
    have e : b - d ᵥ* ((1 - w) • β₀ + w • ccT β₀) =
        (b - d ᵥ* β₀) - (d ᵥ* ((1 - w) • β₀ + w • ccT β₀) - d ᵥ* β₀) := by abel
    rw [e, pair_sub_left, hzS]
    exact sub_mem ((mem_inf_iff h₁ h₂ _).mp ⟨hz₁, hz₂⟩ d' hd') (hcorr d hdm d' hd')
  · rintro ⟨hdm, hint⟩
    obtain ⟨z, hzdef⟩ : ∃ z : Fin r → E, z = (b - d ᵥ* β₀) ᵥ* (skew X)⁻¹ := ⟨_, rfl⟩
    have hz : z ᵥ* skew X = b - d ᵥ* β₀ := by
      rw [hzdef, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_det_skew X),
        Matrix.vecMul_one]
    have hzm : z ∈ L₁ ∧ z ∈ L₂ := by
      refine (mem_inf_iff h₁ h₂ z).mpr fun y hy => ?_
      have e : z ᵥ* skew X = (b - d ᵥ* ((1 - w) • β₀ + w • ccT β₀)) +
          (d ᵥ* ((1 - w) • β₀ + w • ccT β₀) - d ᵥ* β₀) := by
        rw [hz]
        abel
      rw [e, pair_add_left]
      exact add_mem (hint y hy) (hcorr d hdm y hy)
    refine ⟨d ᵥ* A + z, add_mem (hA d hdm).1 hzm.1, (d ᵥ* A - d) + z,
      add_mem (hA d hdm).2 hzm.2, ?_⟩
    rw [vecMul_dblT]
    have e3 : (1 / 2 : E) • ((d ᵥ* A + z + (d ᵥ* A - d + z)) ᵥ* skew X) = b := by
      rw [← Matrix.smul_vecMul]
      have e4 : (1 / 2 : E) • (d ᵥ* A + z + (d ᵥ* A - d + z)) = (d ᵥ* A - (1 / 2 : E) • d) + z := by
        module
      rw [e4, Matrix.add_vecMul, ← hvA, hz]
      abel
    rw [e3]
    congr 1
    abel

end GlobalTheory.SW.DiagSplit

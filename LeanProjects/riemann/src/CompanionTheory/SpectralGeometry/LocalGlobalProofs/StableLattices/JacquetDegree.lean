import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.QdetSub

noncomputable section

open Finset Polynomial

namespace GlobalTheory.CompanionTheory.RgExhDec.DegreeP

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL

section Extract

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem extract (W' : Submodule ℂ (Module.Dual ℂ V)) (φ : Module.Dual ℂ V) {m : ℕ} (hm : 1 ≤ m)
    (E : Fin m → Fin m → Module.End ℂ V) (a : ℂ) (P : ℂ[X]) (hdeg : P.natDegree = m) (hP : P.Monic)
    (h : ∀ Y : ℂ, φ ∘ₗ qdet E (Y + a) - P.eval Y • φ ∈ W') :
    φ ∘ₗ (∑ k, E k k) - (P.coeff (m - 1) - (m : ℂ) * a + (m : ℂ) * ((m : ℂ) - 1) / 2) • φ ∈ W' := by
  by_contra hx
  obtain ⟨f, hf, hW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have hW' : ∀ w ∈ W', f w = 0 := fun w hw => by
    have : f w ∈ W'.map f := Submodule.mem_map_of_mem hw
    rw [hW] at this
    simpa using this
  obtain ⟨Cc, hC⟩ := GroundTheory.BlockD.FourierDecayAlt.GaugeExists.quantum_determinant_leading_terms (Module.End ℂ V) m E hm
  set t : Module.End ℂ V := ∑ i, E i i - algebraMap ℂ _ (((m : ℂ) * ((m : ℂ) - 1)) / 2) with ht
  set R : ℂ[X] := (X + C a) ^ m * C (f φ) + (X + C a) ^ (m - 1) * C (f (φ ∘ₗ t)) +
    ∑ j ∈ range (m - 1), (X + C a) ^ j * C (f (φ ∘ₗ Cc j)) - P * C (f φ) with hR
  have hRe : ∀ Y : ℂ, R.eval Y = f (φ ∘ₗ qdet E (Y + a) - P.eval Y • φ) := by
    intro Y
    have e : φ ∘ₗ qdet E (Y + a) = (Y + a) ^ m • φ + (Y + a) ^ (m - 1) • (φ ∘ₗ t) +
        ∑ j ∈ range (m - 1), (Y + a) ^ j • (φ ∘ₗ Cc j) := by
      refine LinearMap.ext fun v => ?_
      rw [hC (Y + a)]
      simp [Algebra.algebraMap_eq_smul_one, LinearMap.sum_apply, map_sum, ← ht]
    rw [e]
    simp [hR, eval_finset_sum, map_sum, map_add, map_sub, map_smul]
  have hR0 : R = 0 := Polynomial.funext fun Y => by
    rw [hRe, hW' _ (h Y)]; simp
  have hc : R.coeff (m - 1) = 0 := by rw [hR0]; simp
  have c1 : ((X + C a) ^ m).coeff (m - 1) = (m : ℂ) * a := by
    rw [coeff_X_add_C_pow, Nat.sub_sub_self hm, pow_one, Nat.choose_symm hm, Nat.choose_one_right, mul_comm]
  have c2 : ((X + C a) ^ (m - 1)).coeff (m - 1) = 1 := by
    rw [coeff_X_add_C_pow]; simp
  have c3 : ∀ j ∈ range (m - 1), ((X + C a) ^ j).coeff (m - 1) = 0 := fun j hj => by
    rw [coeff_X_add_C_pow, Nat.choose_eq_zero_of_lt (mem_range.1 hj)]; simp
  rw [hR] at hc
  simp only [coeff_sub, coeff_add, coeff_mul_C, finset_sum_coeff, c1, c2] at hc
  rw [Finset.sum_eq_zero (fun j hj => by rw [c3 j hj, zero_mul])] at hc
  apply hf
  have et : φ ∘ₗ (∑ k, E k k) = φ ∘ₗ t + (((m : ℂ) * ((m : ℂ) - 1)) / 2) • φ := by
    refine LinearMap.ext fun v => ?_
    simp [ht, Algebra.algebraMap_eq_smul_one]
  rw [et]
  simp only [map_sub, map_add, map_smul, smul_eq_mul]
  linear_combination hc

end Extract

theorem prod_coeff {n : ℕ} (s : Finset (Fin n)) (χ : Fin n → ℂ) {m : ℕ} (hs : s.card = m) (hm : 1 ≤ m) :
    (∏ r ∈ s, (X + C (χ r))).coeff (m - 1) = ∑ r ∈ s, χ r := by
  have h1 : ∀ r ∈ s, (X + C (χ r)).Monic := fun r _ => monic_X_add_C _
  have h2 : (∏ r ∈ s, (X + C (χ r))).natDegree = m := by
    rw [natDegree_prod_of_monic _ _ h1]
    simp [hs]
  have h3 := Polynomial.Monic.nextCoeff_prod s _ h1
  rw [nextCoeff_of_natDegree_pos (by omega), h2] at h3
  rw [h3]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp

section Act

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def actL (E : Fin n → Fin n → Module.End ℂ M) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M where
  toFun := actM E
  map_add' Y Z := by simp [actM, add_smul, sum_add_distrib]
  map_smul' c Y := by simp [actM, smul_sum, mul_smul]

theorem actL_apply (E : Fin n → Fin n → Module.End ℂ M) (Y) : actL E Y = actM E Y := rfl

theorem actL_single (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (x : ℂ) :
    actL E (Matrix.single a b x) = x • E a b := by
  rw [actL_apply, actM, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [Matrix.single_apply, hc.symm]
  · simp
  · intro c _ hc
    exact Finset.sum_eq_zero fun d _ => by simp [Matrix.single_apply, hc.symm]
  · simp

theorem act_single (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    actM E (Matrix.single a b 1) = E a b := by
  rw [← actL_apply, actL_single, one_smul]

theorem actL_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) (Y Z : Matrix (Fin n) (Fin n) ℂ) :
    actL E Y * actL E Z - actL E Z * actL E Y = actL E (Y * Z - Z * Y) := by
  refine Matrix.induction_on' Y ?_ ?_ ?_
  · simp
  · intro p q hp hq
    have e1 : actL E (p + q) * actL E Z - actL E Z * actL E (p + q) =
        (actL E p * actL E Z - actL E Z * actL E p) + (actL E q * actL E Z - actL E Z * actL E q) := by
      rw [map_add, add_mul, mul_add]; abel
    have e2 : actL E ((p + q) * Z - Z * (p + q)) = actL E (p * Z - Z * p) + actL E (q * Z - Z * q) := by
      rw [← map_add]; congr 1; rw [add_mul, mul_add]; abel
    rw [e1, e2, hp, hq]
  · intro i j x
    refine Matrix.induction_on' Z ?_ ?_ ?_
    · simp
    · intro p q hp hq
      have e1 : actL E (Matrix.single i j x) * actL E (p + q) - actL E (p + q) * actL E (Matrix.single i j x) =
          (actL E (Matrix.single i j x) * actL E p - actL E p * actL E (Matrix.single i j x)) +
            (actL E (Matrix.single i j x) * actL E q - actL E q * actL E (Matrix.single i j x)) := by
        rw [map_add, add_mul, mul_add]; abel
      have e2 : actL E (Matrix.single i j x * (p + q) - (p + q) * Matrix.single i j x) =
          actL E (Matrix.single i j x * p - p * Matrix.single i j x) +
            actL E (Matrix.single i j x * q - q * Matrix.single i j x) := by
        rw [← map_add]; congr 1; rw [add_mul, mul_add]; abel
      rw [e1, e2, hp, hq]
    · intro k l y
      have hm : ∀ (a b c d : Fin n) (x y : ℂ), Matrix.single a b x * Matrix.single c d y =
          if b = c then Matrix.single a d (x * y) else 0 := by
        intro a b c d x y
        split_ifs with h
        · subst h; exact Matrix.single_mul_single_same _ _ _ _ _
        · exact Matrix.single_mul_single_of_ne _ _ _ _ h _
      have g := hE i j k l
      have e : (x • E i j) * (y • E k l) - (y • E k l) * (x • E i j) = (x * y) • (E i j * E k l - E k l * E i j) := by
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub, mul_comm y x]
      rw [actL_single, actL_single, e, g, hm, hm, map_sub]
      by_cases h1 : j = k <;> by_cases h2 : l = i <;> simp [h1, h2, actL_single, smul_sub, mul_comm y x]

end Act

section Semi

variable {R : Type*} [Ring R] [Algebra ℂ R]

theorem semiconj_aeval {a b z : R} (h : a * z = z * b) (p : ℂ[X]) : aeval a p * z = z * aeval b p := by
  induction p using Polynomial.induction_on with
  | C r => simp [Algebra.commutes]
  | add p q hp hq => simp [add_mul, mul_add, hp, hq]
  | monomial k r ih =>
    have e : ∀ w : R, aeval w (C r * X ^ (k + 1) : ℂ[X]) = aeval w (C r * X ^ k : ℂ[X]) * w := fun w => by
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    rw [e, e, mul_assoc, h, ← mul_assoc, ih, mul_assoc]

end Semi

def Good (c : ℝ) (p : ℂ[X]) : Prop := p ≠ 0 ∧ ∀ z : ℂ, p.eval z = 0 → z.re < c

theorem Good.mul {c : ℝ} {p q : ℂ[X]} (hp : Good c p) (hq : Good c q) : Good c (p * q) :=
  ⟨mul_ne_zero hp.1 hq.1, fun z hz => by
    rw [eval_mul, mul_eq_zero] at hz
    exact hz.elim (hp.2 z) (hq.2 z)⟩

theorem good_one (c : ℝ) : Good c 1 := ⟨one_ne_zero, by simp⟩

theorem good_lin {c : ℝ} {z : ℂ} (h : z.re < c) : Good c (X - C z) :=
  ⟨X_sub_C_ne_zero z, fun w hw => by
    have : w = z := by simpa [sub_eq_zero] using hw
    rwa [this]⟩

theorem Good.shift {c : ℝ} {p : ℂ[X]} (hp : Good c p) {k : ℝ} (hk : 0 ≤ k) :
    Good c (p.comp (X + C (k : ℂ))) := by
  refine ⟨fun h0 => hp.1 ?_, fun z hz => ?_⟩
  · have : (p.comp (X + C (k : ℂ))).comp (X - C (k : ℂ)) = p := by
      rw [comp_assoc]; simp
    rw [← this, h0, zero_comp]
  · have h := hp.2 (z + k) (by simpa [eval_comp] using hz)
    simp only [Complex.add_re, Complex.ofReal_re] at h
    linarith

section Filt

variable {n : ℕ} {X : GMod n} {A : Matrix (Fin n) (Fin n) ℂ}

theorem act_weight (X : GMod n) {A Y : Matrix (Fin n) (Fin n) ℂ} {k : ℂ} (hw : A * Y - Y * A = k • Y) :
    actM X.E A * actM X.E Y = actM X.E Y * (actM X.E A + algebraMap ℂ _ k) := by
  have h := actL_comm X.gl A Y
  rw [hw, map_smul] at h
  simp only [actL_apply] at h
  rw [mul_add, ← Algebra.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← h]
  abel

def SS (F : Filt X A) (c : ℝ) : Submodule ℂ (Module.Dual ℂ X.V) where
  carrier := {ψ | ψ ∈ W F ∧ ∃ p, Good c p ∧ ψ ∘ₗ aeval (actM X.E A) p = 0}
  add_mem' := by
    rintro ψ₁ ψ₂ ⟨h₁, p₁, g₁, e₁⟩ ⟨h₂, p₂, g₂, e₂⟩
    refine ⟨add_mem h₁ h₂, p₁ * p₂, g₁.mul g₂, ?_⟩
    have a₁ : ψ₁ ∘ₗ aeval (actM X.E A) (p₁ * p₂) = (ψ₁ ∘ₗ aeval (actM X.E A) p₁) ∘ₗ aeval (actM X.E A) p₂ := by
      rw [map_mul]; rfl
    have a₂ : ψ₂ ∘ₗ aeval (actM X.E A) (p₁ * p₂) = (ψ₂ ∘ₗ aeval (actM X.E A) p₂) ∘ₗ aeval (actM X.E A) p₁ := by
      rw [mul_comm, map_mul]; rfl
    rw [LinearMap.add_comp, a₁, a₂, e₁, e₂]
    simp
  zero_mem' := ⟨zero_mem _, 1, good_one c, by simp⟩
  smul_mem' := by
    rintro a ψ ⟨h, p, g, e⟩
    exact ⟨Submodule.smul_mem _ a h, p, g, by rw [LinearMap.smul_comp, e, smul_zero]⟩

theorem SS_le (F : Filt X A) (c : ℝ) : SS F c ≤ W F := fun _ h => h.1

theorem W_weight (F : Filt X A) {Y : Matrix (Fin n) (Fin n) ℂ} {k : ℤ} (hw : A * Y - Y * A = (k : ℂ) • Y)
    {ψ : Module.Dual ℂ X.V} (hψ : ψ ∈ W F) : ψ ∘ₗ actM X.E Y ∈ W F := by
  obtain ⟨s, hs⟩ := hψ
  refine ⟨s - k, fun u hu => ?_⟩
  have := F.shift Y k hw (s - k) u hu
  rw [sub_add_cancel] at this
  exact hs _ this

theorem SS_weight (F : Filt X A) (c : ℝ) {Y : Matrix (Fin n) (Fin n) ℂ} {k : ℤ} (hk : 0 ≤ k)
    (hw : A * Y - Y * A = (k : ℂ) • Y) {ψ : Module.Dual ℂ X.V} (hψ : ψ ∈ SS F c) :
    ψ ∘ₗ actM X.E Y ∈ SS F c := by
  obtain ⟨h, p, g, e⟩ := hψ
  refine ⟨W_weight F hw h, p.comp (Polynomial.X + C ((k : ℝ) : ℂ)), g.shift (k := (k : ℝ)) (by exact_mod_cast hk), ?_⟩
  have e1 := act_weight X hw
  have e2 := semiconj_aeval e1 p
  have e3 : aeval (actM X.E A) (p.comp (Polynomial.X + C ((k : ℝ) : ℂ))) = aeval (actM X.E A + algebraMap ℂ _ (k : ℂ)) p := by
    rw [aeval_comp]
    simp
  rw [e3]
  have : (ψ ∘ₗ actM X.E Y) ∘ₗ aeval (actM X.E A + algebraMap ℂ _ (k : ℂ)) p =
      ψ ∘ₗ (actM X.E Y * aeval (actM X.E A + algebraMap ℂ _ (k : ℂ)) p) := rfl
  rw [this, ← e2]
  change (ψ ∘ₗ aeval (actM X.E A) p) ∘ₗ actM X.E Y = 0
  rw [e]
  simp

def Stab (M : Submodule ℂ (Module.Dual ℂ X.V)) : Prop :=
  ∀ (Y : Matrix (Fin n) (Fin n) ℂ), ∀ ψ ∈ M, ψ ∘ₗ actM X.E Y ∈ M

def Wm (F : Filt X A) (c : ℝ) : Submodule ℂ (Module.Dual ℂ X.V) :=
  sSup {M | M ≤ SS F c ∧ Stab M}

theorem Wm_le (F : Filt X A) (c : ℝ) : Wm F c ≤ SS F c := sSup_le fun _ h => h.1

theorem Wm_stab (F : Filt X A) (c : ℝ) : Stab (Wm F c) := by
  intro Y
  have : Wm F c ≤ (Wm F c).comap (actM X.E Y).dualMap :=
    sSup_le fun M hM ψ hψ => (le_sSup hM : M ≤ Wm F c) (hM.2 Y ψ hψ)
  exact fun ψ hψ => this hψ

end Filt

section Basis

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}

def Ym (B : GradBasis A) (p q : Fin n) : Matrix (Fin n) (Fin n) ℂ := B.U * Matrix.single p q 1 * B.Ui

theorem mat_sum (B : GradBasis A) (M : Matrix (Fin n) (Fin n) ℂ) :
    M = ∑ p, ∑ q, (B.Ui * M * B.U) p q • Ym B p q := by
  set G := B.Ui * M * B.U with hG
  have h1 : M = B.U * G * B.Ui := by
    rw [hG]
    calc M = (B.U * B.Ui) * M * (B.U * B.Ui) := by rw [B.hU]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have h2 := Matrix.matrix_eq_sum_single G
  calc M = B.U * G * B.Ui := h1
    _ = B.U * (∑ p, ∑ q, Matrix.single p q (G p q)) * B.Ui := by rw [← h2]
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      have : Matrix.single p q (G p q) = G p q • Matrix.single p q (1 : ℂ) := by simp
      rw [this, Ym, Matrix.mul_smul, Matrix.smul_mul]

def dz : Fin 3 → ℤ := ![-1, 0, 1]

theorem dz_mono {a b : Fin 3} (h : a ≤ b) : dz a ≤ dz b := by
  revert a b; decide

theorem dv_eq (i : Fin 3) : (![-1, 0, 1] : Fin 3 → ℂ) i = (dz i : ℂ) := by
  fin_cases i <;> simp [dz]

theorem conj_weight {U Ui : Matrix (Fin n) (Fin n) ℂ} (hUi : Ui * U = 1) (d : Fin n → ℂ) (p q : Fin n) :
    (U * Matrix.diagonal d * Ui) * (U * Matrix.single p q 1 * Ui) -
      (U * Matrix.single p q 1 * Ui) * (U * Matrix.diagonal d * Ui) =
      (d p - d q) • (U * Matrix.single p q 1 * Ui) := by
  have h1 : (U * Matrix.diagonal d * Ui) * (U * Matrix.single p q 1 * Ui) =
      U * (Matrix.diagonal d * Matrix.single p q 1) * Ui := by
    calc _ = U * Matrix.diagonal d * (Ui * U) * Matrix.single p q 1 * Ui := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUi]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  have h2 : (U * Matrix.single p q 1 * Ui) * (U * Matrix.diagonal d * Ui) =
      U * (Matrix.single p q 1 * Matrix.diagonal d) * Ui := by
    calc _ = U * Matrix.single p q 1 * (Ui * U) * Matrix.diagonal d * Ui := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUi]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  have h3 : Matrix.diagonal d * Matrix.single p q (1 : ℂ) = d p • Matrix.single p q 1 := by
    ext a b
    by_cases ha : p = a
    · subst ha; simp [Matrix.diagonal_mul, Matrix.single_apply]
    · simp [Matrix.diagonal_mul, Matrix.single_apply, ha]
  have h4 : Matrix.single p q (1 : ℂ) * Matrix.diagonal d = d q • Matrix.single p q 1 := by
    ext a b
    by_cases hb : q = b
    · subst hb; simp [Matrix.mul_diagonal, Matrix.single_apply]
    · simp [Matrix.mul_diagonal, Matrix.single_apply, hb]
  rw [h1, h2, h3, h4, sub_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem Ym_weight (B : GradBasis A) (p q : Fin n) :
    A * Ym B p q - Ym B p q * A = (((dz (bl B p) - dz (bl B q) : ℤ)) : ℂ) • Ym B p q := by
  have hA := B.eq
  have h := conj_weight B.hUi (fun p => ((![-1, 0, 1] : Fin 3 → ℂ) ((stdBlocks (dims n B.j) B.hj).symm p).1)) p q
  rw [← hA] at h
  have e : ∀ p, (![-1, 0, 1] : Fin 3 → ℂ) ((stdBlocks (dims n B.j) B.hj).symm p).1 = (dz (bl B p) : ℂ) :=
    fun p => dv_eq _
  simp only [e] at h
  push_cast
  exact h

end Basis

section Gen

variable {n : ℕ} {X : GMod n} {A : Matrix (Fin n) (Fin n) ℂ}

theorem mem_Wm (F : Filt X A) (B : GradBasis A) (c : ℝ) {φ : Module.Dual ℂ X.V} (hφ : φ ∈ SS F c)
    (hn : ∀ p q, bl B p < bl B q → φ ∘ₗ Eb X B p q ∈ Wm F c) : φ ∈ Wm F c := by
  set Cl : Set (Submodule ℂ (Module.Dual ℂ X.V)) := {M | Wm F c ≤ M ∧ φ ∈ M ∧
    ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (k : ℤ), 0 ≤ k → A * Y - Y * A = (k : ℂ) • Y → ∀ ψ ∈ M, ψ ∘ₗ actM X.E Y ∈ M} with hCl
  set T := sInf Cl with hT
  have hTmem : ∀ M ∈ Cl, T ≤ M := fun M hM => sInf_le hM
  have hTW : Wm F c ≤ T := le_sInf fun M hM => hM.1
  have hTφ : φ ∈ T := (Submodule.mem_sInf).2 fun M hM => hM.2.1
  have hTY : ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (k : ℤ), 0 ≤ k → A * Y - Y * A = (k : ℂ) • Y →
      ∀ ψ ∈ T, ψ ∘ₗ actM X.E Y ∈ T := fun Y k hk hw ψ hψ =>
    (Submodule.mem_sInf).2 fun M hM => hM.2.2 Y k hk hw ψ ((Submodule.mem_sInf).1 hψ M hM)
  have hTS : T ≤ SS F c := hTmem _ ⟨Wm_le F c, hφ, fun Y k hk hw ψ hψ => SS_weight F c hk hw hψ⟩

  let R : Submodule ℂ (Module.Dual ℂ X.V) :=
    { carrier := {ψ | ψ ∈ T ∧ ∀ Y : Matrix (Fin n) (Fin n) ℂ, ψ ∘ₗ actM X.E Y ∈ T}
      add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun Y => by
        rw [LinearMap.add_comp]; exact add_mem (ha.2 Y) (hb.2 Y)⟩
      zero_mem' := ⟨zero_mem _, fun Y => by rw [LinearMap.zero_comp]; exact zero_mem _⟩
      smul_mem' := fun a ψ h => ⟨Submodule.smul_mem _ a h.1, fun Y => by
        rw [LinearMap.smul_comp]; exact Submodule.smul_mem _ a (h.2 Y)⟩ }
  have hRW : Wm F c ≤ R := fun ψ hψ => ⟨hTW hψ, fun Y => hTW (Wm_stab F c Y ψ hψ)⟩
  have hRφ : φ ∈ R := by
    refine ⟨hTφ, fun Y => ?_⟩
    have e : actM X.E Y = ∑ p, ∑ q, (B.Ui * Y * B.U) p q • Eb X B p q := by
      conv_lhs => rw [mat_sum B Y]
      rw [← actL_apply, map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul]
      rfl
    have e2 : φ ∘ₗ actM X.E Y = ∑ p, ∑ q, (B.Ui * Y * B.U) p q • (φ ∘ₗ Eb X B p q) := by
      refine LinearMap.ext fun v => ?_
      simp [e, LinearMap.sum_apply, map_sum]
    rw [e2]
    refine sum_mem fun p _ => sum_mem fun q _ => Submodule.smul_mem _ _ ?_
    by_cases h : bl B p < bl B q
    · exact hTW (hn p q h)
    · exact hTY (Ym B p q) (dz (bl B p) - dz (bl B q)) (sub_nonneg.2 (dz_mono (not_lt.1 h))) (Ym_weight B p q) φ hTφ
  have hRY : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (k : ℤ), 0 ≤ k → A * Z - Z * A = (k : ℂ) • Z →
      ∀ ψ ∈ R, ψ ∘ₗ actM X.E Z ∈ R := by
    intro Z k hk hw ψ hψ
    refine ⟨hTY Z k hk hw ψ hψ.1, fun Y => ?_⟩
    have e : actM X.E Z * actM X.E Y = actM X.E Y * actM X.E Z + actM X.E (Z * Y - Y * Z) := by
      have := actL_comm X.gl Z Y
      simp only [actL_apply] at this
      rw [← this]
      abel
    have e2 : (ψ ∘ₗ actM X.E Z) ∘ₗ actM X.E Y =
        (ψ ∘ₗ actM X.E Y) ∘ₗ actM X.E Z + ψ ∘ₗ actM X.E (Z * Y - Y * Z) := by
      refine LinearMap.ext fun v => ?_
      have := LinearMap.congr_fun e v
      simp only [Module.End.mul_apply, LinearMap.add_apply] at this
      simp [this]
    rw [e2]
    exact add_mem (hTY Z k hk hw _ (hψ.2 Y)) (hψ.2 _)
  have hTR : T ≤ R := hTmem _ ⟨hRW, hRφ, hRY⟩
  have hst : Stab T := fun Y ψ hψ => (hTR hψ).2 Y
  have hle : T ≤ Wm F c := le_sSup ⟨hTS, hst⟩
  exact hle hTφ

end Gen

section Final

variable {n : ℕ} {X : GMod n} {A : Matrix (Fin n) (Fin n) ℂ}

theorem top_of_SS (F : Filt X A) (c : ℝ) (hS : SS F c = W F) : F.N c = ⊤ := by
  by_contra hN
  obtain ⟨u, hu⟩ : ∃ u, u ∉ F.N c := by
    by_contra h
    push_neg at h
    exact hN (Submodule.eq_top_iff'.2 h)
  obtain ⟨s0, hs0⟩ := F.top
  have hc : c < s0 := by
    by_contra h
    exact hN (top_le_iff.1 (hs0 ▸ F.mono _ _ (not_lt.1 h)))
  set T := actM X.E A with hT
  have hstab : ∀ v ∈ F.N c, T v ∈ F.N c := fun v hv => by
    have := F.shift A 0 (by simp) c v hv
    simpa using this
  have hstab' : ∀ (p : ℂ[X]), ∀ v ∈ F.N c, aeval T p v ∈ F.N c := by
    intro p
    induction p using Polynomial.induction_on with
    | C r => intro v hv; simpa [Algebra.algebraMap_eq_smul_one] using Submodule.smul_mem _ r hv
    | add p q hp hq => intro v hv; simpa using add_mem (hp v hv) (hq v hv)
    | monomial k r ih =>
      intro v hv
      have e : aeval T (C r * Polynomial.X ^ (k + 1) : ℂ[X]) v = aeval T (C r * Polynomial.X ^ k : ℂ[X]) (T v) := by
        rw [pow_succ, ← mul_assoc, map_mul, aeval_X]; rfl
      rw [e]
      exact ih _ (hstab v hv)
  let I : Ideal ℂ[X] :=
    { carrier := {p | aeval T p u ∈ F.N c}
      add_mem' := fun {a b} ha hb => by
        simpa using add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a p hp => by
        have : aeval T (a • p) u = aeval T a (aeval T p u) := by
          rw [smul_eq_mul, map_mul]; rfl
        show aeval T (a • p) u ∈ F.N c
        rw [this]
        exact hstab' a _ hp }
  have hI : ∀ p, p ∈ I ↔ aeval T p u ∈ F.N c := fun p => Iff.rfl
  obtain ⟨lam, hre, hlam⟩ : ∃ lam : ℂ, c ≤ lam.re ∧ ∀ p ∈ I, p.eval lam = 0 := by
    by_cases h0 : I = ⊥
    · refine ⟨c, by simp, fun p hp => ?_⟩
      rw [h0, Ideal.mem_bot] at hp
      simp [hp]
    · set m := Submodule.IsPrincipal.generator I with hm
      have hmI : m ∈ I := Submodule.IsPrincipal.generator_mem I
      have hm0 : m ≠ 0 := fun e => h0 ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).2 e)
      have hdeg : m.degree ≠ 0 := fun e => by
        have hunit : IsUnit m := Polynomial.isUnit_iff_degree_eq_zero.2 e
        have : (1 : ℂ[X]) ∈ I := by
          rw [I.eq_top_of_isUnit_mem hmI hunit]; trivial
        have := (hI 1).1 this
        simp at this
        exact hu this
      obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_root m hdeg
      obtain ⟨r, hr⟩ := Polynomial.dvd_iff_isRoot.2 hlam
      have hr0 : r ≠ 0 := fun e => hm0 (by rw [hr, e, mul_zero])
      have hrI : r ∉ I := fun h => by
        have hd : m ∣ r := (Submodule.IsPrincipal.mem_iff_generator_dvd I).1 h
        have h1 := Polynomial.natDegree_le_of_dvd hd hr0
        have h2 : m.natDegree = 1 + r.natDegree := by
          rw [hr, natDegree_mul (X_sub_C_ne_zero lam) hr0, natDegree_X_sub_C]
        omega
      refine ⟨lam, ?_, fun p hp => ?_⟩
      · have hw : aeval T r u ∉ F.N c := hrI
        have hz : T (aeval T r u) - lam • aeval T r u ∈ F.N c := by
          have e : aeval T m u = T (aeval T r u) - lam • aeval T r u := by
            rw [hr, map_mul]
            simp [Algebra.algebraMap_eq_smul_one]
          rw [← e]
          exact hmI
        exact (F.eig s0 c hc hs0 lam _ hw hz).1
      · obtain ⟨g, hg⟩ := (Submodule.IsPrincipal.mem_iff_generator_dvd I).1 hp
        rw [hg, eval_mul, hlam.eq_zero, zero_mul]
  let g : ℂ[X] →ₗ[ℂ] X.V :=
    { toFun := fun p => aeval T p u
      map_add' := fun p q => by simp
      map_smul' := fun a p => by simp }
  let f0 : ℂ[X] →ₗ[ℂ] X.V ⧸ F.N c := (F.N c).mkQ ∘ₗ g
  have hker : Polynomial.leval lam ∈ (LinearMap.ker f0).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro p hp
    have : aeval T p u ∈ F.N c := by
      have h2 : (F.N c).mkQ (g p) = 0 := hp
      have h3 : g p ∈ F.N c := by simpa using h2
      exact h3
    simpa using hlam p this
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hker
  obtain ⟨ψb, hψb⟩ := hker
  set ψ : Module.Dual ℂ X.V := ψb ∘ₗ (F.N c).mkQ with hψ
  have hψW : ψ ∈ W F := ⟨c, fun v hv => by
    have : (F.N c).mkQ v = 0 := by simpa using hv
    simp [hψ, this]⟩
  rw [← hS] at hψW
  obtain ⟨-, p, hp, hp0⟩ := hψW
  have e : p.eval lam = ψ (aeval T p u) := by
    have := LinearMap.congr_fun hψb p
    simpa [f0, g, hψ] using this.symm
  have e0 : ψ (aeval T p u) = 0 := LinearMap.congr_fun hp0 u
  have := hp.2 lam (e.trans e0)
  linarith

end Final

section Eig

variable {n : ℕ} {X : GMod n} {A : Matrix (Fin n) (Fin n) ℂ}

def trB (X : GMod n) (B : GradBasis A) (i : Fin 3) : Module.End ℂ X.V :=
  ∑ k : Fin (dims n B.j i), Eb X B (stdBlocks (dims n B.j) B.hj ⟨i, k⟩) (stdBlocks (dims n B.j) B.hj ⟨i, k⟩)

theorem tr_mem (B : GradBasis A) (χ : Fin n → ℂ) (W' : Submodule ℂ (Module.Dual ℂ X.V))
    {φ : Module.Dual ℂ X.V} {L : Fin n → Fin 3} (hL : IsLabel B.j L)
    (h : ∀ i Y, φ ∘ₗ Qb X B i Y - plab χ L i Y • φ ∈ W') (i : Fin 3) :
    φ ∘ₗ trB X B i - (∑ s ∈ univ.filter (fun s => L s = i), χ s +
      (dims n B.j i : ℂ) * (modExp (fun i => Fin (dims n B.j i)) i : ℂ) / 2) • φ ∈ W' := by
  have hc := hL i
  rcases Nat.eq_zero_or_pos (dims n B.j i) with h0 | hm
  · have hemp : IsEmpty (Fin (dims n B.j i)) := by rw [h0]; infer_instance
    have e1 : trB X B i = 0 := by
      unfold trB
      rw [Finset.univ_eq_empty, Finset.sum_empty]
    have e2 : univ.filter (fun s => L s = i) = ∅ := Finset.card_eq_zero.1 (hc.trans h0)
    rw [e1, e2, h0]
    simp
  · set m := dims n B.j i with hmdef
    set e : ℂ := (modExp (fun i => Fin (dims n B.j i)) i : ℂ) with he
    set a : ℂ := ((m : ℂ) - 1) / 2 - e / 2 with ha
    set P : ℂ[X] := ∏ s ∈ univ.filter (fun s => L s = i), (Polynomial.X + C (χ s)) with hP
    have hPm : P.Monic := monic_prod_of_monic _ _ fun s _ => monic_X_add_C _
    have hPd : P.natDegree = m := by
      rw [hP, natDegree_prod_of_monic _ _ fun s _ => monic_X_add_C _]
      simp [hc]
    have hx := extract W' φ hm
      (fun p q : Fin m => Eb X B (stdBlocks (dims n B.j) B.hj ⟨i, p⟩) (stdBlocks (dims n B.j) B.hj ⟨i, q⟩))
      a P hPd hPm (fun Y => by
        have := h i Y
        have e1 : Y + a = Y + ((m : ℂ) - 1) / 2 - e / 2 := by rw [ha]; ring
        have e2 : P.eval Y = plab χ L i Y := by
          simp [hP, plab, eval_prod]
        rw [e1, e2]
        exact this)
    have hcoef := prod_coeff (univ.filter fun s => L s = i) χ hc hm
    rw [← hP] at hcoef
    rw [hcoef] at hx
    have e3 : ∑ s ∈ univ.filter (fun s => L s = i), χ s - (m : ℂ) * a + (m : ℂ) * ((m : ℂ) - 1) / 2 =
        ∑ s ∈ univ.filter (fun s => L s = i), χ s + (m : ℂ) * e / 2 := by
      rw [ha]; ring
    rw [e3] at hx
    exact hx

theorem block_standard (B : GradBasis A) (i : Fin 3) (k : Fin (dims n B.j i)) :
    bl B (stdBlocks (dims n B.j) B.hj ⟨i, k⟩) = i := by
  simp [bl]

theorem sum_blocks (B : GradBasis A) {N : Type*} [AddCommMonoid N] (f : Fin n → N) :
    ∑ p, f p = ∑ k : Fin (dims n B.j 0), f (stdBlocks (dims n B.j) B.hj ⟨0, k⟩) +
      (∑ k : Fin (dims n B.j 1), f (stdBlocks (dims n B.j) B.hj ⟨1, k⟩) +
      ∑ k : Fin (dims n B.j 2), f (stdBlocks (dims n B.j) B.hj ⟨2, k⟩)) := by
  rw [← (stdBlocks (dims n B.j) B.hj).sum_comp f, Fintype.sum_sigma, Fin.sum_univ_three, add_assoc]

theorem A_eq (B : GradBasis A) : A = ∑ p, (dz (bl B p) : ℂ) • Ym B p p := by
  have hA := B.eq
  have e : Matrix.diagonal (fun p => ((![-1, 0, 1] : Fin 3 → ℂ) ((stdBlocks (dims n B.j) B.hj).symm p).1)) =
      ∑ p, (dz (bl B p) : ℂ) • Matrix.single p p (1 : ℂ) := by
    ext a b
    rw [Matrix.sum_apply]
    by_cases h : a = b
    · subst h
      rw [Finset.sum_eq_single a]
      · simp [dv_eq, bl]
      · intro c _ hc
        simp [Matrix.single_apply, hc]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [Matrix.diagonal_apply, h]
      · intro c _
        by_cases hc : c = a
        · subst hc; simp [Matrix.single_apply, h]
        · simp [Matrix.single_apply, hc]
  have hA2 : A = B.U * (∑ p, (dz (bl B p) : ℂ) • Matrix.single p p (1 : ℂ)) * B.Ui := by
    rw [← e]; exact hA
  calc A = _ := hA2
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Ym]

theorem act_A (X : GMod n) (B : GradBasis A) : actM X.E A = trB X B 2 - trB X B 0 := by
  conv_lhs => rw [A_eq B]
  rw [← actL_apply, map_sum, sum_blocks B]
  simp only [map_smul, block_standard]
  have e : ∀ p, actL X.E (Ym B p p) = Eb X B p p := fun _ => rfl
  simp only [e, ← Finset.smul_sum]
  simp [dz, trB]
  abel

theorem rho_eq (B : GradBasis A) : rhoA A = (B.j : ℝ) * ((n : ℝ) - B.j) := by
  have htr : Matrix.trace ((1 / 2 : ℂ) • (A * A + A)) = (B.j : ℂ) := by
    have h1 : A = ∑ p, (dz (bl B p) : ℂ) • Ym B p p := A_eq B
    have hA := B.eq
    set d : Fin n → ℂ := fun p => ((![-1, 0, 1] : Fin 3 → ℂ) ((stdBlocks (dims n B.j) B.hj).symm p).1) with hd
    have h2 : A * A + A = B.U * Matrix.diagonal (fun p => d p * d p + d p) * B.Ui := by
      have e : (B.U * Matrix.diagonal d * B.Ui) * (B.U * Matrix.diagonal d * B.Ui) =
          B.U * (Matrix.diagonal d * Matrix.diagonal d) * B.Ui := by
        calc _ = B.U * Matrix.diagonal d * (B.Ui * B.U) * Matrix.diagonal d * B.Ui := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [B.hUi]; simp only [Matrix.mul_assoc, Matrix.mul_one]
      calc A * A + A = (B.U * Matrix.diagonal d * B.Ui) * (B.U * Matrix.diagonal d * B.Ui) +
            B.U * Matrix.diagonal d * B.Ui := by rw [← hA]
        _ = _ := by
          rw [e, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
    rw [Matrix.trace_smul, h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, B.hUi, Matrix.one_mul,
      Matrix.trace_diagonal, sum_blocks B]
    have e : ∀ (i : Fin 3) (k : Fin (dims n B.j i)),
        d (stdBlocks (dims n B.j) B.hj ⟨i, k⟩) = (![-1, 0, 1] : Fin 3 → ℂ) i := fun i k => by
      simp [hd]
    simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [dims]
    ring
  simp only [rhoA, htr]
  simp

theorem modExp0 (j : ℕ) (h : 2 * j ≤ n) : (modExp (fun i => Fin (dims n j i)) 0 : ℂ) = (n : ℂ) - j := by
  have : ((n - 2 * j : ℕ) : ℂ) = (n : ℂ) - 2 * j := by push_cast [Nat.cast_sub h]; ring
  unfold modExp
  simp only [Finset.sum_filter, Fin.sum_univ_three, Fintype.card_fin]
  simp [dims, this]
  ring

theorem modExp2 (j : ℕ) (h : 2 * j ≤ n) : (modExp (fun i => Fin (dims n j i)) 2 : ℂ) = -((n : ℂ) - j) := by
  have : ((n - 2 * j : ℕ) : ℂ) = (n : ℂ) - 2 * j := by push_cast [Nat.cast_sub h]; ring
  unfold modExp
  simp only [Finset.sum_filter, Fin.sum_univ_three, Fintype.card_fin]
  simp [dims, this]
  ring

theorem eig_mod (B : GradBasis A) (χ : Fin n → ℂ) (W' : Submodule ℂ (Module.Dual ℂ X.V))
    {φ : Module.Dual ℂ X.V} {L : Fin n → Fin 3} (hL : IsLabel B.j L)
    (h : ∀ i Y, φ ∘ₗ Qb X B i Y - plab χ L i Y • φ ∈ W') :
    φ ∘ₗ actM X.E A - (deg χ L - (rhoA A : ℂ)) • φ ∈ W' := by
  have hj : 2 * B.j ≤ n := by
    have := B.hj
    simp [dims, Fin.sum_univ_three] at this
    omega
  have h2 := tr_mem B χ W' hL h 2
  have h0 := tr_mem B χ W' hL h 0
  have e : φ ∘ₗ actM X.E A - (deg χ L - (rhoA A : ℂ)) • φ =
      (φ ∘ₗ trB X B 2 - (∑ s ∈ univ.filter (fun s => L s = 2), χ s +
        (dims n B.j 2 : ℂ) * (modExp (fun i => Fin (dims n B.j i)) 2 : ℂ) / 2) • φ) -
      (φ ∘ₗ trB X B 0 - (∑ s ∈ univ.filter (fun s => L s = 0), χ s +
        (dims n B.j 0 : ℂ) * (modExp (fun i => Fin (dims n B.j i)) 0 : ℂ) / 2) • φ) := by
    rw [act_A X B, rho_eq B, modExp0 B.j hj, modExp2 B.j hj]
    have d0 : dims n B.j 0 = B.j := rfl
    have d2 : dims n B.j 2 = B.j := rfl
    rw [d0, d2]
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_sub, smul_eq_mul, deg]
    push_cast
    ring
  rw [e]
  exact sub_mem h2 h0

end Eig

theorem degree : CompanionTheory.RgExh.Dec.J.Degree := by
  intro n X A F B χ Λ c _ _ hPP hΛ
  refine top_of_SS F c ?_
  by_contra hne
  have hWne : Wm F c ≠ W F := fun e =>
    hne (le_antisymm (SS_le F c) (e ▸ Wm_le F c))
  have hst : ∀ a b, ∀ φ ∈ Wm F c, contraE X a b φ ∈ Wm F c := by
    intro a b φ hφ
    have := Wm_stab F c (Matrix.single a b 1) φ hφ
    rw [act_single] at this
    have e : contraE X a b φ = -(φ ∘ₗ X.E a b) := rfl
    rw [e]
    exact neg_mem this
  obtain ⟨φ, hφW, hφ', hn, L, hLΛ, hLab, hq⟩ := hPP (Wm F c) ((Wm_le F c).trans (SS_le F c)) hst hWne
  have hz := eig_mod B χ (Wm F c) hLab hq
  set z : ℂ := deg χ L - (rhoA A : ℂ) with hzdef
  have hzre : z.re < c := by
    have := hΛ L hLΛ
    simp only [hzdef, Complex.sub_re, Complex.ofReal_re]
    linarith
  obtain ⟨-, p, hp, hp0⟩ := Wm_le F c hz
  have hφS : φ ∈ SS F c := by
    refine ⟨hφW, (Polynomial.X - C z) * p, (good_lin hzre).mul hp, ?_⟩
    have e : φ ∘ₗ aeval (actM X.E A) ((Polynomial.X - C z) * p) =
        (φ ∘ₗ actM X.E A - z • φ) ∘ₗ aeval (actM X.E A) p := by
      refine LinearMap.ext fun v => ?_
      simp [map_mul, Algebra.algebraMap_eq_smul_one]
    rw [e, hp0]
  exact hφ' (mem_Wm F B c hφS fun p q h => hn p q h)

end GlobalTheory.CompanionTheory.RgExhDec.DegreeP

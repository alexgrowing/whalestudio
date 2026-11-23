import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruenceLiftLieElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormHasUnitVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruencePrescribedDetStatement
open Matrix GlobalTheory.SUCong

namespace GlobalTheory.SUCong

theorem levSurj_cT_sub {R : Type} [CommRing R] {n : Type} (τ : R →+* R) (M N : Matrix n n R) :
    Formalism.UG.cT τ (M - N) = Formalism.UG.cT τ M - Formalism.UG.cT τ N := by
  ext i j; simp [Formalism.UG.cT]

theorem levSurj_cT_smul {R : Type} [CommRing R] {n : Type} (τ : R →+* R) (c : R) (M : Matrix n n R) :
    Formalism.UG.cT τ (c • M) = τ c • Formalism.UG.cT τ M := by
  ext i j; simp [Formalism.UG.cT]

theorem levSurj_cT_cT {R : Type} [CommRing R] {n : Type} (τ : R →+* R) (hτ : ∀ a, τ (τ a) = a)
    (M : Matrix n n R) : Formalism.UG.cT τ (Formalism.UG.cT τ M) = M := by
  ext i j; simp [Formalism.UG.cT, hτ]

theorem levSurj_unitOne : ∀ {R : Type} [CommRing R] (τ : R →+* R) (p : R), (∀ a, τ (τ a) = a) → τ p = p →
    (∀ a, τ a = a → (¬ ∃ s, a = p * s) → IsUnit a) → (¬ ∃ s, p * s = 1) → ∀ s, IsUnit (1 + p * s) := by
  intro R _ τ p hτ hp hloc hnt s
  have hN : τ ((1 + p * s) * (1 + p * τ s)) = (1 + p * s) * (1 + p * τ s) := by
    simp only [map_mul, map_add, map_one, hp, hτ]; ring
  have hu := hloc _ hN (by
    rintro ⟨t, ht⟩
    exact hnt ⟨t - (s + τ s + p * s * τ s), by linear_combination (-1 : R) * ht⟩)
  exact isUnit_of_mul_isUnit_left hu

theorem levSurj_detCong : ∀ {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n R)
    (p t : R) (k : ℕ), 1 ≤ k → M.trace = p * t → ∃ s, (1 + p ^ k • M).det = 1 + p ^ (k + 1) * s := by
  intro R _ n _ _ M p t k hk hM
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine ⟨t + (det (1 + (Polynomial.X : Polynomial R) • M.map Polynomial.C)).divX.divX.eval (p ^ (j + 1)) * p ^ j, ?_⟩
  rw [det_one_add_smul, hM]; ring

theorem levSurj_skewLift : ∀ {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (τ : R →+* R)
    (H H' X₀ N : Matrix n n R) (p w t : R), (∀ a, τ (τ a) = a) → w + τ w = 1 → Formalism.UG.cT τ H = H →
    H * H' = 1 → Formalism.UG.cT τ X₀ * H + H * X₀ = p • N → X₀.trace = p * t →
    ∃ X D : Matrix n n R, X = X₀ + p • D ∧ Formalism.UG.cT τ X * H + H * X = 0 := by
  intro R _ n _ _ τ H H' X₀ N p w t hτ hw hH hHH hX₀ _
  have hH'H : H' * H = 1 := mul_eq_one_comm.mp hHH
  have hcH' : Formalism.UG.cT τ H' * H = 1 := by
    have := congrArg (Formalism.UG.cT τ) hHH
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_one, hH] at this
  have hcY : Formalism.UG.cT τ (H * X₀) = p • N - H * X₀ := by
    rw [Formalism.UG.cT_mul, hH, ← hX₀]; abel
  refine ⟨H' * (w • (H * X₀) - τ w • Formalism.UG.cT τ (H * X₀)), -(H' * (τ w • N)), ?_, ?_⟩
  · rw [hcY, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_smul,
      ← Matrix.mul_assoc, hH'H, Matrix.one_mul, Matrix.mul_smul]
    have hw' : w = 1 - τ w := eq_sub_of_add_eq hw
    generalize τ w = c at hw' ⊢
    subst hw'
    module
  · rw [Formalism.UG.cT_mul, Matrix.mul_assoc, hcH', Matrix.mul_one, ← Matrix.mul_assoc, hHH, Matrix.one_mul,
      levSurj_cT_sub, levSurj_cT_smul, levSurj_cT_smul, levSurj_cT_cT τ hτ, hτ]
    abel

end GlobalTheory.SUCong

namespace GlobalTheory.SUCong

theorem levSurj_detcT {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (τ : R →+* R) (M : Matrix n n R) : (Formalism.UG.cT τ M).det = τ M.det := by
  unfold Formalism.UG.cT; rw [det_transpose, RingHom.map_det]; rfl

theorem levSurj_core {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : R →+* R) (H H' X₀ N : Matrix n n R) (p w v t : R) (k : ℕ)
    (hτ : ∀ a, τ (τ a) = a) (hp : τ p = p) (hw : w + τ w = 1) (hv : (w - τ w) * v = 1)
    (hloc : ∀ a, τ a = a → (¬ ∃ s, a = p * s) → IsUnit a) (hnt : ¬ ∃ s, p * s = 1)
    (hH : Formalism.UG.cT τ H = H) (hHH : H * H' = 1) (hX₀ : Formalism.UG.cT τ X₀ * H + H * X₀ = p • N)
    (htr : X₀.trace = p * t) (hk : 1 ≤ k) :
    ∃ g X' D : Matrix n n R, Formalism.UG.cT τ g * H * g = H ∧ g.det = 1 ∧ g = 1 + p ^ k • X' ∧
      X' = X₀ + p • D := by
  obtain ⟨X, D₁, hX, hsk⟩ := levSurj_skewLift τ H H' X₀ N p w t hτ hw hH hHH hX₀ htr
  have hu := levSurj_unitOne τ p hτ hp hloc hnt
  obtain ⟨g₁, X₁, D₂, hg₁, hg₁e, hX₁⟩ := GlobalTheory.T.unitary_congruence_lift_lie_element τ H X p w k hτ hp hw hu hk hsk
  have htr1 : X₁.trace = p * (t + D₁.trace + D₂.trace) := by
    rw [hX₁, hX, trace_add, trace_add, trace_smul, trace_smul, htr, smul_eq_mul, smul_eq_mul]; ring
  obtain ⟨s, hs⟩ := levSurj_detCong X₁ p _ k hk htr1
  rw [← hg₁e] at hs
  obtain ⟨e, he⟩ := GlobalTheory.T.hermitian_form_has_unit_vector τ H H' p w v hτ hw hv hH hHH hloc hnt
  have hdH : IsUnit H.det := by
    have h : H.det * H'.det = 1 := by rw [← det_mul, hHH, det_one]
    exact ⟨⟨H.det, H'.det, h, by rw [mul_comm]; exact h⟩, rfl⟩
  have hdd : τ g₁.det * g₁.det = 1 := by
    have h := congrArg det hg₁
    rw [det_mul, det_mul, levSurj_detcT] at h
    apply hdH.mul_left_cancel
    linear_combination h
  obtain ⟨g₂, M, hg₂, hdet₂, hg₂e⟩ := GlobalTheory.T.unitary_congruence_prescribed_det τ H e p (τ g₁.det) (τ s) k hτ hH he
    (by rw [hτ]; exact hdd) (by rw [hs, map_add, map_one, map_mul, map_pow, hp])
  refine ⟨g₁ * g₂, X₁ + p • (g₁ * M), D₁ + D₂ + g₁ * M, ?_, ?_, ?_, ?_⟩
  · rw [Formalism.UG.cT_mul, show Formalism.UG.cT τ g₂ * Formalism.UG.cT τ g₁ * H * (g₁ * g₂) =
      Formalism.UG.cT τ g₂ * (Formalism.UG.cT τ g₁ * H * g₁) * g₂ by simp only [Matrix.mul_assoc], hg₁, hg₂]
  · rw [det_mul, hdet₂, mul_comm, hdd]
  · rw [hg₂e, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    generalize g₁ * M = G
    rw [hg₁e, smul_add, smul_smul, ← pow_succ, add_assoc]
  · rw [hX₁, hX, smul_add, smul_add]; abel

theorem levSurj_cancel {A : Type} [CommRing A] (ϖ : A) (h : ∀ a : A, ϖ * a = 0 → a = 0) :
    ∀ (k : ℕ) (a b : A), ϖ ^ k * a = ϖ ^ k * b → a = b := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro a b hab
    apply ih
    have : ϖ * (ϖ ^ k * a - ϖ ^ k * b) = 0 := by rw [pow_succ] at hab; linear_combination hab
    exact sub_eq_zero.1 (h _ this)

theorem levSurj : ∀ {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (S : Subring A)
    (σ : A →+* A) (H : Matrix n n A) (ϖ : A) (q k : ℕ), GoodRing S σ ϖ q → GoodForm S σ H → 1 ≤ k →
    ∀ Y : Matrix n n (Res S ϖ), Y ∈ skewTr S σ H ϖ →
      ∃ g ∈ congSU S σ H ϖ k, levMap S ϖ k (g : Matrix n n A) = Y := by
  intro A _ n _ _ S σ H ϖ q k hR hF hk Y hY
  obtain ⟨hσσ, hσS, hϖS, hσϖ, hnzd, ⟨w, hwS, hw1, ⟨u, huS, hwu⟩, -⟩, hloc, -⟩ := hR
  obtain ⟨hHS, hHh, H', hH'S, hHH'⟩ := hF
  obtain ⟨X₀, hX₀S, hYX, hskew, htrace⟩ := hY
  by_cases hn : IsEmpty n
  · exact ⟨1, one_mem _, funext fun i => isEmptyElim i⟩
  rw [not_isEmpty_iff] at hn
  let p : S := ⟨ϖ, hϖS⟩
  have hpI : p ∈ piIdeal S ϖ := Ideal.subset_span (show (p : A) = ϖ from rfl)
  by_cases hnt : ∃ s : S, p * s = 1
  · refine ⟨1, one_mem _, funext fun i => funext fun j => ?_⟩
    obtain ⟨s, hs⟩ := hnt
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (levMap S ϖ k ((1 : GL n A) : Matrix n n A) i j)
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Y i j)
    rw [← ha, ← hb, Ideal.Quotient.eq]
    have : a - b = p * (s * (a - b)) := by rw [← mul_assoc, hs, one_mul]
    rw [this]; exact Ideal.mul_mem_right _ _ hpI
  haveI := hn
  let τ : S →+* S := (σ.comp S.subtype).codRestrict S (fun x => hσS x x.2)
  have hτv : ∀ a : S, (τ a : A) = σ a := fun a => rfl
  have hτ : ∀ a, τ (τ a) = a := fun a => Subtype.ext (hσσ a)
  have hp : τ p = p := Subtype.ext hσϖ
  let wS : S := ⟨w, hwS⟩
  let vS : S := ⟨u, huS⟩
  have hw : wS + τ wS = 1 := Subtype.ext hw1
  have hv : (wS - τ wS) * vS = 1 := Subtype.ext hwu
  have hlocS : ∀ a : S, τ a = a → (¬ ∃ s, a = p * s) → IsUnit a := by
    intro a ha hna
    obtain ⟨b, hb, hab⟩ := hloc a a.2 (congrArg Subtype.val ha) (by
      rintro ⟨s, hs, he⟩
      exact hna ⟨⟨s, hs⟩, Subtype.ext (by simpa using he)⟩)
    exact ⟨⟨a, ⟨b, hb⟩, Subtype.ext hab, Subtype.ext (by rw [mul_comm]; exact hab)⟩, rfl⟩
  let HS : Matrix n n S := fun i j => ⟨H i j, hHS i j⟩
  let H'S : Matrix n n S := fun i j => ⟨H' i j, hH'S i j⟩
  let X₀S : Matrix n n S := fun i j => ⟨X₀ i j, hX₀S i j⟩
  have hinj : Function.Injective (fun M : Matrix n n S => M.map S.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hcTm : ∀ M : Matrix n n S, (Formalism.UG.cT τ M).map S.subtype = Formalism.UG.cT σ (M.map S.subtype) :=
    fun M => rfl
  have hHm : HS.map S.subtype = H := rfl
  have hH'm : H'S.map S.subtype = H' := rfl
  have hX₀m : X₀S.map S.subtype = X₀ := rfl
  have hHSh : Formalism.UG.cT τ HS = HS := hinj (by simp only; rw [hcTm, hHm, hHh])
  have hHHS : HS * H'S = 1 := hinj (by simp only; rw [Matrix.map_mul, hHm, hH'm, hHH', Matrix.map_one _ (map_zero _) (map_one _)])
  choose N hNS hNe using hskew
  let NS : Matrix n n S := fun i j => ⟨N i j, hNS i j⟩
  have hX₀S' : Formalism.UG.cT τ X₀S * HS + HS * X₀S = p • NS := by
    apply hinj; simp only
    rw [Matrix.map_add _ (map_add S.subtype), Matrix.map_mul, Matrix.map_mul, hcTm, hHm, hX₀m]
    ext i j
    rw [hNe i j, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, pow_one]
    rfl
  obtain ⟨t, htS, hte⟩ := htrace
  have htr : X₀S.trace = p * ⟨t, htS⟩ := by
    apply Subtype.ext
    have : ((X₀S.trace : S) : A) = X₀.trace := AddMonoidHom.map_trace S.subtype.toAddMonoidHom X₀S
    rw [this, hte, pow_one]; rfl
  obtain ⟨g, X', D, hgu, hgd, hge, hX'⟩ := levSurj_core τ HS H'S X₀S NS p wS vS ⟨t, htS⟩ k hτ hp hw hv
    hlocS hnt hHSh hHHS hX₀S' htr hk
  let gU : GL n S := Matrix.nonsingInvUnit g (by rw [hgd]; exact isUnit_one)
  have hgA : ((Formalism.UG.bc S.subtype gU : GL n A) : Matrix n n A) = g.map S.subtype := rfl
  have hgA1 : g.map S.subtype = 1 + ϖ ^ k • X'.map S.subtype := by
    rw [hge]; ext i j; simp [Matrix.one_apply, p]; split_ifs <;> simp
  refine ⟨Formalism.UG.bc S.subtype gU, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show Formalism.UG.cT σ _ * H * _ = H
    rw [hgA, ← hcTm, ← hHm, ← Matrix.map_mul, ← Matrix.map_mul, hgu]
  · rw [hgA, show g.map S.subtype = S.subtype.mapMatrix g from rfl, ← RingHom.map_det, hgd, map_one]
  · intro i j; rw [hgA]; exact (g i j).2
  · intro i j; rw [← map_inv]; exact ((gU⁻¹ : GL n S) : Matrix n n S) i j |>.2
  · intro i j; rw [hgA, hgA1]; exact ⟨X' i j, (X' i j).2, by simp⟩
  · funext i j
    have hI : InPow S ϖ k ((((Formalism.UG.bc S.subtype gU : GL n A) : Matrix n n A) - 1) i j) :=
      ⟨X' i j, (X' i j).2, by rw [hgA, hgA1]; simp⟩
    simp only [levMap, dif_pos hI]
    obtain ⟨hcS, hce⟩ := Classical.choose_spec hI
    have hc : Classical.choose hI = X' i j := by
      apply levSurj_cancel ϖ hnzd k
      rw [← hce, hgA, hgA1]; simp
    rw [hYX i j]
    simp only [red, hc, (X' i j).2, hX₀S i j, dif_pos]
    rw [Ideal.Quotient.eq]
    have : X' i j - X₀S i j = p * D i j := by rw [hX']; simp
    simp only [Subtype.coe_eta]
    rw [show (⟨X₀ i j, hX₀S i j⟩ : S) = X₀S i j from rfl, this]
    exact Ideal.mul_mem_right _ _ hpI

end GlobalTheory.SUCong

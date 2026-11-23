import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.S3x8

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3

section Key

variable {A F : Type} [CommRing A] [CommRing F]

theorem lead_top {r : ℕ} (M : Matrix (Fin r) (Fin r) A) : lead M r le_rfl = M.det := by
  unfold lead
  congr 1

theorem solveL (φ : A →+* F) (I : AddSubgroup F) (hI : ∀ a x, x ∈ I → φ a * x ∈ I) {r : ℕ}
    (N : Matrix (Fin r) (Fin r) A) (hN : IsUnit N.det) (μ w : Fin r → F)
    (h : (N.map φ) *ᵥ μ = w) (hw : ∀ a, w a ∈ I) : ∀ a, μ a ∈ I := by
  have e : μ = (N⁻¹.map φ) *ᵥ w := by
    rw [← h, Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul N hN]
    simp
  intro a
  rw [e]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact sum_mem fun c _ => hI _ _ (hw c)

theorem solveR (φ : A →+* F) (I : AddSubgroup F) (hI : ∀ a x, x ∈ I → φ a * x ∈ I) {r : ℕ}
    (N : Matrix (Fin r) (Fin r) A) (hN : IsUnit N.det) (μ w : Fin r → F)
    (h : μ ᵥ* (N.map φ) = w) (hw : ∀ a, w a ∈ I) : ∀ a, μ a ∈ I := by
  have e : μ = w ᵥ* (N⁻¹.map φ) := by
    rw [← h, Matrix.vecMul_vecMul, ← Matrix.map_mul, Matrix.mul_nonsing_inv N hN]
    simp
  intro a
  rw [e]
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
  exact sum_mem fun c _ => by rw [mul_comm]; exact hI _ _ (hw c)

theorem key (φ : A →+* F) (hφ : Function.Injective φ) (I : AddSubgroup F)
    (hI : ∀ a x, x ∈ I → φ a * x ∈ I) :
    ∀ (r : ℕ) (M M' : Matrix (Fin r) (Fin r) A) (L U : Matrix (Fin r) (Fin r) F),
      IsLowUni L → IsUpUni U → L * M'.map φ = M.map φ * U →
      (∀ a b, φ (M' a b - M a b) ∈ I) →
      (∀ (l : ℕ) (hl : l ≤ r), IsUnit (lead M l hl)) →
      (∀ a b, (L - 1) a b ∈ I) ∧ (∀ a b, (U - 1) a b ∈ I) ∧
        ∀ (l : ℕ) (hl : l ≤ r), lead M' l hl = lead M l hl := by
  intro r
  induction r with
  | zero =>
    intro M M' L U _ _ _ _ _
    refine ⟨fun a => a.elim0, fun a => a.elim0, fun l hl => ?_⟩
    obtain rfl : l = 0 := Nat.le_zero.1 hl
    simp [lead]
  | succ r ih =>
    intro M M' L U hL hU hE hd hu
    have E : ∀ a b, ∑ c, L a c * φ (M' c b) = ∑ c, φ (M a c) * U c b := fun a b => by
      have := congrFun (congrFun hE a) b
      simpa [Matrix.mul_apply] using this
    have L0 : ∀ a : Fin r, L a.castSucc (Fin.last r) = 0 := fun a =>
      hL.1 (by simp)
    have U0 : ∀ a : Fin r, U (Fin.last r) a.castSucc = 0 := fun a =>
      hU.1 (by simp)
    have hL' : IsLowUni (L.submatrix Fin.castSucc Fin.castSucc) :=
      ⟨fun i j h => hL.1 (by simpa using h), fun a => hL.2 _⟩
    have hU' : IsUpUni (U.submatrix Fin.castSucc Fin.castSucc) :=
      ⟨fun i j h => hU.1 (by simpa using h), fun a => hU.2 _⟩
    have hE' : L.submatrix Fin.castSucc Fin.castSucc * (M'.submatrix Fin.castSucc Fin.castSucc).map φ =
        (M.submatrix Fin.castSucc Fin.castSucc).map φ * U.submatrix Fin.castSucc Fin.castSucc := by
      ext a b
      have := E a.castSucc b.castSucc
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, L0, U0] at this
      simpa [Matrix.mul_apply] using this
    obtain ⟨iL, iU, il⟩ := ih (M.submatrix Fin.castSucc Fin.castSucc)
      (M'.submatrix Fin.castSucc Fin.castSucc) _ _ hL' hU' hE' (fun a b => hd _ _)
      (fun l hl => hu l (hl.trans (Nat.le_succ r)))
    have hM : IsUnit (M.submatrix Fin.castSucc Fin.castSucc).det := by
      rw [← lead_top]; exact hu r (Nat.le_succ r)
    have hM' : IsUnit (M'.submatrix Fin.castSucc Fin.castSucc).det := by
      rw [← lead_top, il r le_rfl, lead_top]; exact hM

    have cU : ∀ a : Fin r, U a.castSucc (Fin.last r) ∈ I := by
      refine solveL φ I hI _ hM (fun c => U c.castSucc (Fin.last r))
        (fun a => ∑ c, (L.submatrix Fin.castSucc Fin.castSucc - 1) a c * φ (M' c.castSucc (Fin.last r)) +
          φ (M' a.castSucc (Fin.last r) - M a.castSucc (Fin.last r))) ?_ ?_
      · funext a
        have := E a.castSucc (Fin.last r)
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, L0, hU.2] at this
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.submatrix_apply,
          Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, ite_mul, one_mul,
          zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sub]
        linear_combination -this
      · intro a
        refine add_mem (sum_mem fun c _ => ?_) (hd _ _)
        rw [mul_comm]; exact hI _ _ (iL a c)
    have rL : ∀ a : Fin r, L (Fin.last r) a.castSucc ∈ I := by
      refine solveR φ I hI _ hM' (fun c => L (Fin.last r) c.castSucc)
        (fun b => ∑ c, φ (M (Fin.last r) c.castSucc) * (U.submatrix Fin.castSucc Fin.castSucc - 1) c b -
          φ (M' (Fin.last r) b.castSucc - M (Fin.last r) b.castSucc)) ?_ ?_
      · funext b
        have := E (Fin.last r) b.castSucc
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, U0, hL.2] at this
        simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Matrix.submatrix_apply,
          Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, Matrix.one_apply, mul_ite, mul_one,
          mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_sub]
        linear_combination this
      · intro b
        refine sub_mem (sum_mem fun c _ => ?_) (hd _ _)
        exact hI _ _ (iU c b)
    refine ⟨?_, ?_, ?_⟩
    · intro a b
      refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
      · simp [hL.2]
      · simpa [Matrix.one_apply, (Fin.castSucc_lt_last b).ne'] using rL b
      · simp [L0, Matrix.one_apply, (Fin.castSucc_lt_last a).ne]
      · simpa [Matrix.one_apply] using iL a b
    · intro a b
      refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
      · simp [hU.2]
      · simp [U0, Matrix.one_apply, (Fin.castSucc_lt_last b).ne']
      · simpa [Matrix.one_apply, (Fin.castSucc_lt_last a).ne] using cU a
      · simpa [Matrix.one_apply] using iU a b
    · intro l hl
      rcases Nat.lt_or_ge l (r + 1) with h | h
      · exact il l (Nat.lt_succ_iff.1 h)
      · obtain rfl : l = r + 1 := le_antisymm hl h
        rw [lead_top, lead_top]
        apply hφ
        have := congrArg Matrix.det hE
        rw [Matrix.det_mul, Matrix.det_mul, isLowUni_det F hL, isUpUni_det F hU, one_mul, mul_one] at this
        simpa [RingHom.map_det, RingHom.mapMatrix_apply] using this

end Key

section Corner

variable {A F : Type} [CommRing A] [CommRing F]

theorem keyCm (φ : A →+* F) (hφ : Function.Injective φ) (I : AddSubgroup F)
    (hI : ∀ a x, x ∈ I → φ a * x ∈ I) {r : ℕ} (X X' : Matrix (Fin r) (Fin r) A)
    (v₂ v₁ : Matrix (Fin r) (Fin r) F) (h₂ : IsUpUni v₂) (h₁ : IsUpUni v₁)
    (hE : v₂ * X'.map φ = X.map φ * v₁) (hd : ∀ a b, φ (X' a b - X a b) ∈ I)
    (hu : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X l hl)) :
    (∀ a b, (v₂ - 1) a b ∈ I) ∧ (∀ a b, (v₁ - 1) a b ∈ I) ∧
      ∀ (l : ℕ) (hl : l ≤ r), cm X' l hl = cm X l hl := by
  have hL : IsLowUni (v₂.submatrix Fin.rev Fin.rev) :=
    ⟨fun i j h => h₂.1 (by simpa using h), fun a => h₂.2 _⟩
  have hE' : v₂.submatrix Fin.rev Fin.rev * (X'.submatrix Fin.rev id).map φ =
      (X.submatrix Fin.rev id).map φ * v₁ := by
    calc v₂.submatrix Fin.rev Fin.rev * (X'.submatrix Fin.rev id).map φ
        = (v₂ * X'.map φ).submatrix Fin.rev id :=
          Matrix.submatrix_mul_equiv v₂ (X'.map φ) Fin.rev Fin.revPerm id
      _ = (X.map φ * v₁).submatrix Fin.rev id := by rw [hE]
      _ = (X.submatrix Fin.rev id).map φ * v₁ :=
          (Matrix.submatrix_mul_equiv (X.map φ) v₁ Fin.rev (Equiv.refl _) id).symm
  obtain ⟨a1, a2, a3⟩ := key φ hφ I hI r (X.submatrix Fin.rev id) (X'.submatrix Fin.rev id) _ _ hL h₁ hE'
    (fun a b => hd _ _) (fun l hl => hu l hl)
  refine ⟨fun a b => ?_, a2, fun l hl => a3 l hl⟩
  have := a1 a.rev b.rev
  simpa [Matrix.one_apply] using this

theorem uniqCm {r : ℕ} (X v₂ v₁ : Matrix (Fin r) (Fin r) F) (h₂ : IsUpUni v₂) (h₁ : IsUpUni v₁)
    (hE : v₂ * X = X * v₁) (hu : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X l hl)) : v₂ = 1 ∧ v₁ = 1 := by
  obtain ⟨a1, a2, -⟩ := keyCm (RingHom.id F) Function.injective_id ⊥ (by simp) X X v₂ v₁ h₂ h₁
    (by simpa using hE) (by simp) hu
  constructor
  · ext a b
    have := a1 a b
    simpa [sub_eq_zero] using this
  · ext a b
    have := a2 a b
    simpa [sub_eq_zero] using this

theorem invCm {r : ℕ} (X X' v₂ v₁ : Matrix (Fin r) (Fin r) F) (h₂ : IsUpUni v₂) (h₁ : IsUpUni v₁)
    (hE : v₂ * X' = X * v₁) (hu : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X l hl)) :
    ∀ (l : ℕ) (hl : l ≤ r), cm X' l hl = cm X l hl :=
  (keyCm (RingHom.id F) Function.injective_id ⊤ (by simp) X X' v₂ v₁ h₂ h₁
    (by simpa using hE) (by simp) hu).2.2

theorem cm_map (f : A →+* F) {r : ℕ} (X : Matrix (Fin r) (Fin r) A) (l : ℕ) (hl : l ≤ r) :
    cm (X.map f) l hl = f (cm X l hl) := by
  unfold cm
  rw [RingHom.map_det]
  rfl

theorem cm_neg {r : ℕ} (X : Matrix (Fin r) (Fin r) A) (l : ℕ) (hl : l ≤ r) :
    cm (-X) l hl = (-1) ^ l * cm X l hl := by
  unfold cm
  rw [Matrix.submatrix_neg, Pi.neg_apply, Pi.neg_apply, Matrix.det_neg, Fintype.card_fin]

theorem det_of_cm {r : ℕ} (X : Matrix (Fin r) (Fin r) A) (h : IsUnit (cm X r le_rfl)) :
    IsUnit X.det := by
  have e : cm X r le_rfl = (X.submatrix Fin.revPerm id).det := by
    unfold cm
    congr 1
  rw [e, Matrix.det_permute] at h
  exact isUnit_of_mul_isUnit_right h

end Corner

section Maps

variable {A F : Type} [CommRing A] [CommRing F]

theorem map_smul' (f : A →+* F) {m n : Type} (c : A) (X : Matrix m n A) :
    (c • X).map f = f c • X.map f := by
  ext a b; simp

theorem upUni_map (f : A →+* F) {r : ℕ} {x : Matrix (Fin r) (Fin r) A} (h : IsUpUni x) :
    IsUpUni (x.map f) :=
  ⟨fun i j hij => by simp [h.1 hij], fun a => by simp [h.2 a]⟩

theorem upUni_of_map (f : A →+* F) (hf : Function.Injective f) {r : ℕ} {x : Matrix (Fin r) (Fin r) A}
    (h : IsUpUni (x.map f)) : IsUpUni x :=
  ⟨fun i j hij => hf (by simpa using h.1 hij), fun a => hf (by simpa using h.2 a)⟩

end Maps

section DVR

variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0]

theorem int_map {m n : Type} (y : Matrix m n o) : Integral o (y.map (algebraMap o k0)) := ⟨y, rfl⟩

theorem int_mul {m n p : Type} [Fintype n] {x : Matrix m n k0} {y : Matrix n p k0}
    (hx : Integral o x) (hy : Integral o y) : Integral o (x * y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, Matrix.map_mul⟩

theorem int_add {m n : Type} {x y : Matrix m n k0}
    (hx : Integral o x) (hy : Integral o y) : Integral o (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by ext; simp⟩

theorem int_sub {m n : Type} {x y : Matrix m n k0}
    (hx : Integral o x) (hy : Integral o y) : Integral o (x - y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, by ext; simp⟩

theorem int_one {m : Type} [DecidableEq m] : Integral o (1 : Matrix m m k0) :=
  ⟨1, by simp⟩

theorem int_zero {m n : Type} : Integral o (0 : Matrix m n k0) :=
  ⟨0, by ext; simp⟩

theorem int_of_entries {m n : Type} {x : Matrix m n k0}
    (h : ∀ a b, x a b ∈ (algebraMap o k0).toAddMonoidHom.range) : Integral o x := by
  choose y hy using h
  exact ⟨Matrix.of y, by ext a b; exact hy a b⟩

theorem int_of_sub_one {m : Type} [DecidableEq m] {x : Matrix m m k0}
    (h : ∀ a b, (x - 1) a b ∈ (algebraMap o k0).toAddMonoidHom.range) : Integral o x := by
  have := int_add (int_of_entries h) (int_one (o := o) (k0 := k0) (m := m))
  simpa using this

theorem range_stable (a : o) (x : k0) (hx : x ∈ (algebraMap o k0).toAddMonoidHom.range) :
    algebraMap o k0 a * x ∈ (algebraMap o k0).toAddMonoidHom.range := by
  obtain ⟨b, rfl⟩ := hx
  exact ⟨a * b, by simp⟩

variable [IsDomain o] [IsDiscreteValuationRing o]

theorem div_pi {ϖ : o} (hϖ : Irreducible ϖ) {m n : Type} (x : Matrix m n o)
    (h : x.map (IsLocalRing.residue o) = 0) : ∃ y : Matrix m n o, x = ϖ • y := by
  have : ∀ a b, ∃ c, x a b = ϖ * c := fun a b => by
    have h1 : IsLocalRing.residue o (x a b) = 0 := congrFun (congrFun h a) b
    rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at h1
    exact h1
  choose y hy using this
  exact ⟨Matrix.of y, by ext a b; simp [hy]⟩

theorem res_pi {ϖ : o} (hϖ : Irreducible ϖ) : IsLocalRing.residue o ϖ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq]
  exact Ideal.mem_span_singleton_self ϖ

end DVR

theorem centreBlocks : CentreBlocks := by
  intro F _ r ϖ j₁₁ j₁₃ j₃₃ X S S' hϖ hX
  have h1 : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hX
  have h2 : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hX
  have e1 : (j₁₁ - ϖ • (S * X)) * X⁻¹ = j₁₁ * X⁻¹ - ϖ • S := by
    rw [sub_mul, smul_mul_assoc, mul_assoc, h1, mul_one]
  have e3 : j₁₁ * X⁻¹ * (X * S') = j₁₁ * S' := by rw [mul_assoc, ← mul_assoc X⁻¹, h2, one_mul]
  have e2 : (j₁₁ * X⁻¹ - ϖ • S) * (j₃₃ + ϖ • (X * S')) - j₁₁ * X⁻¹ * j₃₃
      = ϖ • (j₁₁ * S' - S * j₃₃ - S * (ϖ • X) * S') := by
    simp only [sub_mul, mul_add, mul_smul_comm, smul_mul_assoc, e3, smul_sub, mul_assoc]; abel
  rw [e1, e2, smul_smul, inv_mul_cancel₀ hϖ, one_smul, sub_mul]; abel

theorem centreForcing : CentreForcing := by
  intro o _ _ _ k0 _ _ _ ϖ hϖ r ξ₁ ξ₂ j₁₃ X y₁ y₂ y₃ S S' hξ₁ hξ₂ hX hy₁ hy₂ e₁ e₂ e₃
  have hinj : Function.Injective (algebraMap o k0) := IsFractionRing.injective o k0
  have hϖ0 : algebraMap o k0 ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have hXd : IsUnit X.det := det_of_cm X (hX r le_rfl)
  have X1 : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hXd
  have X2 : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hXd
  rw [map_smul'] at e₁ e₂ e₃
  simp only [← RingHom.mapMatrix_apply] at e₁ e₂ e₃
  generalize hΦ : (algebraMap o k0).mapMatrix (m := Fin r) = Φ at e₁ e₂ e₃
  have Φsmul : ∀ (c : o) (x : Matrix (Fin r) (Fin r) o), Φ (c • x) = algebraMap o k0 c • Φ x := by
    intro c x; rw [← hΦ]; exact map_smul' _ c x
  have Φinj : Function.Injective Φ := by
    rw [← hΦ]; exact Matrix.map_injective hinj
  have X1φ : Φ X * Φ X⁻¹ = 1 := by rw [← map_mul, X1, map_one]
  have X2φ : Φ X⁻¹ * Φ X = 1 := by rw [← map_mul, X2, map_one]
  have s1 : algebraMap o k0 ϖ • S = Φ (ξ₁ - y₁) * Φ X⁻¹ := by
    have : Φ (ξ₁ - y₁) = algebraMap o k0 ϖ • (S * Φ X) := by
      rw [map_sub, e₁, mul_smul_comm]; abel
    rw [this, smul_mul_assoc, mul_assoc, X1φ, mul_one]
  have s2 : algebraMap o k0 ϖ • S' = Φ X⁻¹ * Φ (y₂ - ξ₂) := by
    have : Φ (y₂ - ξ₂) = algebraMap o k0 ϖ • (Φ X * S') := by
      rw [map_sub, e₂, smul_mul_assoc]; abel
    rw [this, mul_smul_comm, ← mul_assoc, X2φ, one_mul]
  have rel : ϖ • (y₃ - j₁₃) = y₁ * X⁻¹ * y₂ - ξ₁ * X⁻¹ * ξ₂ := by
    apply Φinj
    calc Φ (ϖ • (y₃ - j₁₃)) = algebraMap o k0 ϖ • (-(S * Φ ξ₂) + Φ y₁ * S') := by
          rw [Φsmul, map_sub, e₃, ← e₁]; congr 1; abel
      _ = -((algebraMap o k0 ϖ • S) * Φ ξ₂) + Φ y₁ * (algebraMap o k0 ϖ • S') := by
          rw [smul_add, smul_neg, smul_mul_assoc, mul_smul_comm]
      _ = Φ (y₁ * X⁻¹ * y₂ - ξ₁ * X⁻¹ * ξ₂) := by
          rw [s1, s2]; simp only [map_sub, map_mul]; noncomm_ring

  have hres : ∀ x : Matrix (Fin r) (Fin r) o, (ϖ • x).map (IsLocalRing.residue o) = 0 := by
    intro x; rw [map_smul', res_pi hϖ, zero_smul]
  have rel' : y₁.map (IsLocalRing.residue o) * X⁻¹.map (IsLocalRing.residue o) *
        y₂.map (IsLocalRing.residue o) =
      ξ₁.map (IsLocalRing.residue o) * X⁻¹.map (IsLocalRing.residue o) *
        ξ₂.map (IsLocalRing.residue o) := by
    have := congrArg (fun m => m.map (IsLocalRing.residue o)) rel
    simp only [hres] at this
    simp only [← RingHom.mapMatrix_apply, map_sub, map_mul] at this ⊢
    exact (sub_eq_zero.1 this.symm)
  have xx : X.map (IsLocalRing.residue o) * X⁻¹.map (IsLocalRing.residue o) = 1 := by
    rw [← Matrix.map_mul, X1]; simp
  have xix : X⁻¹.map (IsLocalRing.residue o) * X.map (IsLocalRing.residue o) = 1 := by
    rw [← Matrix.map_mul, X2]; simp
  have hXr : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm (X.map (IsLocalRing.residue o)) l hl) := by
    intro l hl; rw [cm_map]; exact (hX l hl).map _
  generalize X.map (IsLocalRing.residue o) = x at xx xix hXr
  generalize X⁻¹.map (IsLocalRing.residue o) = xi at xx xix rel'
  have key2 : ξ₁.map (IsLocalRing.residue o) = y₁.map (IsLocalRing.residue o) ∧
      ξ₂.map (IsLocalRing.residue o) = y₂.map (IsLocalRing.residue o) := by
    generalize ξ₁.map (IsLocalRing.residue o) = a at hξ₁ rel' ⊢
    generalize y₁.map (IsLocalRing.residue o) = b at hy₁ rel' ⊢
    generalize ξ₂.map (IsLocalRing.residue o) = c at hξ₂ rel' ⊢
    generalize y₂.map (IsLocalRing.residue o) = d at hy₂ rel' ⊢
    have ua : IsUnit a.det := by rw [isUpUni_det _ hξ₁]; exact isUnit_one
    have ud : IsUnit d.det := by rw [isUpUni_det _ hy₂]; exact isUnit_one
    have aa : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a ua
    have aa' : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a ua
    have dd : d * d⁻¹ = 1 := Matrix.mul_nonsing_inv d ud
    have dd' : d⁻¹ * d = 1 := Matrix.nonsing_inv_mul d ud
    have h1 : a⁻¹ * b * xi = xi * c * d⁻¹ := by
      calc a⁻¹ * b * xi = a⁻¹ * (b * xi * d) * d⁻¹ := by simp only [mul_assoc, dd, mul_one]
        _ = a⁻¹ * (a * xi * c) * d⁻¹ := by rw [rel']
        _ = xi * c * d⁻¹ := by simp only [← mul_assoc, aa, one_mul]
    have h2 : c * d⁻¹ * x = x * (a⁻¹ * b) := by
      calc c * d⁻¹ * x = x * (xi * c * d⁻¹) * x := by simp only [← mul_assoc, xx, one_mul]
        _ = x * (a⁻¹ * b * xi) * x := by rw [h1]
        _ = x * (a⁻¹ * b) := by simp only [mul_assoc, xix, mul_one]
    obtain ⟨q1, p1⟩ := uniqCm x (c * d⁻¹) (a⁻¹ * b) (isUpUni_mul _ hξ₂ (isUpUni_inv _ hy₂))
      (isUpUni_mul _ (isUpUni_inv _ hξ₁) hy₁) h2 hXr
    constructor
    · calc a = a * (a⁻¹ * b) := by rw [p1, mul_one]
        _ = b := by rw [← mul_assoc, aa', one_mul]
    · calc c = c * d⁻¹ * d := by rw [mul_assoc, dd', mul_one]
        _ = d := by rw [q1, one_mul]
  obtain ⟨k1, k2⟩ := key2
  obtain ⟨a', ha'⟩ := div_pi hϖ (ξ₁ - y₁) (by
    simp only [← RingHom.mapMatrix_apply, map_sub] at k1 ⊢; rw [k1, sub_self])
  obtain ⟨b', hb'⟩ := div_pi hϖ (y₂ - ξ₂) (by
    simp only [← RingHom.mapMatrix_apply, map_sub] at k2 ⊢; rw [k2, sub_self])
  constructor
  · refine ⟨a' * X⁻¹, ?_⟩
    rw [ha', Φsmul, smul_mul_assoc] at s1
    have := smul_right_injective _ hϖ0 s1
    rw [this, ← map_mul, ← hΦ]; rfl
  · refine ⟨X⁻¹ * b', ?_⟩
    rw [hb', Φsmul, mul_smul_comm] at s2
    have := smul_right_injective _ hϖ0 s2
    rw [this, ← map_mul, ← hΦ]; rfl

section Blocks

variable {A : Type} {r k : ℕ}

theorem ext9 {x y : Matrix (Idx r k) (Idx r k) A} (h11 : b11 x = b11 y) (h12 : b12 x = b12 y)
    (h13 : b13 x = b13 y) (h21 : b21 x = b21 y) (h22 : b22 x = b22 y) (h23 : b23 x = b23 y)
    (h31 : b31 x = b31 y) (h32 : b32 x = b32 y) (h33 : b33 x = b33 y) : x = y := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j
  · exact congrFun (congrFun h11 i) j
  · exact congrFun (congrFun h12 i) j
  · exact congrFun (congrFun h13 i) j
  · exact congrFun (congrFun h21 i) j
  · exact congrFun (congrFun h22 i) j
  · exact congrFun (congrFun h23 i) j
  · exact congrFun (congrFun h31 i) j
  · exact congrFun (congrFun h32 i) j
  · exact congrFun (congrFun h33 i) j

variable [CommRing A]

theorem block11_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b11 (x * y) = b11 x * b11 y + b12 x * b21 y + b13 x * b31 y := by
  ext a b
  simp [b11, b12, b13, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem one_block11 : b11 (1 : Matrix (Idx r k) (Idx r k) A) = 1 := by
  ext a b
  simp [b11, Matrix.one_apply]

theorem block11_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b11 (x.map f) = (b11 x).map f := rfl

theorem block12_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b12 (x * y) = b11 x * b12 y + b12 x * b22 y + b13 x * b32 y := by
  ext a b
  simp [b11, b12, b13, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block12_one : b12 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b12, Matrix.one_apply]

theorem block12_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b12 (x.map f) = (b12 x).map f := rfl

theorem block13_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b13 (x * y) = b11 x * b13 y + b12 x * b23 y + b13 x * b33 y := by
  ext a b
  simp [b11, b12, b13, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block13_one : b13 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b13, Matrix.one_apply]

theorem block13_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b13 (x.map f) = (b13 x).map f := rfl

theorem block21_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b21 (x * y) = b21 x * b11 y + b22 x * b21 y + b23 x * b31 y := by
  ext a b
  simp [b21, b22, b23, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem one_block21 : b21 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b21, Matrix.one_apply]

theorem block21_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b21 (x.map f) = (b21 x).map f := rfl

theorem block22_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b22 (x * y) = b21 x * b12 y + b22 x * b22 y + b23 x * b32 y := by
  ext a b
  simp [b21, b22, b23, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block22_one : b22 (1 : Matrix (Idx r k) (Idx r k) A) = 1 := by
  ext a b
  simp [b22, Matrix.one_apply]

theorem block22_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b22 (x.map f) = (b22 x).map f := rfl

theorem block23_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b23 (x * y) = b21 x * b13 y + b22 x * b23 y + b23 x * b33 y := by
  ext a b
  simp [b21, b22, b23, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block23_one : b23 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b23, Matrix.one_apply]

theorem block23_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b23 (x.map f) = (b23 x).map f := rfl

theorem block31_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x * y) = b31 x * b11 y + b32 x * b21 y + b33 x * b31 y := by
  ext a b
  simp [b31, b32, b33, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem one_block31 : b31 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b31, Matrix.one_apply]

theorem block31_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b31 (x.map f) = (b31 x).map f := rfl

theorem block32_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b32 (x * y) = b31 x * b12 y + b32 x * b22 y + b33 x * b32 y := by
  ext a b
  simp [b31, b32, b33, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block32_one : b32 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b32, Matrix.one_apply]

theorem block32_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b32 (x.map f) = (b32 x).map f := rfl

theorem block33_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b33 (x * y) = b31 x * b13 y + b32 x * b23 y + b33 x * b33 y := by
  ext a b
  simp [b31, b32, b33, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block33_one : b33 (1 : Matrix (Idx r k) (Idx r k) A) = 1 := by
  ext a b
  simp [b33, Matrix.one_apply]

theorem block33_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b33 (x.map f) = (b33 x).map f := rfl

theorem lcancel {n m : Type} [Fintype n] [DecidableEq n] {f : Matrix n n A} (hf : IsUnit f.det)
    {Y Z : Matrix n m A} (h : f * Y = f * Z) : Y = Z := by
  rw [← Matrix.nonsing_inv_mul_cancel_left f Y hf, h, Matrix.nonsing_inv_mul_cancel_left f Z hf]

theorem rcancel {n m : Type} [Fintype n] [DecidableEq n] {f : Matrix n n A} (hf : IsUnit f.det)
    {Y Z : Matrix m n A} (h : Y * f = Z * f) : Y = Z := by
  rw [← Matrix.mul_nonsing_inv_cancel_right f Y hf, h, Matrix.mul_nonsing_inv_cancel_right f Z hf]

theorem uni_unit {n : ℕ} {u : Matrix (Fin n) (Fin n) A} (hu : IsUpUni u) : IsUnit u.det := by
  rw [isUpUni_det A hu]; exact isUnit_one

def BT (x : Matrix (Idx r k) (Idx r k) A) : Prop :=
  IsUpUni (b11 x) ∧ IsUpUni (b33 x) ∧ b21 x = 0 ∧ b31 x = 0 ∧ b32 x = 0 ∧ IsUnit (b22 x).det

theorem bt_det {x : Matrix (Idx r k) (Idx r k) A} (hx : BT x) : IsUnit x.det := by
  obtain ⟨h11, h33, h21, h31, h32, h22⟩ := hx
  have e : x = Matrix.fromBlocks (b11 x) x.toBlocks₁₂ 0 (Matrix.fromBlocks (b22 x) (b23 x) 0 (b33 x)) := by
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j
    · rfl
    · rfl
    · rfl
    · exact congrFun (congrFun h21 i) j
    · rfl
    · rfl
    · exact congrFun (congrFun h31 i) j
    · exact congrFun (congrFun h32 i) j
    · rfl
  rw [e, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁,
    isUpUni_det A h11, isUpUni_det A h33]
  simpa using h22

theorem bt_mul {x y : Matrix (Idx r k) (Idx r k) A} (hx : BT x) (hy : BT y) : BT (x * y) := by
  obtain ⟨h11, h33, h21, h31, h32, h22⟩ := hx
  obtain ⟨g11, g33, g21, g31, g32, g22⟩ := hy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [block11_mul, g21, g31]; simpa using isUpUni_mul A h11 g11
  · rw [block33_mul, h31, h32]; simpa using isUpUni_mul A h33 g33
  · rw [block21_mul, h21, g21, g31]; simp
  · rw [block31_mul, h31, h32, g31]; simp
  · rw [block32_mul, h31, h32, g32]; simp
  · rw [block22_mul, h21, g32]; simpa using h22.mul g22

theorem bt_rinv {x y : Matrix (Idx r k) (Idx r k) A} (hx : BT x) (e : x * y = 1) : BT y := by
  obtain ⟨h11, h33, h21, h31, h32, h22⟩ := hx
  have y31 : b31 y = 0 := by
    have := block31_mul x y
    rw [e, one_block31, h31, h32] at this
    exact lcancel (uni_unit h33) (by simpa using this.symm)
  have y32 : b32 y = 0 := by
    have := block32_mul x y
    rw [e, block32_one, h31, h32] at this
    exact lcancel (uni_unit h33) (by simpa using this.symm)
  have y33 : b33 y = (b33 x)⁻¹ := by
    have := block33_mul x y
    rw [e, block33_one, h31, h32] at this
    exact (Matrix.inv_eq_right_inv (by simpa using this.symm)).symm
  have y21 : b21 y = 0 := by
    have := block21_mul x y
    rw [e, one_block21, h21, y31] at this
    exact lcancel h22 (by simpa using this.symm)
  have y22 : b22 y = (b22 x)⁻¹ := by
    have := block22_mul x y
    rw [e, block22_one, h21, y32] at this
    exact (Matrix.inv_eq_right_inv (by simpa using this.symm)).symm
  have y11 : b11 y = (b11 x)⁻¹ := by
    have := block11_mul x y
    rw [e, one_block11, y21, y31] at this
    exact (Matrix.inv_eq_right_inv (by simpa using this.symm)).symm
  exact ⟨y11 ▸ isUpUni_inv A h11, y33 ▸ isUpUni_inv A h33, y21, y31, y32,
    y22 ▸ Matrix.isUnit_nonsing_inv_det _ h22⟩

theorem bt_of_isN {x : Matrix (Idx r k) (Idx r k) A} (hx : IsN x) : BT x := by
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hx
  exact ⟨h11, h33, h21, h31, h32, by rw [h22]; simp⟩

theorem bt_of_isNU {x : Matrix (Idx r k) (Idx r k) A} (hx : IsNU x) : BT x := by
  obtain ⟨n, _, hn, ⟨u, hu, rfl⟩, rfl⟩ := hx
  refine bt_mul (bt_of_isN hn) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : b11 (hEmb r u) = 1 := by ext a b; simp [b11, hEmb]
    rw [this]; exact isUpUni_one A
  · have : b33 (hEmb r u) = 1 := by ext a b; simp [b33, hEmb]
    rw [this]; exact isUpUni_one A
  · ext a b; simp [b21, hEmb]
  · ext a b; simp [b31, hEmb]
  · ext a b; simp [b32, hEmb]
  · have : b22 (hEmb r u) = midEmb u := by ext a b; simp [b22, hEmb]
    rw [this]; simpa [midEmb] using uni_unit hu

theorem isN_map {B : Type} [CommRing B] (f : A →+* B) {x : Matrix (Idx r k) (Idx r k) A} (hx : IsN x) :
    IsN (x.map f) := by
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [block11_map]; exact upUni_map f h11
  · rw [block33_map]; exact upUni_map f h33
  · rw [block22_map, h22]; simp
  · rw [block21_map, h21]; ext; simp
  · rw [block31_map, h31]; ext; simp
  · rw [block32_map, h32]; ext; simp

def mk (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A) :
    Matrix (Idx r k) (Idx r k) A :=
  Matrix.fromBlocks a (Matrix.fromCols b c) 0 (Matrix.fromBlocks m e 0 f)

section mk
variable (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A)
theorem block11_of_blocks : b11 (mk a b c m e f) = a := by ext i j; simp [b11, mk]
theorem block12_of_blocks : b12 (mk a b c m e f) = b := by ext i j; simp [b12, mk]
theorem block13_of_blocks : b13 (mk a b c m e f) = c := by ext i j; simp [b13, mk]
theorem block21_of_blocks : b21 (mk a b c m e f) = 0 := by ext i j; simp [b21, mk]
theorem block22_of_blocks : b22 (mk a b c m e f) = m := by ext i j; simp [b22, mk]
theorem block23_of_blocks : b23 (mk a b c m e f) = e := by ext i j; simp [b23, mk]
theorem block31_of_blocks : b31 (mk a b c m e f) = 0 := by ext i j; simp [b31, mk]
theorem block32_of_blocks : b32 (mk a b c m e f) = 0 := by ext i j; simp [b32, mk]
theorem block33_of_blocks : b33 (mk a b c m e f) = f := by ext i j; simp [b33, mk]
end mk

end Blocks

section Stab

variable {F : Type} [Field F] {r k : ℕ}

theorem halfStab {g n n' : Matrix (Idx r k) (Idx r k) F}
    (hc : ∀ (l : ℕ) (hl : l ≤ r), cm (b31 g) l hl ≠ 0) (hn : IsN n) (hn' : IsN n')
    (e : g * n' = n * g) : b33 n = 1 ∧ b11 n' = 1 ∧ b23 n = 0 ∧ b12 n' = 0 := by
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hn
  obtain ⟨g11, g33, g22, g21, g31, g32⟩ := hn'
  have hu : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm (b31 g) l hl) := fun l hl => (hc l hl).isUnit
  have hd : IsUnit (b31 g).det := det_of_cm _ (hu r le_rfl)
  have e31 := congrArg b31 e
  rw [block31_mul, block31_mul, g21, g31, h31, h32] at e31
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e31
  obtain ⟨u2, u1⟩ := uniqCm (b31 g) (b33 n) (b11 n') h33 g11 e31.symm hu
  refine ⟨u2, u1, ?_, ?_⟩
  · have e21 := congrArg b21 e
    rw [block21_mul, block21_mul, g21, g31, h21, h22, u1] at e21
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul] at e21
    refine rcancel hd ?_
    rw [Matrix.zero_mul]
    exact (left_eq_add.1 e21)
  · have e32 := congrArg b32 e
    rw [block32_mul, block32_mul, g22, g32, h31, h32, u2] at e32
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul] at e32
    refine lcancel hd ?_
    rw [Matrix.mul_zero]
    exact (add_eq_right.1 e32)

theorem stabiliserTrivial : StabiliserTrivial := by
  intro F _ r k g n n' hg hc hc' hn hn' e
  have g1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have g2 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hg
  have e' : g⁻¹ * n = n' * g⁻¹ := by
    calc g⁻¹ * n = g⁻¹ * (n * g) * g⁻¹ := by simp only [mul_assoc, g1, mul_one]
      _ = g⁻¹ * (g * n') * g⁻¹ := by rw [e]
      _ = n' * g⁻¹ := by simp only [← mul_assoc, g2, one_mul]
  obtain ⟨a33, a11', a23, a12'⟩ := halfStab hc hn hn' e
  obtain ⟨a33', a11, a23', a12⟩ := halfStab hc' hn' hn e'
  have hd : IsUnit (b31 g).det := det_of_cm _ (hc r le_rfl).isUnit
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hn
  obtain ⟨g11, g33, g22, g21, g31, g32⟩ := hn'
  have a13 : b13 n = 0 := by
    have e11 := congrArg b11 e
    rw [block11_mul, block11_mul, g21, g31, a11', a11, a12] at e11
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul] at e11
    refine rcancel hd ?_
    rw [Matrix.zero_mul]
    exact (left_eq_add.1 e11)
  have a13' : b13 n' = 0 := by
    have e33 := congrArg b33 e
    rw [block33_mul, block33_mul, h31, h32, a33', a33, a23'] at e33
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul] at e33
    refine lcancel hd ?_
    rw [Matrix.mul_zero]
    exact (add_eq_right.1 e33)
  constructor
  · apply ext9 <;> simp only [one_block11, block12_one, block13_one, one_block21, block22_one, block23_one, one_block31, block32_one,
      block33_one] <;> assumption
  · apply ext9 <;> simp only [one_block11, block12_one, block13_one, one_block21, block22_one, block23_one, one_block31, block32_one,
      block33_one] <;> assumption

end Stab

section Forcing

variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0] {r k : ℕ}

def cen {A : Type} [CommRing A] (S : Matrix (Fin r) (Fin r) A) : Matrix (Idx r k) (Idx r k) A :=
  mk 1 0 S 1 0 1

theorem int_cen {S : Matrix (Fin r) (Fin r) k0} (h : Integral o S) :
    Integral o (cen S : Matrix (Idx r k) (Idx r k) k0) := by
  obtain ⟨s, rfl⟩ := h
  refine ⟨cen s, ?_⟩
  apply ext9 <;>
    simp [cen, block11_map, block12_map, block13_map, block21_map, block22_map, block23_map, block31_map, block32_map, block33_map,
      block11_of_blocks, block12_of_blocks, block13_of_blocks, block21_of_blocks, block22_of_blocks, block23_of_blocks, block31_of_blocks, block32_of_blocks, block33_of_blocks]

theorem int_rdiv {m : Type} {Y : Matrix m (Fin r) k0} {X : Matrix (Fin r) (Fin r) o} (hX : IsUnit X.det)
    (h : Integral o (Y * X.map (algebraMap o k0))) : Integral o Y := by
  have e : Y = Y * X.map (algebraMap o k0) * X⁻¹.map (algebraMap o k0) := by
    rw [Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv X hX]; simp
  rw [e]; exact int_mul h (int_map _)

theorem int_ldiv {m : Type} {Y : Matrix (Fin r) m k0} {X : Matrix (Fin r) (Fin r) o} (hX : IsUnit X.det)
    (h : Integral o (X.map (algebraMap o k0) * Y)) : Integral o Y := by
  have e : Y = X⁻¹.map (algebraMap o k0) * (X.map (algebraMap o k0) * Y) := by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul X hX]; simp
  rw [e]; exact int_mul (int_map _) h

variable [IsDomain o] [IsDiscreteValuationRing o] [IsFractionRing o k0]

theorem decomp {n : Matrix (Idx r k) (Idx r k) k0} (hn : IsN n) (i11 : Integral o (b11 n))
    (i12 : Integral o (b12 n)) (i23 : Integral o (b23 n)) (i33 : Integral o (b33 n)) :
    ∃ (m : Matrix (Idx r k) (Idx r k) o) (S : Matrix (Fin r) (Fin r) k0),
      IsN m ∧ n = cen S * m.map (algebraMap o k0) := by
  have hinj : Function.Injective (algebraMap o k0) := IsFractionRing.injective o k0
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hn
  obtain ⟨u1, hu1⟩ := i11
  obtain ⟨a, ha⟩ := i12
  obtain ⟨a', ha'⟩ := i23
  obtain ⟨u2, hu2⟩ := i33
  refine ⟨mk u1 a 0 1 a' u2, b13 n * (b33 n)⁻¹, ⟨?_, ?_, block22_of_blocks .., block21_of_blocks .., block31_of_blocks .., block32_of_blocks ..⟩, ?_⟩
  · rw [block11_of_blocks]; exact upUni_of_map _ hinj (hu1 ▸ h11)
  · rw [block33_of_blocks]; exact upUni_of_map _ hinj (hu2 ▸ h33)
  · have hz : (b33 n)⁻¹ * b33 n = 1 := Matrix.nonsing_inv_mul _ (uni_unit h33)
    apply ext9 <;>
      simp only [cen, block11_mul, block12_mul, block13_mul, block21_mul, block22_mul, block23_mul, block31_mul, block32_mul, block33_mul,
        block11_map, block12_map, block13_map, block21_map, block22_map, block23_map, block31_map, block32_map, block33_map,
        block11_of_blocks, block12_of_blocks, block13_of_blocks, block21_of_blocks, block22_of_blocks, block23_of_blocks, block31_of_blocks, block32_of_blocks, block33_of_blocks, hu1, ha, ha', hu2,
        h22, h21, h31, h32] <;>
      simp [Matrix.mul_assoc, hz]

theorem halfForce {ϖ : o} (hϖ : Irreducible ϖ) {j j' : Matrix (Idx r k) (Idx r k) o}
    {n n' : Matrix (Idx r k) (Idx r k) k0} {X : Matrix (Fin r) (Fin r) o}
    (hj : BT (j.map (IsLocalRing.residue o))) (hX : b31 j = ϖ • X)
    (hc : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X l hl))
    (hj' : BT (j'.map (IsLocalRing.residue o))) (hn : IsN n) (hn' : IsN n')
    (e : n * j'.map (algebraMap o k0) = j.map (algebraMap o k0) * n') :
    Integral o (b33 n) ∧ Integral o (b11 n') ∧ Integral o (b23 n) ∧ Integral o (b12 n') ∧
      ∃ X' : Matrix (Fin r) (Fin r) o, b31 j' = ϖ • X' ∧ ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X' l hl) := by
  have hinj : Function.Injective (algebraMap o k0) := IsFractionRing.injective o k0
  have hϖ0 : algebraMap o k0 ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hn
  obtain ⟨g11, g33, g22, g21, g31, g32⟩ := hn'
  obtain ⟨X', hX'⟩ := div_pi hϖ (b31 j') hj'.2.2.2.1
  obtain ⟨P, hP⟩ := div_pi hϖ (b21 j) hj.2.2.1
  obtain ⟨P', hP'⟩ := div_pi hϖ (b21 j') hj'.2.2.1
  obtain ⟨Q, hQ⟩ := div_pi hϖ (b32 j) hj.2.2.2.2.1
  obtain ⟨Q', hQ'⟩ := div_pi hϖ (b32 j') hj'.2.2.2.2.1
  have e31 := congrArg b31 e
  rw [block31_mul, block31_mul, h31, h32, g21, g31, block31_map, block31_map, hX, hX', map_smul', map_smul'] at e31
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_smul,
    Matrix.smul_mul] at e31
  have E31 := smul_right_injective _ hϖ0 e31
  obtain ⟨c33, c11, cc⟩ := keyCm (algebraMap o k0) hinj (algebraMap o k0).toAddMonoidHom.range
    range_stable X X' (b33 n) (b11 n') h33 g11 E31 (fun a b => ⟨_, rfl⟩) hc
  have i33 : Integral o (b33 n) := int_of_sub_one c33
  have i11 : Integral o (b11 n') := int_of_sub_one c11
  have hc' : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X' l hl) := fun l hl => by rw [cc]; exact hc l hl
  refine ⟨i33, i11, ?_, ?_, X', hX', hc'⟩
  · have e21 := congrArg b21 e
    rw [block21_mul, block21_mul, h21, h22, g21, g31, block21_map, block21_map, block31_map, hX', hP, hP', map_smul',
      map_smul', map_smul'] at e21
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.one_mul, ← smul_add] at e21
    have E21 := smul_right_injective _ hϖ0 e21
    refine int_rdiv (det_of_cm X' (hc' r le_rfl)) ?_
    rw [eq_sub_iff_add_eq'.2 E21]
    exact int_sub (int_mul (int_map _) i11) (int_map _)
  · have e32 := congrArg b32 e
    rw [block32_mul, block32_mul, h31, h32, g22, g32, block32_map, block32_map, block31_map, hX, hQ, hQ', map_smul',
      map_smul', map_smul'] at e32
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, ← smul_add] at e32
    have E32 := smul_right_injective _ hϖ0 e32
    refine int_ldiv (det_of_cm X (hc r le_rfl)) ?_
    rw [eq_sub_iff_add_eq.2 E32.symm]
    exact int_sub (int_mul i33 (int_map _)) (int_map _)

omit [IsFractionRing o k0] in
theorem invOm {ϖ : o} (hϖ : Irreducible ϖ) {j : Matrix (Idx r k) (Idx r k) o}
    {X : Matrix (Fin r) (Fin r) o} (hd : IsUnit j.det)
    (hj : BT (j.map (IsLocalRing.residue o))) (hX : b31 j = ϖ • X)
    (hc : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X l hl)) :
    BT (j⁻¹.map (IsLocalRing.residue o)) ∧
      ∃ Y : Matrix (Fin r) (Fin r) o, b31 j⁻¹ = ϖ • Y ∧ ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm Y l hl) := by
  have j1 : j * j⁻¹ = 1 := Matrix.mul_nonsing_inv j hd
  have hi : BT (j⁻¹.map (IsLocalRing.residue o)) := bt_rinv hj (by rw [← Matrix.map_mul, j1]; simp)
  refine ⟨hi, ?_⟩
  obtain ⟨Y, hY⟩ := div_pi hϖ (b31 j⁻¹) hi.2.2.2.1
  obtain ⟨Q, hQ⟩ := div_pi hϖ (b21 j⁻¹) hi.2.2.1
  obtain ⟨P, hP⟩ := div_pi hϖ (b32 j) hj.2.2.2.2.1
  refine ⟨Y, hY, ?_⟩
  have e31 := congrArg b31 j1
  rw [block31_mul, one_block31, hX, hP, hQ, hY] at e31
  have e31' : ϖ • (X * b11 j⁻¹ + ϖ • (P * Q) + b33 j * Y) = ϖ • (0 : Matrix (Fin r) (Fin r) o) := by
    rw [smul_zero, ← e31]
    simp only [smul_add, Matrix.mul_smul, Matrix.smul_mul]
  have E := smul_right_injective _ hϖ.ne_zero e31'
  have E' := congrArg (fun m => m.map (IsLocalRing.residue o)) E
  simp only [← RingHom.mapMatrix_apply, map_add, map_mul, map_zero] at E'
  simp only [RingHom.mapMatrix_apply, map_smul', res_pi hϖ, zero_smul, add_zero] at E'
  have E2 : (b33 j).map (IsLocalRing.residue o) * Y.map (IsLocalRing.residue o) =
      (-X.map (IsLocalRing.residue o)) * (b11 j⁻¹).map (IsLocalRing.residue o) := by
    rw [neg_mul]; exact eq_neg_of_add_eq_zero_right E'
  have hu : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm (-X.map (IsLocalRing.residue o)) l hl) := by
    intro l hl
    rw [cm_neg, cm_map]
    exact ((isUnit_one.neg).pow l).mul ((hc l hl).map _)
  have := invCm _ _ _ _ hj.2.1 hi.1 E2 hu
  intro l hl
  refine (isUnit_map_iff (IsLocalRing.residue o) _).1 ?_
  rw [← cm_map, this]
  exact hu l hl

end Forcing

theorem forcing : Forcing := by
  intro o _ _ _ k0 _ _ _ ϖ hϖ r k j j' n n' hj hj' hn hn' e
  obtain ⟨⟨hjd, hjNU⟩, X, hX, hc⟩ := hj
  have bj := bt_of_isNU hjNU
  have bj' := bt_of_isNU hj'.2
  have j1 : j⁻¹ * j = 1 := Matrix.nonsing_inv_mul j hjd
  have j1' : j' * j'⁻¹ = 1 := Matrix.mul_nonsing_inv j' hj'.1
  obtain ⟨i33, i11', i23, i12', X', hX', hc'⟩ := halfForce hϖ bj hX hc bj' hn hn' e
  obtain ⟨bi, Y, hY, hcY⟩ := invOm hϖ hjd bj hX hc
  have bi' : BT (j'⁻¹.map (IsLocalRing.residue o)) :=
    bt_rinv bj' (by rw [← Matrix.map_mul, j1']; simp)
  have J1 : j⁻¹.map (algebraMap o k0) * j.map (algebraMap o k0) = 1 := by
    rw [← Matrix.map_mul, j1]; simp
  have J1' : j'.map (algebraMap o k0) * j'⁻¹.map (algebraMap o k0) = 1 := by
    rw [← Matrix.map_mul, j1']; simp
  have e' : n' * j'⁻¹.map (algebraMap o k0) = j⁻¹.map (algebraMap o k0) * n := by
    calc n' * j'⁻¹.map (algebraMap o k0)
        = j⁻¹.map (algebraMap o k0) * (j.map (algebraMap o k0) * n') * j'⁻¹.map (algebraMap o k0) := by
          simp only [← mul_assoc, J1, one_mul]
      _ = j⁻¹.map (algebraMap o k0) * (n * j'.map (algebraMap o k0)) * j'⁻¹.map (algebraMap o k0) := by
          rw [e]
      _ = j⁻¹.map (algebraMap o k0) * n := by simp only [mul_assoc, J1', mul_one]
  obtain ⟨i33', i11, i23', i12, -⟩ := halfForce hϖ bi hY hcY bi' hn' hn e'
  obtain ⟨m, S, hm, hnS⟩ := decomp hn i11 i12 i23 i33
  obtain ⟨m', S', hm', hnS'⟩ := decomp hn' i11' i12' i23' i33'
  have m1 : m' * m'⁻¹ = 1 := Matrix.mul_nonsing_inv m' (bt_det (bt_of_isN hm'))
  have M1 : m'.map (algebraMap o k0) * m'⁻¹.map (algebraMap o k0) = 1 := by
    rw [← Matrix.map_mul, m1]; simp
  have bj'' : BT ((m * j' * m'⁻¹).map (IsLocalRing.residue o)) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    exact bt_mul (bt_mul (bt_of_isN (isN_map _ hm)) bj')
      (bt_rinv (bt_of_isN (isN_map _ hm')) (by rw [← Matrix.map_mul, m1]; simp))
  have e'' : cen S * (m * j' * m'⁻¹).map (algebraMap o k0) = j.map (algebraMap o k0) * cen S' := by
    rw [Matrix.map_mul, Matrix.map_mul]
    calc cen S * (m.map (algebraMap o k0) * j'.map (algebraMap o k0) * m'⁻¹.map (algebraMap o k0))
        = (cen S * m.map (algebraMap o k0)) * j'.map (algebraMap o k0) * m'⁻¹.map (algebraMap o k0) := by
          simp only [mul_assoc]
      _ = j.map (algebraMap o k0) * (cen S' * m'.map (algebraMap o k0)) * m'⁻¹.map (algebraMap o k0) := by
          rw [← hnS, e, ← hnS']
      _ = j.map (algebraMap o k0) * cen S' := by simp only [mul_assoc, M1, mul_one]
  generalize m * j' * m'⁻¹ = j'' at bj'' e''
  have f31 := congrArg b31 e''
  have f11 := congrArg b11 e''
  have f33 := congrArg b33 e''
  have f13 := congrArg b13 e''
  simp only [cen, block11_mul, block13_mul, block31_mul, block33_mul, block11_of_blocks, block12_of_blocks, block13_of_blocks, block21_of_blocks, block22_of_blocks, block23_of_blocks,
    block31_of_blocks, block32_of_blocks, block33_of_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Matrix.one_mul, block11_map, block13_map, block31_map, block33_map] at f31 f11 f33 f13
  rw [f31] at f11
  rw [hX] at f11 f33
  have E1 : (b11 j'').map (algebraMap o k0) =
      (b11 j).map (algebraMap o k0) - S * (ϖ • X).map (algebraMap o k0) := eq_sub_of_add_eq f11
  have E2 : (b33 j'').map (algebraMap o k0) =
      (b33 j).map (algebraMap o k0) + (ϖ • X).map (algebraMap o k0) * S' := by rw [f33, add_comm]
  have E3 : (b13 j'').map (algebraMap o k0) = (b13 j).map (algebraMap o k0) -
      S * (b33 j).map (algebraMap o k0) +
        ((b11 j).map (algebraMap o k0) - S * (ϖ • X).map (algebraMap o k0)) * S' := by
    rw [eq_sub_of_add_eq f13, E2]; noncomm_ring
  obtain ⟨iS, iS'⟩ := centreForcing o k0 ϖ hϖ r (b11 j) (b33 j) (b13 j) X (b11 j'') (b33 j'') (b13 j'')
    S S' bj.1 bj.2.1 hc bj''.1 bj''.2.1 E1 E2 E3
  refine ⟨?_, ?_, hj', X', hX', hc'⟩
  · rw [hnS]; exact int_mul (int_cen iS) (int_map m)
  · rw [hnS']; exact int_mul (int_cen iS') (int_map m')

end Formalism.FourierDecayAlt.P.S3x8

theorem Formalism.FourierDecayAlt.P.block_forcing : Formalism.FourierDecayAlt.S3.Forcing := Formalism.FourierDecayAlt.P.S3x8.forcing

theorem Formalism.FourierDecayAlt.P.centre_block_structure : Formalism.FourierDecayAlt.S3.CentreBlocks := Formalism.FourierDecayAlt.P.S3x8.centreBlocks

theorem Formalism.FourierDecayAlt.P.centreForcing_true : Formalism.FourierDecayAlt.S3.CentreForcing := Formalism.FourierDecayAlt.P.S3x8.centreForcing

theorem Formalism.FourierDecayAlt.P.stabiliserTrivial_true : Formalism.FourierDecayAlt.S3.StabiliserTrivial :=
  Formalism.FourierDecayAlt.P.S3x8.stabiliserTrivial

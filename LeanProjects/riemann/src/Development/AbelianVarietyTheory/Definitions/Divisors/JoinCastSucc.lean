import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice

def join {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) : Fin (D + 1) × Fin N → R :=
  fun p => Fin.lastCases (motive := fun _ => R) (ξ p.2) (fun i => u i p.2) p.1

def spec {F E : Type} [CommRing F] [CommRing E] [Algebra F E] {D N : ℕ} (s : Fin D → Fin N → E)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) : MvPolynomial (Fin 1 × Fin N) E :=
  aeval (join (fun i j => C (s i j)) fun j => X (0, j)) f

def lin {K : Type} [CommRing K] {N : ℕ} (y : Fin N → K) : MvPolynomial (Fin 1 × Fin N) K := ∑ j, X ((0 : Fin 1), j) * C (y j)

def finPart {K ι : Type} [Field K] [NumberField K] (g : MvPolynomial ι K) : ℝ :=
  (∑ᶠ v : FinitePlace K, Real.log (gaussAbs v g)) / (Module.finrank ℚ K : ℝ)

def mean (K : Type) [Field K] [NumberField K] (a : (K →+* ℂ) → ℝ) : ℝ := (∑ τ, a τ) / (Module.finrank ℚ K : ℝ)

def fixVar {K ι : Type} [CommRing K] [DecidableEq ι] (r : ι) (c : K) (g : MvPolynomial ι K) : MvPolynomial ι K :=
  aeval (fun j => if j = r then C c else X j) g

def fixBelow {K κ : Type} [CommRing K] {m : ℕ} (r : ℕ) (c : Fin m → K) (g : MvPolynomial (Fin m ⊕ κ) K) :
    MvPolynomial (Fin m ⊕ κ) K :=
  aeval (Sum.elim (fun i : Fin m => if (i : ℕ) < r then C (c i) else X (Sum.inl i)) fun k => X (Sum.inr k)) g

def fixRight {K κ : Type} [CommRing K] {m : ℕ} (e : κ → K) (g : MvPolynomial (Fin m ⊕ κ) K) : MvPolynomial (Fin m ⊕ κ) K :=
  aeval (Sum.elim (fun i => X (Sum.inl i)) fun k => C (e k)) g

def ShearInv {F : Type} [CommRing F] {D N : ℕ} (f : MvPolynomial (Fin (D + 1) × Fin N) F) : Prop :=
  ∀ (i : Fin D) (t : F), aeval (fun p : Fin (D + 1) × Fin N =>
    if p.1 = i.castSucc then X p + C t * X (Fin.last D, p.2) else (X p : MvPolynomial (Fin (D + 1) × Fin N) F)) f = f

def LastNonzero {F : Type} [CommRing F] {D N : ℕ} (f : MvPolynomial (Fin (D + 1) × Fin N) F) : Prop :=
  ∀ u : Fin N → F, u ≠ 0 → ∃ v : Fin D → Fin N → F, eval (join v u) f ≠ 0

structure IsMaxPt {B N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (δ : ℕ) (h : MvPolynomial (Fin B × Fin N) ℂ)
    (p : Fin B × Fin N → ℂ) : Prop where
  unit : ∀ i, frameNorm A (fun j => p (i, j)) = 1
  ne : eval p h ≠ 0
  le : ∀ u : Fin B × Fin N → ℂ, ‖eval u h‖ ≤ ‖eval p h‖ * ∏ i, frameNorm A (fun j => u (i, j)) ^ δ

structure ShortLat {F : Type} [Field F] [NumberField F] {N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (Λ : ℝ) : Prop where
  pos : 0 < N
  spans : Submodule.span F (Set.range w.col) = ⊤
  int : ∀ u ∈ Submodule.span (𝓞 F) (Set.range w.col), u ∈ Submodule.span ℤ (Set.range w.col)
  det : ∀ σ, (A σ).det ≠ 0
  conj : ConjCompat A
  le : ∀ k σ, frameNorm (A σ) (fun j => σ (w j k)) ≤ Λ
  one_le : 1 ≤ Λ

def vecs {F E : Type} [Field F] [Field E] [Algebra F E] {D N n : ℕ} (w : Matrix (Fin N) (Fin n) F) (x : Fin D → Fin n → 𝓞 E) :
    Fin D → Fin N → E := fun i => (w.map (algebraMap F E)).mulVec fun k => (x i k : E)

def specHeight {F : Type} [Field F] [NumberField F] {D N n : ℕ} (δ : ℕ) (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (f : MvPolynomial (Fin (D + 1) × Fin N) F) (E : Type) [Field E] [NumberField E]
    [Algebra F E] (s : Fin D → Fin N → E) : ℝ :=
  formHeight δ (w.map (algebraMap F E)) (fun τ => A (τ.comp (algebraMap F E))) (spec s f)

def defect {F : Type} [Field F] [NumberField F] {D N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin D → Fin N → E) : ℝ :=
  finPart (linSubst w f) - finPart (linSubst (w.map (algebraMap F E)) (spec s f))

def Core : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (D N n δ : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (Λ h Θ : ℝ) (f : MvPolynomial (Fin (D + 1) × Fin N) F) (Q : MvPolynomial (Fin D × Fin N) F),
    1 ≤ D → 1 ≤ δ → ShortLat w A Λ → IsMultiHomogeneous (fun _ => δ) f → ShearInv f → LastNonzero f →
    ((D : ℝ) + 1) * δ * h = formHeight δ w A f → (n : ℝ) * D * δ * (2 + |h| + Real.log Λ) ≤ Θ →
    Q ≠ 0 → (Q.totalDegree : ℝ) ≤ Θ ^ 3 →
    ∃ (l : ℕ) (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (x : Fin D → Fin n → 𝓞 E),
      Θ ^ 20 < l ∧ (l : ℝ) ≤ 2 * Θ ^ 20 ∧ (∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → l ≤ Ideal.absNorm P) ∧
      aeval (fun p : Fin D × Fin N => vecs w x p.1 p.2) Q ≠ 0 ∧ spec (vecs w x) f ≠ 0 ∧
      (∀ i (τ : E →+* ℂ), frameNorm (A (τ.comp (algebraMap F E))) (fun j => τ (vecs w x i j)) ≤
        8 * D * δ * n * l * Λ * (1 + 1 / (8 * D * δ))) ∧
      ((D : ℝ) + 1) * δ * h + D * δ * Real.log (8 * D * δ * n * l * Λ) -
        δ * (((D : ℝ) + 1) * (harmonic (N - 1) : ℝ) / 2 + Real.log 2 / δ + 1 / 8) ≤ specHeight δ w A f E (vecs w x) ∧
      specHeight δ w A f E (vecs w x) ≤ ((D : ℝ) + 1) * δ * h + δ * ∑ i, mean E fun τ =>
        Real.log (frameNorm (A (τ.comp (algebraMap F E))) fun j => τ (vecs w x i j))

def AvoidPoly {F : Type} [Field F] [NumberField F] (T : Tuple F) (e : ℕ) : Prop :=
  ∃ Q : MvPolynomial (Fin T.D × Fin T.N) F, Q ≠ 0 ∧ Q.totalDegree ≤ e ∧
    ∀ (K : Type) [Field K] [Algebra F K] [IsAlgClosure F K] (s : Fin T.D → Fin T.N → K),
      aeval (fun p : Fin T.D × Fin T.N => s p.1 p.2) Q ≠ 0 →
      ∀ x : T.Pt K, (∀ i, ∑ j, s i j * T.coords x.1 j = 0) → ptOf x.1 ∈ nonzeroLocus T.th

def NoSquare {K : Type} [Field K] {N : ℕ} (g : MvPolynomial (Fin 1 × Fin N) K) : Prop :=
  g ≠ 0 ∧ ∀ y : Fin N → K, y ≠ 0 → ¬ lin y ^ 2 ∣ g

theorem join_last {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) (j : Fin N) : join u ξ (Fin.last D, j) = ξ j := by
  simp [join]

theorem join_castSucc {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) (i : Fin D) (j : Fin N) :
    join u ξ (i.castSucc, j) = u i j := by
  simp [join]

example : ShortLat (1 : Matrix (Fin 1) (Fin 1) ℚ) (fun _ => 1) 1 :=
  ⟨one_pos, (projTuple.spans 0), (projTuple.shortGenerators 0).int, fun _ => by simp, fun σ x => by simp [frameNorm],
    fun k σ => (projTuple.shortGenerators 0).le k σ, le_rfl⟩

namespace Check

def det2 (R : Type) [CommRing R] : MvPolynomial (Fin 2 × Fin 2) R := X (0,0) * X (1,1) - X (0,1) * X (1,0)

theorem shortLat_std (M : ℕ) : ShortLat (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) ℚ) (fun _ => 1) 1 :=
  ⟨Nat.succ_pos _, projTuple.spans M, (projTuple.shortGenerators M).int, fun _ => by simp,
    fun σ x => by simp [frameNorm], fun k σ => (projTuple.shortGenerators M).le k σ, le_rfl⟩

theorem sl2 : ShortLat (1 : Matrix (Fin 2) (Fin 2) ℚ) (fun _ => 1) 1 := shortLat_std 1

theorem shear2 : ShearInv (D := 1) (det2 ℚ) := by
  intro i t
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [det2, show Fin.last 1 = 1 from rfl]
  ring

theorem join_eval {R : Type} [CommRing R] (v : Fin 1 → Fin 2 → R) (u : Fin 2 → R) :
    eval (join v u) (det2 R) = v 0 0 * u 1 - v 0 1 * u 0 := by
  simp only [det2, map_sub, map_mul, eval_X]
  rfl

theorem last2 : LastNonzero (D := 1) (det2 ℚ) := by
  intro u hu
  refine ⟨fun _ => ![u 1, -u 0], ?_⟩
  rw [join_eval]
  intro h
  simp at h
  apply hu
  funext j
  fin_cases j <;> simp <;> nlinarith [mul_self_nonneg (u 0), mul_self_nonneg (u 1)]

theorem max2 : IsMaxPt (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 (det2 ℂ) (fun p => if p.1 = p.2 then 1 else 0) := by
  refine ⟨fun i => ?_, by simp [det2], fun u => ?_⟩
  · fin_cases i <;> simp [frameNorm, Fin.sum_univ_two]
  · simp only [det2, frameNorm, Fin.prod_univ_two, Fin.sum_univ_two, map_sub, map_mul, eval_X, inv_one, Matrix.one_mulVec, pow_one]
    simp
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    have h := norm_sub_le (u (0,0) * u (1,1)) (u (0,1) * u (1,0))
    rw [norm_mul, norm_mul] at h
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith [sq_nonneg (‖u (0,0)‖ * ‖u (1,0)‖ - ‖u (0,1)‖ * ‖u (1,1)‖)]

theorem mh2 : IsMultiHomogeneous (fun _ => 1) (det2 ℚ) := by
  have := (GlobalTheory.ChowHt.Model.isChowForm_line ℚ).homog
  rwa [Matrix.det_fin_two] at this

theorem core_hyp : ∃ h Θ : ℝ, ShortLat (1 : Matrix (Fin 2) (Fin 2) ℚ) (fun _ => 1) 1 ∧ IsMultiHomogeneous (fun _ => 1) (det2 ℚ) ∧
    ShearInv (D := 1) (det2 ℚ) ∧ LastNonzero (D := 1) (det2 ℚ) ∧
    (((1 : ℕ) : ℝ) + 1) * (1 : ℕ) * h = formHeight 1 (1 : Matrix (Fin 2) (Fin 2) ℚ) (fun _ => 1) (det2 ℚ) ∧
    ((2 : ℕ) : ℝ) * (1 : ℕ) * (1 : ℕ) * (2 + |h| + Real.log 1) ≤ Θ ∧
    (X (0, 0) : MvPolynomial (Fin 1 × Fin 2) ℚ) ≠ 0 ∧
    (((X (0, 0) : MvPolynomial (Fin 1 × Fin 2) ℚ).totalDegree : ℕ) : ℝ) ≤ Θ ^ 3 := by
  refine ⟨formHeight 1 (1 : Matrix (Fin 2) (Fin 2) ℚ) (fun _ => 1) (det2 ℚ) / 2, _, sl2, mh2, shear2, last2, by push_cast; ring, le_rfl,
    X_ne_zero _, ?_⟩
  rw [totalDegree_X]
  push_cast
  apply one_le_pow₀
  simp
  linarith [abs_nonneg (formHeight 1 (1 : Matrix (Fin 2) (Fin 2) ℚ) (fun _ => 1) (det2 ℚ) / 2)]

theorem lin_ne {K : Type} [Field K] {N : ℕ} {y : Fin N → K} (hy : y ≠ 0) : lin y ≠ 0 := by
  intro h
  apply hy
  funext j
  have := congrArg (eval (fun p : Fin 1 × Fin N => if p.2 = j then (1:K) else 0)) h
  simpa [lin] using this

theorem lin_hom {K : Type} [Field K] {N : ℕ} (y : Fin N → K) : (lin y).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => by simpa using (isHomogeneous_X K ((0 : Fin 1), j)).mul (isHomogeneous_C _ (y j))

theorem nosq {K : Type} [Field K] {N : ℕ} {z : Fin N → K} (hz : z ≠ 0) : NoSquare (lin z) := by
  refine ⟨lin_ne hz, fun y hy h => ?_⟩
  have := totalDegree_le_of_dvd_of_isDomain h (lin_ne hz)
  rw [(lin_hom z).totalDegree (lin_ne hz), ((lin_hom y).pow 2).totalDegree (pow_ne_zero _ (lin_ne hy))] at this
  omega

theorem not_nosq {K : Type} [Field K] {N : ℕ} {z : Fin N → K} (hz : z ≠ 0) : ¬ NoSquare (lin z ^ 2) :=
  fun h => h.2 z hz dvd_rfl

theorem avoid : AvoidPoly (projTuple 1) 1 := by
  refine ⟨X ((0 : Fin 1), (0 : Fin 2)), X_ne_zero _, (totalDegree_X _).le, fun K _ _ _ s hs x hx => ?_⟩
  have hb := (projTuple.isAdelic 1 le_rfl).geom.alg.bpf.coords_ne_zero x.1
  have hl : ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (projTuple 1).th = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus ((projTuple 1).b (1 : Fin 2)) :=
    GlobalTheory.nonzeroLocus_secToPow _ le_rfl
  rw [hl, ← LinSys.val_ne_zero_iff]
  intro h1
  have h := hx (0 : Fin 1)
  have e : ∑ j, s (0 : Fin 1) j * (projTuple 1).coords x.1 j = s (0 : Fin 1) (0 : Fin 2) * (projTuple 1).coords x.1 (0 : Fin 2) + s (0 : Fin 1) (1 : Fin 2) * (projTuple 1).coords x.1 (1 : Fin 2) := Fin.sum_univ_two _
  have h1' : (projTuple 1).coords x.1 (1 : Fin 2) = 0 := h1
  rw [e, h1', mul_zero, add_zero] at h
  have hs' : s (0 : Fin 1) (0 : Fin 2) ≠ 0 := by simpa using hs
  apply hb
  funext j
  have h0 := (mul_eq_zero.1 h).resolve_left hs'
  revert j
  exact Fin.forall_fin_two.2 ⟨h0, h1'⟩

end Check

end GlobalTheory.HSChoice

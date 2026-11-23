import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.StatementU
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.KTypeHighest

section OneParam

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem hasDerivAt_of_hasDerivAt_shift (U : ℝ → H →L[ℂ] H) (hadd : ∀ s t v, U (s + t) v = U s (U t v))
    (v w : H) (t : ℝ) (hd : HasDerivAt (fun s => U s (U t v)) w 0) :
    HasDerivAt (fun s => U s v) w t := by
  have h1 : HasDerivAt (fun s => U s (U t v)) w (t - t) := by rw [sub_self]; exact hd
  have h2 := HasDerivAt.comp_sub_const t t h1
  convert h2 using 1
  funext s
  show U s v = U (s - t) (U t v)
  rw [← hadd, sub_add_cancel]

theorem eigen (U : ℝ → H →L[ℂ] H) (h0 : ∀ v, U 0 v = v)
    (hadd : ∀ s t v, U (s + t) v = U s (U t v)) (v : H) (c : ℂ)
    (hd : HasDerivAt (fun t => U t v) (c • v) 0) : U 1 v = Complex.exp c • v := by
  have hder : ∀ t, HasDerivAt (fun s => U s v) (c • U t v) t := by
    intro t
    apply hasDerivAt_of_hasDerivAt_shift U hadd v _ t
    have h1 : (fun s => U s (U t v)) = fun s => U t (U s v) := by
      funext s; rw [← hadd, ← hadd, add_comm]
    rw [h1]
    have h2 := ((U t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    simp only [ContinuousLinearMap.coe_restrictScalars'] at h2
    rw [map_smul] at h2
    exact h2
  let L : H →L[ℂ] H := c • ContinuousLinearMap.id ℂ H
  have hL : ∀ x, L x = c • x := fun x => rfl
  let g : ℝ → H := fun t => Complex.exp (c * t) • v
  have hg : ∀ t, HasDerivAt g (c • g t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_mul c
    have h2 := h1.cexp.smul_const v
    convert h2 using 1
    simp only [g, smul_smul, mul_comm]
  have heq : (fun s => U s v) = g := by
    apply ODE_solution_unique_univ (v := fun _ x => L x) (s := fun _ => Set.univ) (K := ‖L‖₊)
      (t₀ := 0)
    · intro _; exact L.lipschitz.lipschitzOnWith
    · intro t; exact ⟨by simpa [hL] using hder t, trivial⟩
    · intro t; exact ⟨by simpa [hL] using hg t, trivial⟩
    · simp [g, h0]
  have := congrFun heq 1
  simpa [g] using this

theorem deriv_mem (S : Submodule ℂ H) [FiniteDimensional ℂ S] (f : ℝ → H) (hf : ∀ t, f t ∈ S) (w : H)
    (hd : HasDerivAt f w 0) : w ∈ S := by
  have hc : IsClosed (S : Set H) := S.closed_of_finiteDimensional
  rw [hasDerivAt_iff_tendsto_slope] at hd
  refine hc.mem_of_tendsto hd (Filter.Eventually.of_forall fun t => ?_)
  rw [slope_def_module]
  exact S.smul_mem _ (S.sub_mem (hf t) (hf 0))

private theorem mem_of_hasDerivAt_linear_of_invariant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : Submodule ℂ E) [FiniteDimensional ℂ T] (L : E →ₗ[ℂ] E) (hLT : ∀ x ∈ T, L x ∈ T)
    (s : Set E) (hTs : ∀ x ∈ T, x ∈ s) (K : NNReal) (hK : LipschitzOnWith K L s)
    (f : ℝ → E) (hfs : ∀ t, f t ∈ s) (hf : ∀ t, HasDerivAt f (L (f t)) t) (h0 : f 0 ∈ T)
    (t : ℝ) : f t ∈ T := by
  haveI : CompleteSpace T := FiniteDimensional.complete ℂ T
  let B : T →L[ℂ] T := LinearMap.toContinuousLinearMap (L.restrict hLT)
  have hB : ∀ y : T, ((B y : T) : E) = L y := fun y => rfl
  let x0 : T := ⟨f 0, h0⟩
  let g : ℝ → E := fun t => ((NormedSpace.exp ((t : ℂ) • B) x0 : T) : E)
  have hg : ∀ t, HasDerivAt g (L (g t)) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℂ => ((NormedSpace.exp (u • B) x0 : T) : E))
        (((B * NormedSpace.exp ((t : ℂ) • B)) x0 : T) : E) (t : ℂ) := by
      have h0 := T.subtypeL.hasFDerivAt.comp_hasDerivAt (t : ℂ)
        ((hasDerivAt_exp_smul_const' B (t : ℂ)).clm_apply (hasDerivAt_const (t : ℂ) x0))
      convert h0 using 1 <;> first | rfl | simp
    have h2 := (h1.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t ((hasDerivAt_id t).ofReal_comp)
    have h3 : HasDerivAt (fun u : ℝ => ((NormedSpace.exp ((u : ℂ) • B) x0 : T) : E))
        (((B * NormedSpace.exp ((t : ℂ) • B)) x0 : T) : E) t := by
      convert h2 using 1 <;> first | rfl | simp
    have h4 : L (g t) = (((B * NormedSpace.exp ((t : ℂ) • B)) x0 : T) : E) := by
      rw [ContinuousLinearMap.mul_apply, hB]
    rw [h4]
    exact h3
  have heq : f = g := by
    apply ODE_solution_unique_univ (v := fun _ x => L x) (s := fun _ => s) (K := K) (t₀ := 0)
    · intro _; exact hK
    · intro t; exact ⟨hf t, hfs t⟩
    · intro t; exact ⟨hg t, hTs _ (NormedSpace.exp ((t : ℂ) • B) x0).2⟩
    · simp [g, x0]
  rw [heq]
  exact (NormedSpace.exp ((t : ℂ) • B) x0).2

private theorem sign_mul_self' {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    (if ε a then (1 : ℂ) else -1) * (if ε a then 1 else -1) = 1 := by
  split <;> norm_num

private theorem sign_eq_neg_of_ne {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) (h : ε a ≠ ε b) :
    (if ε a then (1 : ℂ) else -1) = -(if ε b then 1 else -1) := by
  cases ha : ε a <;> cases hb : ε b <;> simp_all

private theorem sign_eq_of_eq {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) (h : ε a = ε b) :
    (if ε a then (1 : ℂ) else -1) = (if ε b then 1 else -1) := by
  rw [h]

end OneParam

section Alg

variable {n : ℕ} {ε : Fin n → Bool}

theorem inK_iff (X : Matrix (Fin n) (Fin n) ℂ) :
    inK ε X ↔ Xᴴ = -X ∧ ∀ a b, ε a ≠ ε b → X a b = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    have hc : ∀ a b, X a b * (if ε b then (1 : ℂ) else -1) = (if ε a then (1 : ℂ) else -1) * X a b := by
      intro a b
      have := congrFun (congrFun h2 a) b
      simpa [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] using this
    have hg : ∀ a b, star (X b a) * (if ε b then (1 : ℂ) else -1) +
        (if ε a then (1 : ℂ) else -1) * X a b = 0 := by
      intro a b
      have := congrFun (congrFun h1 a) b
      simpa [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] using this
    have hz : ∀ a b, ε a ≠ ε b → X a b = 0 := by
      intro a b hab
      have e1 := hc a b
      have e2 := sign_eq_neg_of_ne ε a b hab
      have e3 := sign_mul_self' ε b
      linear_combination ((if ε b then (1 : ℂ) else -1) / 2) * e1 +
        ((if ε b then (1 : ℂ) else -1) * X a b / 2) * e2 - X a b * e3
    refine ⟨?_, hz⟩
    ext a b
    rw [Matrix.conjTranspose_apply, Matrix.neg_apply]
    by_cases hab : ε a = ε b
    · have e1 := hg a b
      have e2 := sign_eq_of_eq ε a b hab
      have e3 := sign_mul_self' ε b
      linear_combination (if ε b then (1 : ℂ) else -1) * e1 -
        ((if ε b then (1 : ℂ) else -1) * X a b) * e2 - (star (X b a) + X a b) * e3
    · rw [hz a b hab, hz b a (Ne.symm hab)]
      simp
  · rintro ⟨hX, hz⟩
    have hcomm : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X := by
      ext a b
      simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hab : ε a = ε b
      · rw [sign_eq_of_eq ε a b hab]; ring
      · rw [hz a b hab]; ring
    refine ⟨?_, hcomm⟩
    show Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0
    rw [hX, neg_mul, hcomm, neg_add_cancel]

theorem inK_diag (θ : Fin n → ℝ) : inK ε (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  rw [inK_iff]
  refine ⟨?_, fun a b hab => ?_⟩
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
    congr 1
    funext a
    simp
  · have hne : a ≠ b := fun h => hab (h ▸ rfl)
    exact Matrix.diagonal_apply_ne _ hne

theorem inK_single {a b : Fin n} (hab : ε a = ε b) (c : ℂ) :
    inK ε (Matrix.single a b c - Matrix.single b a (star c)) := by
  rw [inK_iff]
  refine ⟨?_, fun i j hij => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply]
    have e1 : (a = j ∧ b = i) ↔ (b = i ∧ a = j) := and_comm
    have e2 : (b = j ∧ a = i) ↔ (a = i ∧ b = j) := and_comm
    simp only [e1, e2]
    split_ifs <;> simp [star_sub]
  · simp only [Matrix.sub_apply, Matrix.single_apply]
    rw [if_neg, if_neg, sub_zero]
    · rintro ⟨rfl, rfl⟩; simp_all
    · rintro ⟨rfl, rfl⟩; simp_all

theorem exp_diag (θ : Fin n → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) =
      Matrix.diagonal fun a => Complex.exp (((t * θ a : ℝ) : ℂ) * Complex.I) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext a
  rw [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
  congr 1
  push_cast
  ring

theorem exp_mem_K {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := by
  have hXs := ((inK_iff X).1 hX).1
  have hcomm : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X := hX.2
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    have hs : star (NormedSpace.exp ((t : ℂ) • X)) = NormedSpace.exp (-((t : ℂ) • X)) := by
      rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hXs,
        smul_neg]
      simp
    rw [hs, ← Matrix.exp_add_of_commute _ _ ((Commute.refl ((t : ℂ) • X)).neg_right), add_neg_cancel,
      NormedSpace.exp_zero]
  · have hc : Commute (Formalism.REAL.Jm ε) ((t : ℂ) • X) := (Commute.smul_right hcomm.symm _)
    exact hc.exp_right.eq.symm

variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem sum_diag (E : Fin n → Fin n → Module.End ℂ W) (d : Fin n → ℂ) (v : W) :
    ∑ a, ∑ b, Matrix.diagonal d a b • E a b v = ∑ a, d a • E a a v := by
  simp [Matrix.diagonal_apply, ite_smul, Finset.sum_ite_eq]

theorem sum_single (E : Fin n → Fin n → Module.End ℂ W) (a b : Fin n) (c : ℂ) (v : W) :
    ∑ i, ∑ j, Matrix.single a b c i j • E i j v = c • E a b v := by
  simp [Matrix.single_apply, ite_and, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem isWeight_root {E : Fin n → Fin n → Module.End ℂ W} (hE : GlRel E) {μ : Fin n → ℝ} {u : W}
    (hu : IsWeight E μ u) (a b : Fin n) : IsWeight E (μ + root a b) (E a b u) := by
  intro c
  have h : E c c (E a b u) - E a b (E c c u) =
      (if c = a then E c b else 0) u - (if b = c then E a c else 0) u :=
    LinearMap.congr_fun (hE c c a b) u
  have hu' : ∀ d, E d d u = (μ d : ℂ) • u := hu
  rw [hu' c, map_smul] at h
  have key : (if c = a then E c b else 0) u - (if b = c then E a c else 0) u =
      ((((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ)) : ℂ) • E a b u := by
    split_ifs <;> subst_vars <;> simp_all
  have hr : (((μ + Formalism.REAL.root a b) c : ℝ) : ℂ) =
      (μ c : ℂ) + ((((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ)) : ℂ) := by
    simp [Formalism.REAL.root, Pi.single_apply]
  rw [sub_eq_iff_eq_add'] at h
  rw [h, key, hr, add_smul]

private theorem sum_mul_root_eq_sub' {n : ℕ} (i j : Fin n) :
    ∑ k : Fin n, ((k : ℕ) : ℝ) * Formalism.REAL.root i j k = ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) := by
  simp [Formalism.REAL.root, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

theorem not_cdom (Λ : Fin n → ℝ) {a b : Fin n} (hab : a < b) : ¬ CDom ε (Λ + root a b) Λ := by
  rintro ⟨c, hc, heq⟩
  let φ : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ k : Fin n, ((k : ℕ) : ℝ) • LinearMap.proj k
  have hφx : ∀ x, φ x = ∑ k : Fin n, ((k : ℕ) : ℝ) * x k := by
    intro x; simp [φ]
  have hφr : ∀ i j, φ (Formalism.REAL.root i j) = ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) := by
    intro i j; rw [hφx]; exact sum_mul_root_eq_sub' i j
  have hneg : Λ - (Λ + Formalism.REAL.root a b) = -Formalism.REAL.root a b := by abel
  have key : -(((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) =
      ∑ i, ∑ j, ((c i j : ℕ) : ℝ) * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) := by
    have h1 := congrArg φ heq
    rw [hneg, map_neg, hφr] at h1
    rw [h1, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, hφr, smul_eq_mul]
  have hle : ∑ i, ∑ j, ((c i j : ℕ) : ℝ) * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    apply Finset.sum_nonpos
    intro j _
    by_cases h : c i j = 0
    · simp [h]
    · have hij := (hc i j h).1
      have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

end Alg

section Rep

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Vs : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ Vs}

theorem group_zero (hσ : IsURepOn (UJset ε) σ) (Z : Matrix (Fin n) (Fin n) ℂ) (v : H) :
    σ (NormedSpace.exp (((0 : ℝ) : ℂ) • Z)) v = v := by
  rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1]
  rfl

private theorem Jm_mul_JmFlagMeasures (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext a
  split <;> norm_num

private theorem inUJ_exp_smul_of_inG {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z) (t : ℝ) :
    Formalism.REAL.inUJ ε (NormedSpace.exp ((t : ℂ) • Z)) := by
  have hJJ := Jm_mul_JmFlagMeasures ε
  have hst : star (t : ℂ) = t := by simp
  have hAg : ((t : ℂ) • Z)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * ((t : ℂ) • Z) = 0 := by
    have hZ' : Zᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Z = 0 := hZ
    rw [Matrix.conjTranspose_smul, hst, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hZ', smul_zero]
  have hA : ((t : ℂ) • Z)ᴴ = Formalism.REAL.Jm ε * (-((t : ℂ) • Z)) * Formalism.REAL.Jm ε := by
    calc ((t : ℂ) • Z)ᴴ = ((t : ℂ) • Z)ᴴ * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) := by rw [hJJ, mul_one]
      _ = (((t : ℂ) • Z)ᴴ * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by rw [mul_assoc]
      _ = (-(Formalism.REAL.Jm ε * ((t : ℂ) • Z))) * Formalism.REAL.Jm ε := by
        rw [eq_neg_of_add_eq_zero_left hAg]
      _ = Formalism.REAL.Jm ε * (-((t : ℂ) • Z)) * Formalism.REAL.Jm ε := by rw [mul_neg, neg_mul]
  have hconj : NormedSpace.exp (Formalism.REAL.Jm ε * (-((t : ℂ) • Z)) * Formalism.REAL.Jm ε) =
      Formalism.REAL.Jm ε * NormedSpace.exp (-((t : ℂ) • Z)) * Formalism.REAL.Jm ε :=
    Matrix.exp_units_conj ⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, hJJ, hJJ⟩ (-((t : ℂ) • Z))
  show (NormedSpace.exp ((t : ℂ) • Z))ᴴ * Formalism.REAL.Jm ε * NormedSpace.exp ((t : ℂ) • Z) = Formalism.REAL.Jm ε
  rw [← Matrix.exp_conjTranspose, hA, hconj]
  calc Formalism.REAL.Jm ε * NormedSpace.exp (-((t : ℂ) • Z)) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε *
        NormedSpace.exp ((t : ℂ) • Z)
      = Formalism.REAL.Jm ε * (NormedSpace.exp (-((t : ℂ) • Z)) * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) *
        NormedSpace.exp ((t : ℂ) • Z)) := by simp only [mul_assoc]
    _ = Formalism.REAL.Jm ε := by
      rw [hJJ, mul_one, ← Matrix.exp_add_of_commute _ _ ((Commute.refl ((t : ℂ) • Z)).neg_left), neg_add_cancel,
        NormedSpace.exp_zero, mul_one]

theorem group_add (hσ : IsURepOn (UJset ε) σ) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z)
    (s t : ℝ) (v : H) :
    σ (NormedSpace.exp (((s + t : ℝ) : ℂ) • Z)) v =
      σ (NormedSpace.exp ((s : ℂ) • Z)) (σ (NormedSpace.exp ((t : ℂ) • Z)) v) := by
  have hs := inUJ_exp_smul_of_inG hZ s
  have ht := inUJ_exp_smul_of_inG hZ t
  rw [Complex.ofReal_add, add_smul,
    Matrix.exp_add_of_commute _ _ (((Commute.refl Z).smul_left (s : ℂ)).smul_right (t : ℂ)),
    hσ.1.2 _ hs _ ht]
  rfl

theorem isWtOn_of_isWeight (hσ : IsURepOn (UJset ε) σ)
    (hE : ∀ X, inG ε X → ∀ u : Vs,
      HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X u) ((∑ a, ∑ b, X a b • E a b u : Vs) : H) 0)
    (μ : Fin n → ℝ) (v : Vs) (hv : IsWeight E μ v) : IsWtOn (Kset ε) σ μ (v : H) := by
  intro θ _
  have hK := inK_diag (ε := ε) θ
  have hv' : ∀ a, E a a v = (μ a : ℂ) • v := hv
  have hsum : ((∑ a, ∑ b, (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) a b • E a b v : Vs) : H) =
      (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • (v : H) := by
    rw [sum_diag]
    simp only [hv', smul_smul, ← Finset.sum_smul, Submodule.coe_smul]
    congr 1
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have hder : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) •
      Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)) (v : H))
      ((((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • (v : H)) 0 := by
    rw [← hsum]; exact hE _ hK.1 v
  have h1 := eigen (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) •
      Matrix.diagonal fun a => (θ a : ℂ) * Complex.I))) (fun w => group_zero hσ _ w)
    (group_add hσ hK.1) (v : H) _ hder
  have hx : NormedSpace.exp (((1 : ℝ) : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) =
      Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) := by
    rw [exp_diag]; simp only [one_mul]
  rw [← hx]
  exact h1

theorem isWeight_of_isWtOn
    (hE : ∀ X, inG ε X → ∀ u : Vs,
      HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X u) ((∑ a, ∑ b, X a b • E a b u : Vs) : H) 0)
    (μ : Fin n → ℝ) (v : Vs) (hv : IsWtOn (Kset ε) σ μ (v : H)) : IsWeight E μ v := by
  intro a
  have hK := inK_diag (ε := ε) (Pi.single a (1 : ℝ) : Fin n → ℝ)
  have hder := hE _ hK.1 v
  have hs0 : ∀ t : ℝ, ∑ b, μ b * (t * (Pi.single a (1 : ℝ) : Fin n → ℝ) b) = t * μ a := by
    intro t
    rw [Finset.sum_eq_single a]
    · simp; ring
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hf : GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ (Matrix.diagonal fun b => (((Pi.single a (1 : ℝ) : Fin n → ℝ) b : ℝ) : ℂ) *
      Complex.I) (v : H) = fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H) := by
    funext t
    have hm := exp_mem_K hK t
    rw [exp_diag] at hm
    show σ (NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun b => (((Pi.single a (1 : ℝ) : Fin n → ℝ) b : ℝ) : ℂ) *
      Complex.I)) (v : H) = _
    rw [exp_diag, hv _ hm, hs0]
    congr 2
    push_cast
    ring
  have h2 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H))
      (((μ a : ℂ) * Complex.I) • (v : H)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * ((μ a : ℂ) * Complex.I)) ((μ a : ℂ) * Complex.I) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const ((μ a : ℂ) * Complex.I)
    simpa using h1.cexp.smul_const (v : H)
  rw [hf] at hder
  have h3 := hder.unique h2
  rw [sum_diag] at h3
  have hs : ∑ b, ((((Pi.single a (1 : ℝ) : Fin n → ℝ) b : ℝ) : ℂ) * Complex.I) • E b b v = Complex.I • E a a v := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  rw [hs] at h3
  apply Subtype.ext
  rw [Submodule.coe_smul]
  have h4 : Complex.I • ((E a a v : Vs) : H) = Complex.I • ((μ a : ℂ) • (v : H)) := by
    rw [← Submodule.coe_smul, h3, smul_smul, mul_comm]
  exact smul_right_injective H Complex.I_ne_zero h4

private theorem sum_smul_E_mem_of_isKStableOn {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Vs : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ Vs}
    (hE : ∀ X, inG ε X → ∀ u : Vs,
      HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X u) ((∑ a, ∑ b, X a b • E a b u : Vs) : H) 0)
    (S : Submodule ℂ H) [FiniteDimensional ℂ S] (hS : IsKStableOn ε σ S)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : inK ε X) (u : Vs) (hu : (u : H) ∈ S) :
    ((∑ a, ∑ b, X a b • E a b u : Vs) : H) ∈ S :=
  deriv_mem S (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X u) (fun t => hS _ (exp_mem_K hX t) _ hu) _ (hE X hX.1 u)

private theorem sum_single_sub_single_star_smul_E {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (E : Fin n → Fin n → Module.End ℂ W) (a b : Fin n) (c : ℂ) (v : W) :
    ∑ i, ∑ j, (Matrix.single a b c - Matrix.single b a (star c)) i j • E i j v =
      c • E a b v - star c • E b a v := by
  simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, sum_single]

theorem kStable_comap
    (hE : ∀ X, inG ε X → ∀ u : Vs,
      HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X u) ((∑ a, ∑ b, X a b • E a b u : Vs) : H) 0)
    (S : Submodule ℂ H) [FiniteDimensional ℂ S] (hS : IsKStableOn ε σ S) :
    KStable ε E (S.comap Vs.subtype) := by
  intro a b hab x hx
  have hx' : (x : H) ∈ S := hx
  have h1 := sum_smul_E_mem_of_isKStableOn hE S hS _ (inK_single hab (1 : ℂ)) x hx'
  have h2 := sum_smul_E_mem_of_isKStableOn hE S hS _ (inK_single hab Complex.I) x hx'
  rw [sum_single_sub_single_star_smul_E] at h1 h2
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have key : ((E a b x : Vs) : H) =
      (1 / 2 : ℂ) • (((1 : ℂ) • E a b x - star (1 : ℂ) • E b a x : Vs) : H) +
      (-(Complex.I / 2)) • ((Complex.I • E a b x - star Complex.I • E b a x : Vs) : H) := by
    simp only [Submodule.coe_sub, Submodule.coe_smul, star_one, Complex.star_def, Complex.conj_I]
    match_scalars <;> first
      | linear_combination (1 / 2 : ℂ) * hI
      | linear_combination (-1 / 2 : ℂ) * hI
  show ((E a b x : Vs) : H) ∈ S
  rw [key]
  exact S.add_mem (S.smul_mem _ h1) (S.smul_mem _ h2)

private theorem hasDerivAt_of_hasDerivAt_coe {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Vs : Submodule ℂ H) (g : ℝ → Vs) (w : Vs) (t : ℝ)
    (h : HasDerivAt (fun s => (g s : H)) (w : H) t) : HasDerivAt g w t := by
  rw [hasDerivAt_iff_tendsto_slope] at h ⊢
  rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff]
  refine h.congr (fun s => ?_)
  simp [slope_def_module]

theorem kStableOn_map (hσ : IsURepOn (UJset ε) σ)
    (hE : ∀ X, inG ε X → ∀ u : Vs,
      HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X u) ((∑ a, ∑ b, X a b • E a b u : Vs) : H) 0)
    (S : Submodule ℂ H) [FiniteDimensional ℂ S] (hS : IsKStableOn ε σ S) (hle : S ≤ Vs)
    (T : Submodule ℂ Vs) (hT : KStable ε E T) (hTS : T.map Vs.subtype ≤ S) :
    IsKStableOn ε σ (T.map Vs.subtype) := by
  intro g hg w hw
  obtain ⟨Y, hY, hexp, -⟩ := Formalism.REAL.compact_exists_log_bounded ε g hg
  obtain ⟨u, hu, rfl⟩ := hw
  haveI hS' : FiniteDimensional ℂ (S.comap Vs.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hle).symm.finiteDimensional
  have hTle : T ≤ S.comap Vs.subtype := fun x hx => hTS ⟨x, hx, rfl⟩
  haveI : FiniteDimensional ℂ T := Submodule.finiteDimensional_of_le hTle
  let L : Module.End ℂ Vs := ∑ i, ∑ j, Y i j • E i j
  have hL : ∀ x, L x = ∑ i, ∑ j, Y i j • E i j x := by
    intro x; simp [L]
  have hLT : ∀ x ∈ T, L x ∈ T := by
    intro x hx
    rw [hL]
    refine T.sum_mem (fun i _ => T.sum_mem (fun j _ => ?_))
    by_cases hij : ε i = ε j
    · exact T.smul_mem _ (hT i j hij x hx)
    · rw [((inK_iff Y).1 hY).2 i j hij, zero_smul]
      exact T.zero_mem
  let C : (S.comap Vs.subtype) →L[ℂ] Vs :=
    LinearMap.toContinuousLinearMap (L ∘ₗ (S.comap Vs.subtype).subtype)
  have hK : LipschitzOnWith ‖C‖₊ L (S.comap Vs.subtype) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hC : L x - L y = C (⟨x, hx⟩ - ⟨y, hy⟩) := by
      rw [map_sub]; rfl
    rw [dist_eq_norm, dist_eq_norm, hC, coe_nnnorm]
    refine (C.le_opNorm _).trans (le_of_eq ?_)
    rfl
  have hmemS : ∀ t : ℝ, σ (NormedSpace.exp ((t : ℂ) • Y)) (u : H) ∈ S :=
    fun t => hS _ (exp_mem_K hY t) _ (hTS ⟨u, hu, rfl⟩)
  let f : ℝ → Vs := fun t => ⟨σ (NormedSpace.exp ((t : ℂ) • Y)) (u : H), hle (hmemS t)⟩
  have hf : ∀ t, HasDerivAt f (L (f t)) t := by
    intro t
    apply hasDerivAt_of_hasDerivAt_coe Vs f (L (f t)) t
    rw [hL]
    exact hasDerivAt_of_hasDerivAt_shift (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • Y))) (group_add hσ hY.1) (u : H) _ t
      (hE Y hY.1 (f t))
  have h0 : f 0 ∈ T := by
    have : f 0 = u := Subtype.ext (group_zero hσ Y u)
    rw [this]; exact hu
  have key := mem_of_hasDerivAt_linear_of_invariant T L hLT (S.comap Vs.subtype) (fun x hx => hTle hx) ‖C‖₊ hK f
    (fun t => hmemS t) hf h0 1
  refine ⟨f 1, key, ?_⟩
  show σ (NormedSpace.exp (((1 : ℝ) : ℂ) • Y)) (u : H) = σ g (u : H)
  rw [Complex.ofReal_one, one_smul, hexp]

end Rep

theorem kType_generated_by_highest : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Vs : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ Vs), IsURepOn (UJset ε) σ → ((∀ u, u ∈ Vs ↔ SmoothOnGV ε (fun g => σ g u)) ∧ GlRel E ∧ IsUnitary ε E ∧ (∀ X, inG ε X → ∀ u : Vs, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X u) ((∑ a, ∑ b, X a b • E a b u : Vs) : H) 0) ∧ ∀ a b (u : Vs), ∀ g ∈ UJset ε, σ g (E a b u) = EabV ε a b (fun g => σ g u) g) → ∀ (Λ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ Λ S → S ≤ Vs → ∃ u : Vs, u ≠ 0 ∧ KHighest ε E Λ u ∧ (kSpan ε E u).map Vs.subtype = S ∧ FiniteDimensional ℂ (kSpan ε E u) := by
  intro n ε H _ _ _ σ Vs E hσ hc Λ S hS hle
  obtain ⟨_, hgl, _, hE, _⟩ := hc
  obtain ⟨hfin, hKS, hirr, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS
  haveI := hfin
  let u : Vs := ⟨v, hle hvS⟩
  have hwt : IsWeight E Λ u := isWeight_of_isWtOn hE Λ u hvw
  have hS' : KStable ε E (S.comap Vs.subtype) := kStable_comap hE S hKS
  have hhigh : KHighest ε E Λ u := by
    refine ⟨hwt, fun a b hab hε => ?_⟩
    by_contra hne
    have hmem : ((E a b u : Vs) : H) ∈ S := hS' a b hε u hvS
    have hw2 : IsWeight E (Λ + root a b) (E a b u) := isWeight_root hgl hwt a b
    have hw3 := isWtOn_of_isWeight hσ hE (Λ + root a b) (E a b u) hw2
    have hne' : ((E a b u : Vs) : H) ≠ 0 := by
      rwa [ne_eq, Submodule.coe_eq_zero]
    exact not_cdom (ε := ε) Λ hab (hdom _ _ hmem hne' hw3)
  have hKle : kSpan ε E u ≤ S.comap Vs.subtype := sInf_le ⟨hvS, hS'⟩
  have hKst : KStable ε E (kSpan ε E u) := by
    intro a b hab x hx
    simp only [Formalism.REAL.kSpan, Submodule.mem_sInf] at hx ⊢
    intro T hT
    exact hT.2 a b hab x (hx T hT)
  have hum : u ∈ kSpan ε E u := by
    simp only [Formalism.REAL.kSpan, Submodule.mem_sInf]
    intro T hT
    exact hT.1
  haveI : FiniteDimensional ℂ (S.comap Vs.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hle).symm.finiteDimensional
  have hfinK : FiniteDimensional ℂ (kSpan ε E u) := Submodule.finiteDimensional_of_le hKle
  have hmapS : (kSpan ε E u).map Vs.subtype ≤ S := Submodule.map_le_iff_le_comap.2 hKle
  have hKS2 := kStableOn_map hσ hE S hKS hle (kSpan ε E u) hKst hmapS
  refine ⟨u, ?_, hhigh, ?_, hfinK⟩
  · intro h
    apply hv0
    have := congrArg Subtype.val h
    simpa [u] using this
  · rcases hirr _ hmapS hKS2 with h | h
    · exfalso
      have hvm : v ∈ (kSpan ε E u).map Vs.subtype := ⟨u, hum, rfl⟩
      rw [h, Submodule.mem_bot] at hvm
      exact hv0 hvm
    · exact h

end GlobalTheory.KTypeHighest

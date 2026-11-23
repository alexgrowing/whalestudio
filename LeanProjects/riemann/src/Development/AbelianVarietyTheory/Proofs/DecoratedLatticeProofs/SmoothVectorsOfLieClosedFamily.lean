import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianCommutation.PCkPartials
open Matrix
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SmoothCrit

open GlobalTheory.UnitarySmVec GlobalTheory.HolDict

section Mat
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

theorem contDiff_expM : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) :=
  contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt

theorem contDiff_init {k : ℕ} : ContDiff ℝ ∞ fun t : Fin (k + 1) → ℝ => Fin.init t :=
  contDiff_pi.2 fun j => contDiff_apply ℝ ℝ (Fin.castSucc j)

theorem contDiff_pr : ∀ {k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ), ContDiff ℝ ∞ (pr Xs)
  | 0, Xs => by
    have e : pr Xs = fun _ => 1 := funext (pr_zero Xs)
    rw [e]
    exact contDiff_const
  | k + 1, Xs => by
    have e : pr Xs = fun t => pr (Fin.init Xs) (Fin.init t) * NormedSpace.exp (t (Fin.last k) • Xs (Fin.last k)) :=
      funext (pr_succ Xs)
    rw [e]
    exact ((contDiff_pr (Fin.init Xs)).comp contDiff_init).mul
      (contDiff_expM.comp ((contDiff_apply ℝ ℝ (Fin.last k)).smul contDiff_const))

theorem coord {Hm : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit Hm.det) : ∀ {k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ),
    (∀ j, Xs j ∈ lieH Hm) → ∀ m : Fin k, ∃ Y : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ, ContDiff ℝ ∞ Y ∧
      (∀ t, Y t ∈ lieH Hm) ∧
      ∀ (t : Fin k → ℝ) (s : ℝ), pr Xs (t + s • Pi.single m 1) = pr Xs t * NormedSpace.exp (s • Y t)
  | 0, _, _, m => m.elim0
  | k + 1, Xs, hX, m => by
    refine Fin.lastCases ?_ (fun m' => ?_) m
    · refine ⟨fun _ => Xs (Fin.last k), contDiff_const, fun _ => hX _, fun t s => ?_⟩
      have e1 : Fin.init (t + s • Pi.single (Fin.last k) (1:ℝ)) = Fin.init t := by
        funext j
        simp [Fin.init, Pi.single_apply, Fin.castSucc_ne_last]
      have e2 : (t + s • Pi.single (Fin.last k) (1:ℝ) : Fin (k + 1) → ℝ) (Fin.last k) = t (Fin.last k) + s := by simp
      rw [pr_succ, pr_succ Xs t, e1, e2, add_smul,
        Matrix.exp_add_of_commute _ _ (((Commute.refl (Xs (Fin.last k))).smul_left _).smul_right _), mul_assoc]
    · obtain ⟨Y', hY', hYl, hYe⟩ := coord hu (Fin.init Xs) (fun j => hX _) m'
      refine ⟨fun t => NormedSpace.exp (-(t (Fin.last k) • Xs (Fin.last k))) * Y' (Fin.init t) *
        NormedSpace.exp (t (Fin.last k) • Xs (Fin.last k)), ?_, ?_, ?_⟩
      · have hl : ContDiff ℝ ∞ fun t : Fin (k+1) → ℝ => t (Fin.last k) • Xs (Fin.last k) :=
          (contDiff_apply ℝ ℝ (Fin.last k)).smul contDiff_const
        exact ((contDiff_expM.comp hl.neg).mul (hY'.comp contDiff_init)).mul (contDiff_expM.comp hl)
      · intro t
        have hg := exp_mem hu (hX (Fin.last k)) (t (Fin.last k))
        have := lie_conj hu (hYl (Fin.init t)) hg
        simpa only [Matrix.exp_neg] using this
      · intro t s
        have e1 : Fin.init (t + s • Pi.single (Fin.castSucc m') (1:ℝ)) = Fin.init t + s • Pi.single m' 1 := by
          funext j
          simp [Fin.init, Pi.single_apply]
        have e2 : (t + s • Pi.single (Fin.castSucc m') (1:ℝ) : Fin (k + 1) → ℝ) (Fin.last k) = t (Fin.last k) := by
          simp [Pi.single_apply, (Fin.castSucc_lt_last m').ne']
        rw [pr_succ, pr_succ Xs t, e1, e2, hYe]
        beta_reduce
        rw [Matrix.exp_neg]
        have hgd : IsUnit (NormedSpace.exp (t (Fin.last k) • Xs (Fin.last k))).det :=
          det_unit hu (exp_mem hu (hX (Fin.last k)) (t (Fin.last k)))
        have hgu : IsUnit (NormedSpace.exp (t (Fin.last k) • Xs (Fin.last k))) := (isUnit_iff_isUnit_det _).2 hgd
        set g := NormedSpace.exp (t (Fin.last k) • Xs (Fin.last k))
        rw [show s • (g⁻¹ * Y' (Fin.init t) * g) = g⁻¹ * (s • Y' (Fin.init t)) * g by
            rw [Matrix.mul_smul, Matrix.smul_mul], Matrix.exp_conj' _ _ hgu, mul_assoc, mul_assoc, mul_assoc,
          ← mul_assoc g, mul_nonsing_inv _ hgd, one_mul]

end Mat

section Main
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {Hm : Matrix (Fin n) (Fin n) ℂ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ι : Type} {v : ι → H} {δ : Matrix (Fin n) (Fin n) ℂ → ι → ι}

theorem v_zero (hs : ∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i)) (i : ι) : v (δ 0 i) = 0 := by
  simpa using hs i 0 0

theorem v_sum (ha : ∀ i X Y, v (δ (X + Y) i) = v (δ X i) + v (δ Y i))
    (hs : ∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i)) {β : Type} (s : Finset β)
    (f : β → Matrix (Fin n) (Fin n) ℂ) (i : ι) : v (δ (∑ b ∈ s, f b) i) = ∑ b ∈ s, v (δ (f b) i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using v_zero hs i
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, ha, ih]

theorem v_expand (ha : ∀ i X Y, v (δ (X + Y) i) = v (δ X i) + v (δ Y i))
    (hs : ∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i)) (Y : Matrix (Fin n) (Fin n) ℂ) (i : ι) :
    v (δ Y i) = ∑ a, ∑ c, (((Y a c).re : ℂ) • v (δ (single a c 1) i) +
      ((Y a c).im : ℂ) • v (δ (Complex.I • single a c 1) i)) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
  rw [v_sum ha hs]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [v_sum ha hs]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e : single a c (Y a c) = ((Y a c).re : ℂ) • single a c 1 + ((Y a c).im : ℂ) • (Complex.I • single a c 1) := by
    rw [smul_smul, ← add_smul, Matrix.smul_single, smul_eq_mul, mul_one, Complex.re_add_im]
  rw [e, ha, hs, hs]

theorem crit_nat (hu : IsUnit Hm.det) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ)
    (ha : ∀ i X Y, v (δ (X + Y) i) = v (δ X i) + v (δ Y i))
    (hs : ∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i))
    (hd : ∀ X, Xᴴ * Hm + Hm * X = 0 → ∀ i, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) (v i)) (v (δ X i)) 0)
    {k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ j, Xs j ∈ lieH Hm) (N : ℕ) :
    ∀ i, ContDiff ℝ N fun t => σ (pr Xs t) (v i) := by
  choose Y hY hYl hYe using coord hu Xs hX
  induction N with
  | zero =>
    intro i
    simp only [Nat.cast_zero, contDiff_zero]
    exact (hσ.2.2 (v i)).comp_continuous (contDiff_pr Xs).continuous fun t => pr_mem hu Xs hX t
  | succ N ih =>
    intro i
    let D : Fin k → (Fin k → ℝ) → H := fun m t => ∑ a, ∑ c,
      ((Y m t a c).re • σ (pr Xs t) (v (δ (single a c 1) i)) +
        (Y m t a c).im • σ (pr Xs t) (v (δ (Complex.I • single a c 1) i)))
    have hD : ∀ m, ContDiff ℝ N (D m) := by
      intro m
      have he : ∀ a c, ContDiff ℝ ∞ fun t => Y m t a c := fun a c =>
        (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a c)).contDiff.comp (hY m)
      refine ContDiff.sum fun a _ => ContDiff.sum fun c _ => ?_
      exact ((contDiff_infty.1 (Complex.reCLM.contDiff.comp (he a c)) N).smul (ih _)).add
        ((contDiff_infty.1 (Complex.imCLM.contDiff.comp (he a c)) N).smul (ih _))
    have hpart : ∀ y m, HasDerivAt (fun s : ℝ => σ (pr Xs (y + s • Pi.single m (1:ℝ))) (v i)) (D m y) 0 := by
      intro y m
      have e : (fun s : ℝ => σ (pr Xs (y + s • Pi.single m (1:ℝ))) (v i)) =
          fun s => σ (pr Xs y) (σ (NormedSpace.exp (s • Y m y)) (v i)) := by
        funext s
        rw [hYe, hσ.1.2 _ (pr_mem hu Xs hX y) _ (exp_mem hu (hYl m y) s)]
        rfl
      rw [e]
      have h1 : HasDerivAt (fun s : ℝ => σ (pr Xs y) (σ (NormedSpace.exp (s • Y m y)) (v i)))
          (σ (pr Xs y) (v (δ (Y m y) i))) 0 :=
        ((σ (pr Xs y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hd _ (hYl m y) i)
      convert h1 using 1
      show _ = σ (pr Xs y) (v (δ (Y m y) i))
      rw [v_expand ha hs (Y m y) i, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_add, map_smul, map_smul, Complex.coe_smul, Complex.coe_smul]
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun y => ∑ m, (ContinuousLinearMap.proj m : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (D m y), ?_, fun y => ?_⟩
    · exact ContDiff.sum fun m _ => contDiff_const.smulRight (hD m)
    · exact PI.UnitaryGroupMassFormula.JCC.Ck.partials_continuous_differentiable k H Set.univ _ D isOpen_univ (fun m => (hD m).continuous.continuousOn)
        (fun y _ m => hpart y m) y trivial

end Main

theorem smoothVec_of_closed_family : ∀ (n : ℕ) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ι : Type) (v : ι → H) (δ : Matrix (Fin n) (Fin n) ℂ → ι → ι), Hm.det ≠ 0 → Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → (∀ i X Y, v (δ (X + Y) i) = v (δ X i) + v (δ Y i)) → (∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i)) → (∀ X, Xᴴ * Hm + Hm * X = 0 → ∀ i, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) (v i)) (v (δ X i)) 0) → ∀ i, Formalism.L2.Theta.SmoothVec {X | Xᴴ * Hm + Hm * X = 0} σ (v i) := by
  intro n Hm H _ _ σ ι v δ hdet hσ ha hs hd i k Xs hX
  have hu : IsUnit Hm.det := isUnit_iff_ne_zero.2 hdet
  exact contDiff_infty.2 fun N => crit_nat hu hσ ha hs hd Xs hX N i

end GlobalTheory.SmoothCrit

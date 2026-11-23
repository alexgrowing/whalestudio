import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents.HighestWeightDifferencesNat
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement

noncomputable section

open Matrix Finset

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

section Shift

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def endomorphismFamilyShift (F : Fin n → Fin n → Module.End ℂ V) (t : Fin n → ℝ) : Fin n → Fin n → Module.End ℂ V :=
  fun a b => F a b + (if a = b then ((t a : ℝ) : ℂ) else 0) • (1 : Module.End ℂ V)

lemma commutator_shift_scalar (X Y : Module.End ℂ V) (s r : ℂ) :
    (X + s • 1) * (Y + r • 1) - (Y + r • 1) * (X + s • 1) = X * Y - Y * X := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add, smul_smul, mul_comm s r]
  abel

theorem ext1Shift_kRel {F : Fin n → Fin n → Module.End ℂ V} (hF : Formalism.REAL.KRel ε F) {t : Fin n → ℝ}
    (ht : ∀ a b, ε a = ε b → t a = t b) : Formalism.REAL.KRel ε (endomorphismFamilyShift F t) := by
  intro a b c d hab hcd
  have h := hF a b c d hab hcd
  simp only [endomorphismFamilyShift]
  rw [commutator_shift_scalar, h]
  by_cases hbc : b = c
  · subst hbc
    by_cases hda : d = a
    · subst hda
      simp [ht _ _ hab]
    · simp [hda, Ne.symm hda]
  · by_cases hda : d = a
    · simp [hbc, Ne.symm hbc, hda]
    · simp [hbc, hda]

theorem ext1Shift_kHighest {F : Fin n → Fin n → Module.End ℂ V} {t μ : Fin n → ℝ} {p : V}
    (hp : Formalism.REAL.KHighest ε F μ p) : Formalism.REAL.KHighest ε (endomorphismFamilyShift F t) (μ + t) p := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · simp [endomorphismFamilyShift, hp.1 a, add_smul]
  · simp [endomorphismFamilyShift, ne_of_lt hab, hp.2 a b hab he]

end Shift

theorem ext1Shift_kUnit {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {F : Fin n → Fin n → Module.End ℂ V} (hF : Formalism.REAL.KUnit ε F) (t : Fin n → ℝ) :
    Formalism.REAL.KUnit ε (endomorphismFamilyShift F t) := by
  intro a b hab x y
  by_cases h : a = b
  · subst h
    simp [endomorphismFamilyShift, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hF a a hab x y]
  · simp [endomorphismFamilyShift, h, Ne.symm h, inner_add_left, inner_add_right, hF a b hab x y]

section Dual

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixFamilyDual (G : Fin n → Fin n → Matrix ι ι ℂ) : Fin n → Fin n → Matrix ι ι ℂ := fun a b => -(G a b)ᵀ

theorem ext1Dual_kRel {G : Fin n → Fin n → Matrix ι ι ℂ} (hG : Formalism.REAL.KRel ε G) :
    Formalism.REAL.KRel ε (matrixFamilyDual G) := by
  intro a b c d hab hcd
  have h := hG a b c d hab hcd
  have h2 : matrixFamilyDual G a b * matrixFamilyDual G c d - matrixFamilyDual G c d * matrixFamilyDual G a b =
      -(G a b * G c d - G c d * G a b)ᵀ := by
    simp only [matrixFamilyDual, neg_mul_neg]
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, neg_sub]
  rw [h2, h]
  split_ifs <;> simp [matrixFamilyDual, Matrix.transpose_sub] <;> abel

theorem ext1Dual_conjT {G : Fin n → Fin n → Matrix ι ι ℂ} (hGu : ∀ a b, ε a = ε b → G b a = (G a b)ᴴ) :
    ∀ a b, ε a = ε b → matrixFamilyDual G b a = (matrixFamilyDual G a b)ᴴ := by
  intro a b h
  ext i j
  simp [matrixFamilyDual, hGu a b h, Matrix.conjTranspose_apply, Matrix.transpose_apply]

theorem ext1Dual_mulVec_star {G : Fin n → Fin n → Matrix ι ι ℂ} (hGu : ∀ a b, ε a = ε b → G b a = (G a b)ᴴ)
    {a b : Fin n} (hab : ε a = ε b) (f : ι → ℂ) : matrixFamilyDual G a b *ᵥ star f = -star (G b a *ᵥ f) := by
  rw [hGu a b hab]
  ext i
  simp [matrixFamilyDual, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.transpose_apply, star_sum, mul_comm]

end Dual

section Tens

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι]

private lemma tensAct_apply_eq_add_sum_smul (A : Fin n → Fin n → Module.End ℂ V) (D : Fin n → Fin n → Matrix ι ι ℂ)
    (a b : Fin n) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensAct A D a b x i = A a b (x i) + ∑ j, D a b i j • x j := by
  simp [tensAct, LinearMap.pi_apply]

lemma tensor_action_mul_apply (A : Fin n → Fin n → Module.End ℂ V) (D : Fin n → Fin n → Matrix ι ι ℂ)
    (a b c d : Fin n) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensAct A D a b (tensAct A D c d x) i = A a b (A c d (x i)) + ∑ j, D c d i j • A a b (x j) +
      (∑ j, D a b i j • A c d (x j) + ∑ k, (D a b * D c d) i k • x k) := by
  rw [tensAct_apply_eq_add_sum_smul A D a b]
  simp only [tensAct_apply_eq_add_sum_smul A D c d, map_add, map_sum, map_smul, smul_add, Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem tensor_action_lie_relations [DecidableEq ι] {A : Fin n → Fin n → Module.End ℂ V} {D : Fin n → Fin n → Matrix ι ι ℂ}
    (hA : Formalism.REAL.KRel ε A) (hD : Formalism.REAL.KRel ε D) : Formalism.REAL.KRel ε (tensAct A D) := by
  intro a b c d hab hcd
  refine LinearMap.ext fun x => PiLp.ext fun i => ?_
  have key : tensAct A D a b (tensAct A D c d x) i - tensAct A D c d (tensAct A D a b x) i =
      (A a b (A c d (x i)) - A c d (A a b (x i))) +
        ∑ k, ((D a b * D c d) i k - (D c d * D a b) i k) • x k := by
    rw [tensor_action_mul_apply, tensor_action_mul_apply]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  have hA' : A a b (A c d (x i)) - A c d (A a b (x i)) =
      ((if b = c then A a d else 0) - (if d = a then A c b else 0)) (x i) := by
    rw [← hA a b c d hab hcd]
    rfl
  have hD' : ∀ k, (D a b * D c d) i k - (D c d * D a b) i k =
      ((if b = c then D a d else 0) - (if d = a then D c b else 0)) i k := fun k => by
    rw [← hD a b c d hab hcd]
    rfl
  show tensAct A D a b (tensAct A D c d x) i - tensAct A D c d (tensAct A D a b x) i = _
  rw [key, hA']
  simp only [hD']
  by_cases hbc : b = c <;> by_cases hda : d = a <;>
    simp [hbc, hda, tensAct_apply_eq_add_sum_smul, sub_smul, Finset.sum_sub_distrib] <;> abel

theorem tensor_action_unitary {A : Fin n → Fin n → Module.End ℂ V} (hA : Formalism.REAL.KUnit ε A)
    {D : Fin n → Fin n → Matrix ι ι ℂ} (hD : ∀ a b, ε a = ε b → D b a = (D a b)ᴴ) :
    Formalism.REAL.KUnit ε (tensAct A D) := by
  intro a b hab x y
  simp only [PiLp.inner_apply, tensAct_apply_eq_add_sum_smul, inner_add_left, inner_add_right, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.sum_add_distrib, hA a b hab, hD a b hab, Matrix.conjTranspose_apply,
    starRingEnd_apply, star_star]
  congr 1
  rw [Finset.sum_comm]

theorem tensor_pure_highest_weight {A : Fin n → Fin n → Module.End ℂ V} {D : Fin n → Fin n → Matrix ι ι ℂ}
    {μA μD : Fin n → ℝ} {p : V} {g : ι → ℂ} (hp : Formalism.REAL.KHighest ε A μA p)
    (hgw : ∀ a, D a a *ᵥ g = ((μD a : ℝ) : ℂ) • g) (hgh : ∀ a b, a < b → ε a = ε b → D a b *ᵥ g = 0) :
    Formalism.REAL.KHighest ε (tensAct A D) (μA + μD) (WithLp.toLp 2 (fun i => g i • p) : PiLp 2 (fun _ : ι => V)) := by
  refine ⟨fun a => PiLp.ext fun i => ?_, fun a b hab he => PiLp.ext fun i => ?_⟩
  · have h1 := congrFun (hgw a) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [tensAct_apply_eq_add_sum_smul, PiLp.smul_apply]
    simp only [PiLp.toLp_apply]
    rw [map_smul, hp.1 a]
    simp_rw [smul_smul]
    rw [← Finset.sum_smul, h1, ← add_smul]
    congr 1
    simp only [Pi.add_apply, Complex.ofReal_add]
    ring
  · have h1 := congrFun (hgh a b hab he) i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
    rw [tensAct_apply_eq_add_sum_smul]
    simp only [PiLp.toLp_apply, PiLp.zero_apply]
    rw [map_smul, hp.2 a b hab he, smul_zero, zero_add]
    simp_rw [smul_smul]
    rw [← Finset.sum_smul, h1, zero_smul]

theorem tensor_action_single [DecidableEq ι] (A : Fin n → Fin n → Module.End ℂ V) (G : Fin n → Fin n → Matrix ι ι ℂ)
    (a b : Fin n) {p : V} {c : ℂ} (hc : A a b p = c • p) (i : ι) :
    tensAct A (matrixFamilyDual G) a b (WithLp.toLp 2 (Pi.single i p) : PiLp 2 (fun _ : ι => V)) =
      c • (WithLp.toLp 2 (Pi.single i p) : PiLp 2 (fun _ : ι => V)) -
        ∑ j, G a b i j • (WithLp.toLp 2 (Pi.single j p) : PiLp 2 (fun _ : ι => V)) := by
  refine PiLp.ext fun k => ?_
  rw [tensAct_apply_eq_add_sum_smul]
  by_cases hk : k = i
  · subst hk
    simp [matrixFamilyDual, Pi.single_apply, hc, sub_eq_add_neg, Finset.sum_ite_eq', Finset.smul_sum]
  · simp [matrixFamilyDual, Pi.single_apply, hk, sub_eq_add_neg, Finset.sum_ite_eq', Finset.smul_sum]

end Tens

end ReciprocityTheory.ChartRestriction.DS.HW

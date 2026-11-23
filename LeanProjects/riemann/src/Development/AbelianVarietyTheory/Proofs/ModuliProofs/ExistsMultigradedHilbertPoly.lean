import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

namespace GlobalTheory.MultiHilbert

open MvPolynomial

variable {r : ℕ}

def EventuallyPoly (f : (Fin r → ℕ) → ℚ) : Prop :=
  ∃ (Φ : MvPolynomial (Fin r) ℚ) (n₀ : ℕ), ∀ n : Fin r → ℕ, (∀ k, n₀ ≤ n k) →
    f n = MvPolynomial.eval (fun k => (n k : ℚ)) Φ

theorem EventuallyPoly.add {f g : (Fin r → ℕ) → ℚ} (hf : EventuallyPoly f)
    (hg : EventuallyPoly g) : EventuallyPoly (fun n => f n + g n) := by
  obtain ⟨Φ, a, h⟩ := hf
  obtain ⟨Ψ, b, h'⟩ := hg
  refine ⟨Φ + Ψ, max a b, fun n hn => ?_⟩
  rw [map_add, ← h n (fun k => (le_max_left _ _).trans (hn k)),
    ← h' n (fun k => (le_max_right _ _).trans (hn k))]

theorem eval_aeval_coord (x : Fin r → ℚ) (p : Fin r → MvPolynomial (Fin r) ℚ)
    (Φ : MvPolynomial (Fin r) ℚ) :
    eval x (aeval p Φ) = eval (fun k => eval x (p k)) Φ := by
  induction Φ using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, aeval_X, eval_X]

theorem EventuallyPoly.shift_add {f : (Fin r → ℕ) → ℚ} (hf : EventuallyPoly f) (e : Fin r → ℕ) :
    EventuallyPoly (fun n => f (n + e)) := by
  obtain ⟨Φ, a, h⟩ := hf
  refine ⟨aeval (fun k => X k + C (e k : ℚ)) Φ, a, fun n hn => ?_⟩
  beta_reduce
  rw [eval_aeval_coord, h (n + e) (fun k => (hn k).trans (Nat.le_add_right _ _))]
  simp

theorem EventuallyPoly.of_shift_add {f : (Fin r → ℕ) → ℚ} (e : Fin r → ℕ)
    (hf : EventuallyPoly (fun n => f (n + e))) : EventuallyPoly f := by
  obtain ⟨Φ, a, h⟩ := hf
  refine ⟨aeval (fun k => X k - C (e k : ℚ)) Φ, a + ∑ k, e k, fun n hn => ?_⟩
  have he : ∀ k, a + e k ≤ n k := fun k =>
    (Nat.add_le_add_left (Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)) a).trans (hn k)
  have h1 : n = (n - e) + e := by
    funext k
    have := he k
    simp only [Pi.add_apply, Pi.sub_apply]
    omega
  have h2 := h (n - e) (fun k => by have := he k; simp only [Pi.sub_apply]; omega)
  simp only [← h1] at h2
  rw [eval_aeval_coord, h2]
  congr 2
  funext k
  have := he k
  simp only [Pi.sub_apply, map_sub, eval_X, eval_C]
  rw [Nat.cast_sub (by omega)]

theorem eval_polynomial_aeval_X (x : Fin r → ℚ) (k : Fin r) (p : Polynomial ℚ) :
    eval x (Polynomial.aeval (X k : MvPolynomial (Fin r) ℚ) p) = p.eval (x k) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.eval_add]
  | monomial n a => simp

theorem eval_monomial_erase (x : Fin r → ℚ) (k : Fin r) (t : ℚ) (d : Fin r →₀ ℕ) (c : ℚ) :
    eval (Function.update x k t) (monomial (d.erase k) c) = eval x (monomial (d.erase k) c) := by
  rw [eval_monomial, eval_monomial]
  congr 1
  refine Finsupp.prod_congr fun j hj => ?_
  have : j ≠ k := by
    rintro rfl
    simp at hj
  rw [Function.update_of_ne this]

theorem exists_antidifference (Φ : MvPolynomial (Fin r) ℚ) (k : Fin r) :
    ∃ Ψ : MvPolynomial (Fin r) ℚ, ∀ x : Fin r → ℚ,
      eval (Function.update x k (x k + 1)) Ψ - eval x Ψ = eval x Φ := by
  induction Φ using MvPolynomial.induction_on' with
  | monomial d c =>
    refine ⟨monomial (d.erase k) (c / (d k + 1)) *
      Polynomial.aeval (X k : MvPolynomial (Fin r) ℚ) (Polynomial.bernoulli (d k + 1)),
      fun x => ?_⟩
    have hd : monomial d c = monomial (d.erase k) c * (X k : MvPolynomial (Fin r) ℚ) ^ d k := by
      rw [X_pow_eq_monomial, monomial_mul, mul_one, Finsupp.erase_add_single]
    rw [map_mul, map_mul, eval_monomial_erase, eval_polynomial_aeval_X, eval_polynomial_aeval_X,
      Function.update_self, add_comm (x k) 1, Polynomial.bernoulli_eval_one_add, hd, map_mul,
      eval_monomial, eval_monomial]
    have : (d k : ℚ) + 1 ≠ 0 := by positivity
    simp only [map_pow, eval_X, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp
    obtain ⟨Q, hQ⟩ := hq
    refine ⟨P + Q, fun x => ?_⟩
    rw [map_add, map_add, map_add, ← hP, ← hQ]
    ring

theorem EventuallyPoly.of_differences {f : (Fin r → ℕ) → ℚ}
    (hf : ∀ k, EventuallyPoly (fun n => f (n + Pi.single k 1) - f n)) : EventuallyPoly f := by
  classical
  choose Φ a h using hf
  choose Ψ hΨ using fun k => exists_antidifference (Φ k) k
  set N := ∑ k, a k with hN
  have haN : ∀ k, a k ≤ N := fun k =>
    Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have step : ∀ (k : Fin r) (m : Fin r → ℕ), (∀ j, N ≤ m j) → ∀ t : ℕ, N ≤ t →
      f (Function.update m k t) - f (Function.update m k N) =
        eval (fun j => ((Function.update m k t j : ℕ) : ℚ)) (Ψ k) -
          eval (fun j => ((Function.update m k N j : ℕ) : ℚ)) (Ψ k) := by
    intro k m hm t ht
    induction t, ht using Nat.le_induction with
    | base => simp
    | succ t ht ih =>
      have h1 := h k (Function.update m k t) (fun j => by
        by_cases hj : j = k
        · subst hj
          simpa using (haN j).trans ht
        · rw [Function.update_of_ne hj]
          exact (haN k).trans (hm j))
      have h2 := hΨ k (fun j => ((Function.update m k t j : ℕ) : ℚ))
      have e1 : Function.update m k t + Pi.single k 1 = Function.update m k (t + 1) := by
        funext j
        by_cases hj : j = k
        · subst hj
          simp
        · simp [hj]
      have e2 : Function.update (fun j => ((Function.update m k t j : ℕ) : ℚ)) k
          (((Function.update m k t k : ℕ) : ℚ) + 1) =
          fun j => ((Function.update m k (t + 1) j : ℕ) : ℚ) := by
        funext j
        by_cases hj : j = k
        · subst hj
          simp
        · simp [hj]
      simp only [e1] at h1
      rw [e2] at h2
      linarith
  have main : ∀ s : Finset (Fin r), ∃ P : MvPolynomial (Fin r) ℚ, ∀ n : Fin r → ℕ,
      (∀ j, N ≤ n j) → f (fun j => if j ∈ s then n j else N) = eval (fun j => (n j : ℚ)) P := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨C (f (fun _ => N)), fun n _ => by simp⟩
    | insert k s hk ih =>
      obtain ⟨P, hP⟩ := ih
      refine ⟨P + aeval (fun j => if j ∈ insert k s then X j else C (N : ℚ)) (Ψ k) -
        aeval (fun j => if j ∈ s then X j else C (N : ℚ)) (Ψ k), fun n hn => ?_⟩
      have h1 := step k (fun j => if j ∈ s then n j else N)
        (fun j => by split_ifs; exacts [hn j, le_rfl]) (n k) (hn k)
      have e1 : Function.update (fun j => if j ∈ s then n j else N) k (n k) =
          fun j => if j ∈ insert k s then n j else N := by
        funext j
        by_cases hj : j = k
        · subst hj
          simp
        · simp [hj]
      have e2 : Function.update (fun j => if j ∈ s then n j else N) k N =
          fun j => if j ∈ s then n j else N := by
        funext j
        by_cases hj : j = k
        · subst hj
          simp [hk]
        · simp [hj]
      rw [e1, e2] at h1
      have e3 : ∀ u : Finset (Fin r), (fun j => eval (fun j => (n j : ℚ))
          (if j ∈ u then X j else C (N : ℚ) : MvPolynomial (Fin r) ℚ)) =
          fun j => (((if j ∈ u then n j else N : ℕ)) : ℚ) := by
        intro u
        funext j
        split_ifs <;> simp
      rw [map_sub, map_add, eval_aeval_coord, eval_aeval_coord, e3, e3, ← hP n hn]
      linarith
  obtain ⟨P, hP⟩ := main Finset.univ
  exact ⟨P, N, fun n hn => by simpa using hP n hn⟩

end GlobalTheory.MultiHilbert

namespace GlobalTheory.MultiHilbert

open MvPolynomial

section
variable {K σ M : Type} [Field K] [AddCancelCommMonoid M] (w : σ → M)

theorem component_X_mul (i : σ) (n : M) (G : MvPolynomial σ K) :
    weightedHomogeneousComponent w (n + w i) (X i * G) =
      X i * weightedHomogeneousComponent w n G := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_X_mul', coeff_X_mul',
    coeff_weightedHomogeneousComponent]
  by_cases hi : i ∈ d.support
  · have hd : d = (d - Finsupp.single i 1) + Finsupp.single i 1 := by
      rw [tsub_add_cancel_of_le]
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi)
    have hw : Finsupp.weight w d = Finsupp.weight w (d - Finsupp.single i 1) + w i := by
      conv_lhs => rw [hd]
      rw [map_add, Finsupp.weight_single, one_smul]
    simp only [hi, if_true, hw, add_left_inj]
  · simp only [hi, if_false, ite_self]

theorem component_mem_span_X (s : Set σ) (n : M) {G : MvPolynomial σ K}
    (hG : G ∈ Ideal.span (X '' s : Set (MvPolynomial σ K))) :
    weightedHomogeneousComponent w n G ∈ Ideal.span (X '' s : Set (MvPolynomial σ K)) := by
  classical
  rw [mem_ideal_span_X_image] at hG ⊢
  intro m hm
  refine hG m ?_
  rw [mem_support_iff, coeff_weightedHomogeneousComponent] at hm
  rw [mem_support_iff]
  intro h
  simp [h] at hm

noncomputable def colonX (I : Ideal (MvPolynomial σ K)) (i : σ) : Ideal (MvPolynomial σ K) :=
  Submodule.comap (LinearMap.mulLeft (MvPolynomial σ K) (X i)) I

theorem mem_colonX {I : Ideal (MvPolynomial σ K)} {i : σ} {G : MvPolynomial σ K} :
    G ∈ colonX I i ↔ X i * G ∈ I := Iff.rfl

theorem le_colonX (I : Ideal (MvPolynomial σ K)) (i : σ) : I ≤ colonX I i :=
  fun _ h => mem_colonX.2 (I.mul_mem_left _ h)

theorem component_mem_colonX {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ n, weightedHomogeneousComponent w n F ∈ I) (i : σ) :
    ∀ F ∈ colonX I i, ∀ n, weightedHomogeneousComponent w n F ∈ colonX I i := by
  intro F hF n
  rw [mem_colonX, ← component_X_mul]
  exact hI _ hF _

theorem component_mem_sup {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ n, weightedHomogeneousComponent w n F ∈ I) (i : σ) :
    ∀ F ∈ I ⊔ Ideal.span {X i}, ∀ n,
      weightedHomogeneousComponent w n F ∈ I ⊔ Ideal.span {X i} := by
  intro F hF n
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hF
  rw [map_add]
  refine Submodule.add_mem_sup (hI a ha n) ?_
  rw [← Set.image_singleton] at hb ⊢
  exact component_mem_span_X w _ n hb

theorem finrank_sup_add_finrank_colonX {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ n, weightedHomogeneousComponent w n F ∈ I) (i : σ) (n : M)
    [Module.Finite K (weightedHomogeneousSubmodule K w (n + w i))]
    [Module.Finite K (weightedHomogeneousSubmodule K w n)] :
    Module.finrank K ↥(weightedHomogeneousSubmodule K w (n + w i) ⊓
        (I ⊔ Ideal.span {X i}).restrictScalars K) +
      Module.finrank K ↥(weightedHomogeneousSubmodule K w n ⊓ (colonX I i).restrictScalars K) =
    Module.finrank K ↥(weightedHomogeneousSubmodule K w (n + w i) ⊓ I.restrictScalars K) +
      Module.finrank K ↥(weightedHomogeneousSubmodule K w n) := by
  set μ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K := LinearMap.mulLeft K (X i) with hμ
  have hinj : Function.Injective μ := fun a b h => mul_left_cancel₀ (X_ne_zero i) h
  have hmul : ∀ G ∈ weightedHomogeneousSubmodule K w n,
      X i * G ∈ weightedHomogeneousSubmodule K w (n + w i) := by
    intro G hG
    rw [add_comm]
    exact (isWeightedHomogeneous_X K w i).mul hG
  haveI : Module.Finite K ↥(weightedHomogeneousSubmodule K w (n + w i) ⊓ I.restrictScalars K) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (weightedHomogeneousSubmodule K w (n + w i) ⊓ I.restrictScalars K)
    ((weightedHomogeneousSubmodule K w n).map μ)
  have e1 : (weightedHomogeneousSubmodule K w (n + w i) ⊓ I.restrictScalars K) ⊔
      ((weightedHomogeneousSubmodule K w n).map μ) =
      weightedHomogeneousSubmodule K w (n + w i) ⊓ (I ⊔ Ideal.span {X i}).restrictScalars K := by
    apply le_antisymm
    · refine sup_le (fun F hF => ⟨hF.1, Ideal.mem_sup_left hF.2⟩) ?_
      rintro _ ⟨G, hG, rfl⟩
      exact ⟨hmul G hG, Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))⟩
    · rintro F ⟨hF, hF'⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1
        (show F ∈ I ⊔ Ideal.span {X i} from hF')
      obtain ⟨G, rfl⟩ := Ideal.mem_span_singleton.1 hb
      have hc := IsWeightedHomogeneous.weightedHomogeneousComponent_same hF
      rw [← hc, map_add, component_X_mul]
      exact Submodule.add_mem_sup ⟨weightedHomogeneousComponent_mem _ _ _, hI a ha _⟩
        ⟨_, weightedHomogeneousComponent_mem _ _ _, rfl⟩
  have e2 : (weightedHomogeneousSubmodule K w (n + w i) ⊓ I.restrictScalars K) ⊓
      ((weightedHomogeneousSubmodule K w n).map μ) =
      (weightedHomogeneousSubmodule K w n ⊓ (colonX I i).restrictScalars K).map μ := by
    apply le_antisymm
    · rintro _ ⟨⟨-, h2⟩, G, hG, rfl⟩
      exact ⟨G, ⟨hG, h2⟩, rfl⟩
    · rintro _ ⟨G, ⟨hG, h2⟩, rfl⟩
      exact ⟨⟨hmul G hG, h2⟩, G, hG, rfl⟩
  rw [e1, e2, ← (Submodule.equivMapOfInjective μ hinj _).finrank_eq,
    ← (Submodule.equivMapOfInjective μ hinj _).finrank_eq] at h
  exact h

end

section
variable {K σ : Type} [Field K] {r : ℕ} (col : σ → Fin r)

theorem weight_colour_apply (d : σ →₀ ℕ) (k : Fin r) :
    Finsupp.weight (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) d k =
      ∑ i ∈ d.support, if col i = k then d i else 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : col i = k
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem finite_colourPiece [Finite σ] (n : Fin r → ℕ) :
    Module.Finite K (weightedHomogeneousSubmodule K
      (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n) := by
  have hfin : {d : σ →₀ ℕ |
      Finsupp.weight (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) d = n}.Finite := by
    refine (Finsupp.finite_of_degree_le (σ := σ) (∑ k, n k)).subset fun d hd => ?_
    have hd' : Finsupp.weight (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) d = n := hd
    have : ∑ k, n k = d.degree := by
      rw [← hd']
      simp only [weight_colour_apply]
      rw [Finset.sum_comm]
      simp [Finsupp.degree_apply]
    exact this.ge
  have hle : weightedHomogeneousSubmodule K (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n ≤
      Submodule.span K ((fun d => (monomial d (1 : K) : MvPolynomial σ K)) '' {d : σ →₀ ℕ |
      Finsupp.weight (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) d = n}) := by
    intro F hF
    rw [F.as_sum]
    refine Submodule.sum_mem _ fun d hd => ?_
    have : monomial d (coeff d F) = coeff d F • (monomial d (1 : K) : MvPolynomial σ K) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, hF (mem_support_iff.1 hd), rfl⟩)
  haveI := FiniteDimensional.span_of_finite K
    (hfin.image (fun d => (monomial d (1 : K) : MvPolynomial σ K)))
  exact Submodule.finiteDimensional_of_le hle

theorem colourPiece_le {I : Ideal (MvPolynomial σ K)} (k : Fin r)
    (hk : ∀ i, col i = k → X i ∈ I) (n : Fin r → ℕ) (hn : 1 ≤ n k) :
    weightedHomogeneousSubmodule K (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n ≤
      I.restrictScalars K := by
  intro F hF
  have h1 : Ideal.span (X '' {i | col i = k} : Set (MvPolynomial σ K)) ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact hk i hi
  refine h1 ?_
  rw [mem_ideal_span_X_image]
  intro m hm
  have h2 := hF (mem_support_iff.1 hm)
  by_contra hcon
  push Not at hcon
  have h3 := weight_colour_apply col m k
  rw [h2, Finset.sum_eq_zero] at h3
  · omega
  · intro i _
    split_ifs with h
    · exact hcon i h
    · rfl

end

end GlobalTheory.MultiHilbert

namespace GlobalTheory.MultiHilbert

open MvPolynomial

noncomputable def hilbertFun {K σ : Type} [Field K] {r : ℕ} (col : σ → Fin r)
    (I : Ideal (MvPolynomial σ K)) (n : Fin r → ℕ) : ℚ :=
  ((Module.finrank K ↥(weightedHomogeneousSubmodule K
    (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n) : ℕ) : ℚ) -
  ((Module.finrank K ↥(weightedHomogeneousSubmodule K
    (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n ⊓ I.restrictScalars K) : ℕ) : ℚ)

theorem hilbertFun_add {K σ : Type} [Field K] [Finite σ] {r : ℕ} (col : σ → Fin r)
    {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ n : Fin r → ℕ, weightedHomogeneousComponent
      (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n F ∈ I) (i : σ) (n : Fin r → ℕ) :
    hilbertFun col I (n + Pi.single (col i) 1) =
      hilbertFun col (colonX I i) n +
        hilbertFun col (I ⊔ Ideal.span {X i}) (n + Pi.single (col i) 1) := by
  haveI := finite_colourPiece (K := K) col n
  haveI := finite_colourPiece (K := K) col (n + Pi.single (col i) 1)
  have h := finrank_sup_add_finrank_colonX (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) hI i n
  have h' := congrArg (Nat.cast : ℕ → ℚ) h
  rw [Nat.cast_add, Nat.cast_add] at h'
  unfold hilbertFun
  linarith

theorem eventuallyPoly_hilbertFun {K σ : Type} [Field K] [Finite σ] {r : ℕ} (col : σ → Fin r)
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ F ∈ I, ∀ n : Fin r → ℕ, weightedHomogeneousComponent
      (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n F ∈ I) :
    EventuallyPoly (hilbertFun col I) := by
  induction I using IsNoetherian.induction with
  | hgt I ih =>
    by_cases h0 : ∃ k, ∀ i, col i = k → X i ∈ I
    · obtain ⟨k, hk⟩ := h0
      refine ⟨0, 1, fun n hn => ?_⟩
      unfold hilbertFun
      rw [inf_eq_left.2 (colourPiece_le col k hk n (hn k))]
      simp
    push Not at h0
    have hsup : ∀ i, X i ∉ I → EventuallyPoly (hilbertFun col (I ⊔ Ideal.span {X i})) := by
      intro i hi
      refine ih _ (lt_of_le_of_ne le_sup_left fun h => hi ?_) (component_mem_sup _ hI i)
      rw [h]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    by_cases h1 : ∃ i, X i ∉ I ∧ colonX I i ≠ I
    · obtain ⟨i, hi, hne⟩ := h1
      have h2 := ih _ (lt_of_le_of_ne (le_colonX I i) hne.symm) (component_mem_colonX _ hI i)
      refine EventuallyPoly.of_shift_add (Pi.single (col i) 1) ?_
      simp only [hilbertFun_add col hI i]
      exact h2.add ((hsup i hi).shift_add _)
    push Not at h1
    refine EventuallyPoly.of_differences fun k => ?_
    obtain ⟨i, rfl, hi⟩ := h0 k
    simp only [hilbertFun_add col hI i, h1 i hi, add_sub_cancel_left]
    exact (hsup i hi).shift_add _

end GlobalTheory.MultiHilbert

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.exists_multigraded_hilbertPoly : ∀ (K σ : Type) [Field K] [Finite σ] (r : ℕ) (col : σ → Fin r) (I : Ideal (MvPolynomial σ K)), (∀ F ∈ I, ∀ n : Fin r → ℕ, MvPolynomial.weightedHomogeneousComponent (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n F ∈ I) → ∃ (Φ : MvPolynomial (Fin r) ℚ) (n₀ : ℕ), ∀ n : Fin r → ℕ, (∀ k, n₀ ≤ n k) → ((Module.finrank K ↥(MvPolynomial.weightedHomogeneousSubmodule K (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n) : ℕ) : ℚ) - ((Module.finrank K ↥(MvPolynomial.weightedHomogeneousSubmodule K (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n ⊓ I.restrictScalars K) : ℕ) : ℚ) = MvPolynomial.eval (fun k => (n k : ℚ)) Φ :=
  fun _ _ _ _ _ col I hI => GlobalTheory.MultiHilbert.eventuallyPoly_hilbertFun col I hI

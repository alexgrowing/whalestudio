import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section SlopeTestRemainingChoices

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem cycEval_eq_add_mul_of_cycle (φ : Ideal (MRing ι R) → ℤ) {Z₀ Z₁ Z₂ : Ideal (MRing ι R) → ℤ}
    (k : ℤ) (h₀ : (Function.support Z₀).Finite) (h₂ : (Function.support Z₂).Finite)
    (h : ∀ W, Z₁ W = Z₀ W + k * Z₂ W) :
    cycEval φ Z₁ = cycEval φ Z₀ + k * cycEval φ Z₂ := by
  unfold cycEval
  have f₀ : (Function.support fun W => Z₀ W * φ W).Finite :=
    h₀.subset fun W hW h0 => hW (by simp [h0])
  have f₂ : (Function.support fun W => k * (Z₂ W * φ W)).Finite :=
    h₂.subset fun W hW h0 => hW (by simp [h0])
  rw [mul_finsum, ← finsum_add_distrib f₀ f₂]
  refine finsum_congr fun W => ?_
  rw [h W]
  ring

theorem cycEval_eq_add_mul_of_fun {φ₀ φ₁ φ₂ : Ideal (MRing ι R) → ℤ} {Z : Ideal (MRing ι R) → ℤ}
    (k : ℤ) (hZ : (Function.support Z).Finite) (h : ∀ W, Z W ≠ 0 → φ₁ W = φ₀ W + k * φ₂ W) :
    cycEval φ₁ Z = cycEval φ₀ Z + k * cycEval φ₂ Z := by
  unfold cycEval
  have f₀ : (Function.support fun W => Z W * φ₀ W).Finite :=
    hZ.subset fun W hW h0 => hW (by simp [h0])
  have f₂ : (Function.support fun W => k * (Z W * φ₂ W)).Finite :=
    hZ.subset fun W hW h0 => hW (by simp [h0])
  rw [mul_finsum, ← finsum_add_distrib f₀ f₂]
  refine finsum_congr fun W => ?_
  by_cases hW : Z W = 0
  · simp [hW]
  · rw [h W hW]
    ring

end SlopeTestRemainingChoices

section VNum

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem vNum_vecCons_zero (W : Ideal (MRing ι O)) {d : ℕ} (L : Fin d → K → ℤ) :
    vNum W (Matrix.vecCons (0 : K → ℤ) L) = 0 := by
  unfold vNum intNum
  have hm : mixedDiff (Matrix.vecCons (0 : K → ℤ) L) (hilbFn (specialIdeal W)) = fun _ => 0 := by
    funext m
    simp [mixedDiff, List.ofFn_succ, diffStep]
  rw [hm]
  unfold eventualValue
  have hex : ∃ c, ∀ᶠ m in Filter.atTop, (fun _ : K → ℤ => (0 : ℤ)) m = c :=
    ⟨0, Filter.Eventually.of_forall fun _ => rfl⟩
  rw [dif_pos hex]
  obtain ⟨m, hm'⟩ := hex.choose_spec.exists
  exact hm'.symm

end VNum

theorem ShiftByUniformiser.proof (h₁ : DivCycleMul.Statement.{u})
    (h₂ : DivCycleFiniteSupport.Statement.{u}) : ShiftByUniformiser.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s _ hsP hH L n hI₁ hI₂
  have hfin : ∀ (Q : Ideal (MRing ι O)) (x : MRing ι O), (Function.support (divCycle Q x)).Finite :=
    fun Q x => h₂ O K ι Q x
  have hrat : ∀ (Q : Ideal (MRing ι O)) (x y : MRing ι O), (Function.support (ratDiv Q x y)).Finite :=
    fun Q x y => ((hfin Q x).union (hfin Q y)).subset fun W hW => by
      by_contra hc
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
      exact hW (by simp [ratDiv, hc.1, hc.2])

  have hpow : ∀ (Q : Ideal (MRing ι O)), Q.IsPrime → (C ϖ : MRing ι O) ∉ Q → f ∉ Q → ∀ m : ℕ,
      ∀ W, divCycle Q (C ϖ ^ m * f) W = divCycle Q f W + m * divCycle Q (C ϖ) W := by
    intro Q hQ hϖQ hfQ m
    induction m with
    | zero => intro W; simp
    | succ m ih =>
      intro W
      have hm : C ϖ ^ m * f ∉ Q := fun h =>
        (hQ.mem_or_mem h).elim (fun h' => hϖQ (hQ.mem_of_pow_mem _ h')) hfQ
      have e : (C ϖ : MRing ι O) ^ (m + 1) * f = C ϖ * (C ϖ ^ m * f) := by ring
      rw [e, congrFun (h₁ O K ι Q (C ϖ) (C ϖ ^ m * f) hQ hϖQ hm) W, Pi.add_apply, ih W]
      push_cast
      ring
  have hshift : ∀ (Q : Ideal (MRing ι O)), Q.IsPrime → (C ϖ : MRing ι O) ∉ Q → f ∉ Q → ∀ W,
      ratDiv Q (C ϖ ^ n * f) g W = ratDiv Q f g W + (n : ℤ) * ratDiv Q (C ϖ) 1 W := by
    intro Q hQ hϖQ hfQ W
    simp only [ratDiv, divCycle_one, sub_zero]
    rw [hpow Q hQ hϖQ hfQ n W]
    ring
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'
  unfold cutIdentity at hI₁ hI₂ ⊢
  rw [cycEval_eq_add_mul_of_cycle _ (n : ℤ) (hrat P f g) (hrat P (C ϖ) 1)
      (hshift P hPp hϖP hD.num_not_mem)] at hI₁
  classical
  have hR : cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
        else cycEval (fun G => vNum G L) (ratDiv W (C ϖ ^ n * f) g)) (divCycle P s) =
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
        else cycEval (fun G => vNum G L) (ratDiv W f g)) (divCycle P s) +
      (n : ℤ) * cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons (0 : K → ℤ) L)
        else cycEval (fun G => vNum G L) (ratDiv W (C ϖ) 1)) (divCycle P s) := by
    refine cycEval_eq_add_mul_of_fun (n : ℤ) (hfin P s) fun W hW => ?_
    by_cases hϖW : (C ϖ : MRing ι O) ∈ W
    · simp only [if_pos hϖW, vNum_vecCons_zero]
      ring
    · simp only [if_neg hϖW]
      have hV := hH W hW hϖW
      have hWp : W.IsPrime := by
        unfold divCycle at hW
        split_ifs at hW with hm
        · exact hm.1.1.1
        · exact absurd rfl hW
      exact cycEval_eq_add_mul_of_cycle _ (n : ℤ) (hrat W f g) (hrat W (C ϖ) 1)
        (hshift W hWp hϖW hV.num_not_mem)
  rw [hR, hI₂] at hI₁
  linarith

end

end GroundTheory.Heights₂.Heights.NumbersDVR

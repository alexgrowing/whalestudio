import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToMatrixRepOf
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem intertwine_mul {G ι R S : Type} [Monoid G] [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (B : G → Matrix ι ι S) (hB1 : B 1 = 1)
    (hBm : ∀ g h, B (g * h) = B g * B h) (p : GL ι S) (T : G → Matrix ι ι R)
    (hT : ∀ g, (p : Matrix ι ι S) * (T g).map f = B g * p) :
    T 1 = 1 ∧ ∀ g h, T (g * h) = T g * T h := by
  have hinj : Function.Injective (fun M : Matrix ι ι R => M.map f) := Matrix.map_injective hf
  refine ⟨?_, fun g h => ?_⟩
  · apply hinj
    apply (Units.mul_right_inj p).1
    show (p : Matrix ι ι S) * (T 1).map f = (p : Matrix ι ι S) * (1 : Matrix ι ι R).map f
    rw [hT, hB1, one_mul, Matrix.map_one f (map_zero f) (map_one f), mul_one]
  · apply hinj
    apply (Units.mul_right_inj p).1
    show (p : Matrix ι ι S) * (T (g * h)).map f = (p : Matrix ι ι S) * (T g * T h).map f
    calc (p : Matrix ι ι S) * (T (g * h)).map f = B g * B h * p := by rw [hT, hBm]
      _ = B g * ((p : Matrix ι ι S) * (T h).map f) := by rw [mul_assoc, hT]
      _ = ((p : Matrix ι ι S) * (T g).map f) * (T h).map f := by rw [← mul_assoc, hT]
      _ = (p : Matrix ι ι S) * (T g * T h).map f := by rw [Matrix.map_mul, mul_assoc]

theorem exists_ratForm : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (W : GL (Fin r) ↥(MaximalUnramifiedExtension l)), IsRat r σ →
    (∀ m k : Fin r, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k = fr l m (ω k)) → (∀ k, fr l r (ω k) = ω k) →
    (∀ (X : Type) [TopologicalSpace X] (x : X → ↥(MaximalUnramifiedExtension l)), (∀ t, fr l r (x t) = x t) →
      Continuous (fun t => ((x t : ↥(MaximalUnramifiedExtension l)) : Om l)) →
      ∃ a : X → Fin r → ℚ_[l], Continuous a ∧ ∀ t (m : Fin r),
        fr l m (x t) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a t k)) →
    ∃ (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)),
      (∀ i j, Continuous fun g => (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]) i j) ∧
      (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) ∧
      (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) ∧
      ∀ c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l), (∀ g i, fr l r (c g i) = c g i) →
        (∀ i, Continuous fun g => ((c g i : ↥(MaximalUnramifiedExtension l)) : Om l)) →
        ∃ c₀ : ↥(GK K) → n × Fin r → ℚ_[l], Continuous c₀ ∧ ∀ g,
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1) := by
  intro l _ n _ _ K r σ ω W hσ hW hω hcoef
  classical

  let P0 : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
    Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l))
  let Q0 : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
    Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) ((W⁻¹ : GL (Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l))
  have hPQ : P0 * Q0 = 1 := by
    simp only [P0, Q0]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_kronecker_one]
  have hQP : Q0 * P0 = 1 := by
    simp only [P0, Q0]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_kronecker_one]
  let p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l) := ⟨P0, Q0, hPQ, hQP⟩
  have hp : ∀ i m j k, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) (i, m) (j, k) =
      if i = j then (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k else 0 := by
    intro i m j k
    show P0 (i, m) (j, k) = _
    simp only [P0, Matrix.kronecker_apply, Matrix.one_apply]
    split_ifs <;> simp

  have hA : ∀ (i j : n) (k : Fin r), ∃ a : ↥(GK K) → Fin r → ℚ_[l], Continuous a ∧ ∀ g (m : Fin r),
      fr l m ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k) =
        ∑ k', (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k' * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a g k') := by
    intro i j k
    refine hcoef ↥(GK K) (fun g => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k) (fun g => ?_) ?_
    · rw [map_mul, hσ.rat, hω]
    · show Continuous fun g => (((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) * ((ω k : ↥(MaximalUnramifiedExtension l)) : Om l)
      exact (hσ.cont i j).mul continuous_const
  choose A hAc hA using hA
  let T : ↥(GK K) → Matrix (n × Fin r) (n × Fin r) ℚ_[l] := fun g x y => A x.1 y.1 y.2 g x.2
  let B : ↥(GK K) → Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := fun g =>
    Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))
  have hB1 : B 1 = 1 := by
    simp only [B, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.blockDiagonal_one
  have hBm : ∀ g h, B (g * h) = B g * B h := by
    intro g h
    simp only [B, map_mul, Units.val_mul, Matrix.map_mul]
    rw [Matrix.blockDiagonal_mul]
  have hT : ∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * (T g).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
      B g * p := by
    intro g
    refine Matrix.ext ?_
    rintro ⟨i, m⟩ ⟨j, k⟩
    rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [hp, B, T, Matrix.map_apply, Matrix.blockDiagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Fintype.sum_eq_single i (fun x hx => by simp [Ne.symm hx])]
    simp only [if_true]
    refine (show _ = ∑ x, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m x * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (A i j k g x)
      from rfl).trans ?_
    rw [← hA i j k g m, map_mul]
    symm
    simp [hW]
  obtain ⟨hT1, hTm⟩ := intertwine_mul (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)).injective
    B hB1 hBm p T hT
  let T' : ↥(GK K) →* Matrix (n × Fin r) (n × Fin r) ℚ_[l] :=
    { toFun := T, map_one' := hT1, map_mul' := hTm }
  refine ⟨T'.toHomUnits, p, ?_, ?_, ?_, ?_⟩
  · rintro ⟨i, k'⟩ ⟨j, k⟩
    exact (continuous_apply k').comp (hAc i j k)
  · rintro ⟨i, m⟩ ⟨j, k⟩
    apply hσ.le
    rw [hp]
    split_ifs
    · rw [hW]; exact fr_comm (hω k) m
    · exact map_zero _
  · intro g
    exact hT g
  · intro c hc hcc
    have hC : ∀ i : n, ∃ a : ↥(GK K) → Fin r → ℚ_[l], Continuous a ∧ ∀ g (m : Fin r),
        fr l m (c g i) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a g k) :=
      fun i => hcoef ↥(GK K) (fun g => c g i) (fun g => hc g i) (hcc i)
    choose a hac ha using hC
    refine ⟨fun g x => a x.1 g x.2, continuous_pi fun x => (continuous_apply x.2).comp (hac x.1), fun g => ?_⟩
    funext ⟨i, m⟩
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    simp only [hp, ite_mul, zero_mul]
    rw [Fintype.sum_eq_single i (fun x hx => by simp [Ne.symm hx])]
    simp only [if_true]
    rw [ha i g m]

end GlobalTheory.PMon

end

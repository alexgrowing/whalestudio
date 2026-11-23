import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.RealPlaceAnalysis.StatementU

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Jet

def IsDer {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) : Prop :=
  GlRel E ∧ IsUnitary ε E ∧
    (∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∀ v : V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) ((∑ a, ∑ b, X a b • E a b v : V) : H) 0) ∧
    ∀ (v : V) (y : H), SmoothOnG ε (fun g => ⟪y, σ g (v : H)⟫_ℂ)

def at1 {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (G : Arr V n 1) (a b : Fin n) : V :=
  arrOf V n 1 G (fun _ => (a, b))

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem isDer_trivial {n : ℕ} (ε : Fin n → Bool) :
    IsDer ε (fun _ : Matrix (Fin n) (Fin n) ℂ => ContinuousLinearMap.id ℂ ℂ) ⊤ (fun _ _ => 0) := by
  unfold IsDer
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c d
    simp
  · intro a b x y
    simp
  · intro X _ w
    simpa using hasDerivAt_const (0 : ℝ) (w : ℂ)
  · intro v y g₀ _
    exact ⟨Set.univ, fun _ => ⟪y, (v : ℂ)⟫_ℂ, isOpen_univ, Set.mem_univ _, contDiffOn_const,
      fun _ _ _ => rfl⟩

namespace StdDer

def act {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :=
  (stdRep y).toLinearMap.restrict (fun _ _ => Submodule.mem_top)

theorem act_coe {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (v : (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin n)))) :
    (act y v : EuclideanSpace ℂ (Fin n)) = stdRep y v := rfl

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem isDer (n : ℕ) :
    IsDer (allPos n) stdRep ⊤ (fun a b => act (Matrix.single a b 1)) := by
  have hmul : ∀ x y : Matrix (Fin n) (Fin n) ℂ, act x * act y = act (x * y) := by
    intro x y
    ext w : 1
    apply Subtype.ext
    simp [act_coe, stdRep, map_mul]
  have hsub : ∀ x y : Matrix (Fin n) (Fin n) ℂ, act x - act y = act (x - y) := by
    intro x y
    ext w : 1
    apply Subtype.ext
    simp [act_coe, stdRep, map_sub]
  have hzero : act (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
    ext w : 1
    apply Subtype.ext
    simp [act_coe, stdRep]
  unfold IsDer
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c d
    have key : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
        (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
      by_cases hbc : b = c <;> by_cases hda : d = a
      · subst hbc hda
        simp
      · subst hbc
        simp [hda]
      · subst hda
        simp [hbc]
      · simp [hbc, hda]
    rw [hmul, hmul, hsub, key, ← hsub]
    split_ifs <;> simp [hzero]
  · intro a b x y
    have hs : sgn (allPos n) a b = 1 := by simp [sgn, allPos]
    have hadj : ContinuousLinearMap.adjoint (stdRep (Matrix.single a b (1 : ℂ))) = stdRep (Matrix.single b a 1) := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      simp [stdRep, ← map_star, Matrix.star_eq_conjTranspose]
    rw [hs, Submodule.coe_inner, Submodule.coe_inner, act_coe, act_coe, ← hadj,
      ContinuousLinearMap.adjoint_inner_right]
    simp
  · intro X _ w
    have hX : X = ∑ a, ∑ b, X a b • Matrix.single a b (1 : ℂ) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      simp [Matrix.smul_single]
    have hsum : ((∑ a, ∑ b, X a b • act (Matrix.single a b (1 : ℂ)) w : (⊤ : Submodule ℂ _)) :
        EuclideanSpace ℂ (Fin n)) = stdRep X w := by
      rw [Submodule.coe_sum]
      conv_rhs => rw [hX, stdRep, map_sum, _root_.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Submodule.coe_sum, map_sum, _root_.sum_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Submodule.coe_smul, act_coe, map_smul, _root_.smul_apply, stdRep]
    have hfun : (fun t : ℝ => stdRep (NormedSpace.exp ((t : ℂ) • X)) (w : EuclideanSpace ℂ (Fin n))) =
        fun t : ℝ => NormedSpace.exp ((t : ℂ) • stdRep X) (w : EuclideanSpace ℂ (Fin n)) := by
      funext t
      simp only [stdRep]
      have key : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (NormedSpace.exp ((t : ℂ) • X)) =
          NormedSpace.exp (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) ((t : ℂ) • X)) := by
        rw [NormedSpace.exp_eq_tsum ℂ, NormedSpace.exp_eq_tsum ℂ]
        exact ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.map_tsum).trans
          (tsum_congr fun k => by
            change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) _ = _
            rw [map_smul, map_pow])
      rw [key, map_smul]
    have h1 : HasDerivAt (fun u : ℂ => NormedSpace.exp (u • stdRep X))
        (NormedSpace.exp ((0 : ℂ) • stdRep X) * stdRep X) 0 := hasDerivAt_exp_smul_const _ _
    have h2 : HasDerivAt (fun u : ℂ => NormedSpace.exp (u • stdRep X) (w : EuclideanSpace ℂ (Fin n)))
        (stdRep X w) ((0 : ℝ) : ℂ) := by
      simpa using h1.clm_apply (hasDerivAt_const (0 : ℂ) (w : EuclideanSpace ℂ (Fin n)))
    have h3 := h2.scomp (0 : ℝ) Complex.ofRealCLM.hasDerivAt
    simp only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul] at h3
    rw [hsum, hfun]
    exact h3
  · intro v y g₀ _
    refine ⟨Set.univ, fun g => ⟪y, stdRep g (v : EuclideanSpace ℂ (Fin n))⟫_ℂ, isOpen_univ, Set.mem_univ _, ?_,
      fun _ _ _ => rfl⟩
    have hF : (fun g : Matrix (Fin n) (Fin n) ℂ => ⟪y, stdRep g (v : EuclideanSpace ℂ (Fin n))⟫_ℂ) =
        fun g => ∑ i, (starRingEnd ℂ) (y i) * ∑ j, g i j * (v : EuclideanSpace ℂ (Fin n)) j := by
      funext g
      simp [PiLp.inner_apply, stdRep_apply, mul_comm]
    rw [hF]
    apply ContDiff.contDiffOn
    exact ContDiff.sum fun i _ => contDiff_const.mul
      (ContDiff.sum fun j _ => (contDiff_apply_apply ℝ ℂ i j).mul contDiff_const)

example {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (f : Fin n → Fin n → V) (a b : Fin n) :
    at1 (arrTo V n 1 (fun α => f (α 0).1 (α 0).2)) a b = f a b := rfl

end StdDer

end GlobalTheory.Jet

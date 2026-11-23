import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TriFrame

open GlobalTheory.Twist (resM_resM resM_smul)

theorem isFrame_gl_smul {X : Scheme.{0}} {V : X.Opens} {F : X.Modules} {r : ℕ} {e : Fin r → Γ(F, V)} (he : IsFrame e)
    (P : GL (Fin r) Γ(X, V)) :
    IsFrame fun l => ∑ m, (P : Matrix (Fin r) (Fin r) Γ(X, V)) l m • e m := by
  intro T hT
  let Q : GL (Fin r) Γ(X, T) := Matrix.GeneralLinearGroup.map (resG X hT) P
  have hQ : Function.Bijective (Matrix.vecMulLinear (Q : Matrix (Fin r) (Fin r) Γ(X, T))) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun a => Matrix.vecMul a ((Q⁻¹ : GL _ _) : Matrix _ _ _), fun a => ?_, fun a => ?_⟩
    · simp [Matrix.vecMul_vecMul]
    · simp [Matrix.vecMul_vecMul]
  have h2 := (he T hT).comp hQ
  convert h2 using 1
  funext a
  simp only [Function.comp_apply, Fintype.linearCombination_apply, map_sum, resM_smul, Matrix.vecMulLinear_apply,
    Matrix.vecMul, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  rfl

theorem exists_isTri_of_gl : ∀ (X : Scheme.{0}) (A V V' : X.Opens) (h : V' ≤ V) (F : X.Modules) (r : ℕ) (s : Fin r → Γ(F, A)) (hs : IsFrame s) (e : Fin r → Γ(F, V)) (he : IsFrame e) (P : GL (Fin r) Γ(X, V')) (ρ : Fin r → Γ(X, V' ⊓ A)), (∀ l j, j < l → ((P : Matrix (Fin r) (Fin r) Γ(X, V')).map (resG X (inf_le_left : V' ⊓ A ≤ V')) * (Matrix.of fun l j => GlobalTheory.ChainPts.coef true he hs l (Fin.rev j)).map (resG X (inf_le_inf_right A h))) l j = 0) → (∀ j, ((P : Matrix (Fin r) (Fin r) Γ(X, V')).map (resG X (inf_le_left : V' ⊓ A ≤ V')) * (Matrix.of fun l j => GlobalTheory.ChainPts.coef true he hs l (Fin.rev j)).map (resG X (inf_le_inf_right A h))) j j * ρ j = 1) → ∃ e' : Fin r → Γ(F, V'), IsFrame e' ∧ IsTri hs e' ∧ ∀ i, coordIn hs e' i i * ρ (Fin.rev i) = 1 := by
  intro X A V V' h F r s hs e he P ρ h0 h1
  have key (l i : Fin r) : coordIn hs (fun l => ∑ m, (P : Matrix (Fin r) (Fin r) Γ(X, V')) (Fin.rev l) m • resM F h (e m)) l i =
      ((P : Matrix (Fin r) (Fin r) Γ(X, V')).map (resG X (inf_le_left : V' ⊓ A ≤ V')) * (Matrix.of fun l j => GlobalTheory.ChainPts.coef true he hs l (Fin.rev j)).map (resG X (inf_le_inf_right A h))) (Fin.rev l) (Fin.rev i) := by
    simp only [coordIn, map_sum, resM_smul, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Fin.rev_rev]
    refine Finset.sum_congr rfl fun m _ => congrArg _ ?_
    have := hs.repr_resM (inf_le_right : V ⊓ A ≤ A) (inf_le_inf_right A h) (resM F inf_le_left (e m)) i
    rw [resM_resM] at this ⊢
    exact this
  refine ⟨_, (isFrame_gl_smul (he.res h) P).comp_equiv Fin.revPerm, fun i l hil => ?_, fun i => ?_⟩
  · exact (key i l).trans (h0 _ _ (Fin.rev_lt_rev.2 hil))
  · exact (congrArg (· * _) (key i i)).trans (h1 _)

end GlobalTheory.TriFrame

end

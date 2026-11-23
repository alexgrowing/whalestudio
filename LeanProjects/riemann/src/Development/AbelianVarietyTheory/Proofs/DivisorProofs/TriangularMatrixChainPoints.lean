import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.TriFrame

theorem tri_of_mul_eq_one {R : Type} [CommRing R] {r : ℕ} (U N : Matrix (Fin r) (Fin r) R) (ρ : Fin r → R)
    (hUN : U * N = 1) (hU : ∀ l j, j < l → U l j = 0) (hρ : ∀ j, U j j * ρ j = 1) :
    (∀ i l, i < l → N l i = 0) ∧ ∀ i, N i i = ρ i := by
  have hb : U.BlockTriangular id := fun l j h => hU l j h
  letI : Invertible U := invertibleOfRightInverse U N hUN
  have hN : N.BlockTriangular id := by
    have := Matrix.blockTriangular_inv_of_blockTriangular hb
    rwa [Matrix.inv_eq_right_inv hUN] at this
  refine ⟨fun i l h => hN h, fun i => ?_⟩
  have h1 := congrFun (congrFun hUN i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at h1
  · calc N i i = N i i * (U i i * ρ i) := by rw [hρ, mul_one]
      _ = U i i * N i i * ρ i := by ring
      _ = ρ i := by rw [h1, one_mul]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hU i k h, zero_mul]
    · rw [hN h, mul_zero]
  · simp

theorem isFrame_sum_smul {X : Scheme.{0}} {F : X.Modules} {V : X.Opens} {m : ℕ} {e : Fin m → Γ(F, V)}
    (he : IsFrame e) (M : Matrix (Fin m) (Fin m) Γ(X, V)) (hM : IsUnit M) :
    IsFrame fun j => ∑ l, M l j • e l := fun W h => by
  have hM' : IsUnit (M.map (resG X h)) := hM.map (resG X h).mapMatrix
  have hb : Function.Bijective (M.map (resG X h)).mulVec :=
    ⟨Matrix.mulVec_injective_of_isUnit hM', Matrix.mulVec_surjective_iff_isUnit.2 hM'⟩
  have key : ⇑(Fintype.linearCombination Γ(X, W) fun j => resM F h (∑ l, M l j • e l)) =
      ⇑(Fintype.linearCombination Γ(X, W) fun i => resM F h (e i)) ∘ (M.map (resG X h)).mulVec := by
    funext a
    simp only [Function.comp_apply, Fintype.linearCombination_apply, map_sum, GlobalTheory.Twist.resM_smul,
      Finset.smul_sum, Matrix.mulVec, dotProduct, Finset.sum_smul, Matrix.map_apply, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [key]
  exact (he W h).comp hb

theorem exists_isTri_of_mul_coef : ∀ (X : Scheme.{0}) (A V V' : X.Opens) (h : V' ≤ V) (F : X.Modules) (r : ℕ) (s : Fin r → Γ(F, A)) (hs : IsFrame s) (e : Fin r → Γ(F, V)) (he : IsFrame e) (P : GL (Fin r) Γ(X, V')) (ρ : Fin r → Γ(X, V' ⊓ A)), (∀ l j, j < l → ((P : Matrix (Fin r) (Fin r) Γ(X, V')).map (resG X (inf_le_left : V' ⊓ A ≤ V')) * (Matrix.of (GlobalTheory.ChainPts.coef false he hs)).map (resG X (inf_le_inf_right A h))) l j = 0) → (∀ j, ((P : Matrix (Fin r) (Fin r) Γ(X, V')).map (resG X (inf_le_left : V' ⊓ A ≤ V')) * (Matrix.of (GlobalTheory.ChainPts.coef false he hs)).map (resG X (inf_le_inf_right A h))) j j * ρ j = 1) → ∃ e' : Fin r → Γ(F, V'), IsFrame e' ∧ IsTri hs e' ∧ ∀ i, coordIn hs e' i i = ρ i := by
  intro X A V V' h F r s hs e he P ρ hU hρ
  let Q : Matrix (Fin r) (Fin r) Γ(X, V') := ((P⁻¹ : GL (Fin r) Γ(X, V')) : Matrix (Fin r) (Fin r) Γ(X, V'))
  let e' : Fin r → Γ(F, V') := fun j => ∑ l, Q l j • resM F h (e l)
  have hVA : V' ⊓ A ≤ V := inf_le_left.trans h
  let be := he.basis hVA
  let bs := hs.basis (inf_le_right : V' ⊓ A ≤ A)
  let N : Matrix (Fin r) (Fin r) Γ(X, V' ⊓ A) := bs.toMatrix fun i => resM F inf_le_left (e' i)
  have hM : (Matrix.of (GlobalTheory.ChainPts.coef false he hs)).map (resG X (inf_le_inf_right A h)) = be.toMatrix bs := by
    ext l j : 1
    rw [Matrix.map_apply, Matrix.of_apply, Module.Basis.toMatrix_apply, GlobalTheory.ChainPts.coef,
      ← he.repr_resM inf_le_left (inf_le_inf_right A h), GlobalTheory.Twist.resM_resM, hs.basis_apply]
  have hQ : be.toMatrix (fun i => resM F inf_le_left (e' i)) = Q.map (resG X (inf_le_left : V' ⊓ A ≤ V')) := by
    ext l j : 1
    rw [Matrix.map_apply, Module.Basis.toMatrix_apply]
    simp only [e', map_sum (resM F _), GlobalTheory.Twist.resM_smul, GlobalTheory.Twist.resM_resM]
    simp only [← he.basis_apply hVA]
    rw [Module.Basis.repr_sum_self]
  have hUN : ((P : Matrix (Fin r) (Fin r) Γ(X, V')).map (resG X (inf_le_left : V' ⊓ A ≤ V')) *
      (Matrix.of (GlobalTheory.ChainPts.coef false he hs)).map (resG X (inf_le_inf_right A h))) * N = 1 := by
    rw [hM, Matrix.mul_assoc, Module.Basis.toMatrix_mul_toMatrix, hQ, ← Matrix.map_mul, Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨h₁, h₂⟩ := tri_of_mul_eq_one _ N ρ hUN hU hρ
  exact ⟨e', isFrame_sum_smul (he.res h) Q (Units.isUnit _), h₁, h₂⟩

end GlobalTheory.TriFrame

end

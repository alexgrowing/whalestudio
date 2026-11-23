import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LangXRoot

noncomputable section

namespace GlobalTheory.PMonE

open Polynomial

theorem langCount_card_fixed (F : Type) [Field F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (e : ℕ) (he : 0 < e) : Nat.card {c : F // c ^ p ^ e = c} = p ^ e := by
  have hq : 1 < p ^ e := Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt
  have hsep : (X ^ p ^ e - X : F[X]).Separable := galois_poly_separable p (p ^ e) (dvd_pow_self p he.ne')
  have hdeg : (X ^ p ^ e - X : F[X]).natDegree = p ^ e := FiniteField.X_pow_card_sub_X_natDegree_eq F hq
  have hne : (X ^ p ^ e - X : F[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F hq
  have hcard := Polynomial.card_rootSet_eq_natDegree (K := F) hsep (IsAlgClosed.splits_domain _)
  rw [hdeg] at hcard
  have h2 : Nat.card ((X ^ p ^ e - X : F[X]).rootSet F) = p ^ e := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)).trans h2
  rw [Polynomial.mem_rootSet_of_ne hne]
  simp [sub_eq_zero]

theorem langCount_integral {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (q : ℕ) (hq : 1 < q) (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (x : m → F)
    (hx : ∀ i, x i ^ q = A.mulVec x i) : Integral x := by
  by_contra hcon
  simp only [Integral, not_forall, not_le] at hcon
  obtain ⟨i₀, hi₀⟩ := hcon
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖x j‖) ⟨i₀, Finset.mem_univ _⟩
  have hgt : 1 < ‖x i‖ := lt_of_lt_of_le hi₀ (hi i₀ (Finset.mem_univ _))
  have hle : ‖x i‖ ^ q ≤ ‖x i‖ := by
    rw [← norm_pow, hx i]
    simp only [Matrix.mulVec, dotProduct]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    intro j _
    rw [norm_mul]
    calc ‖A i j‖ * ‖x j‖ ≤ 1 * ‖x i‖ :=
          mul_le_mul (hA i j) (hi j (Finset.mem_univ _)) (norm_nonneg _) zero_le_one
      _ = ‖x i‖ := one_mul _
  have hlt : ‖x i‖ < ‖x i‖ ^ q := lt_self_pow₀ hgt hq
  linarith

theorem langCount_card_semilinear (F : Type) [Field F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (e : ℕ) (he : 0 < e) {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Φ : V →+ V)
    (hΦ : ∀ (a : F) (v : V), Φ (a • v) = a ^ p ^ e • Φ v) (hinj : Function.Injective Φ) :
    Nat.card {v : V // Φ v = v} = (p ^ e) ^ Module.finrank F V := by
  have hq : 1 < p ^ e := Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt
  obtain ⟨b, hb⟩ := LangIsogenyConstruction.lang_basis (p ^ e) hq Φ hΦ hinj
  have hkey : ∀ v, b.equivFun (Φ v) = fun i => b.equivFun v i ^ p ^ e := by
    intro v
    have hv : Φ v = b.equivFun.symm (fun i => b.equivFun v i ^ p ^ e) := by
      conv_lhs => rw [← b.sum_equivFun v]
      rw [map_sum, Module.Basis.equivFun_symm_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hΦ, hb]
    rw [hv, LinearEquiv.apply_symm_apply]
  have e1 : {v : V // Φ v = v} ≃
      {c : Fin (Module.finrank F V) → F // ∀ i, c i ^ p ^ e = c i} :=
    b.equivFun.toEquiv.subtypeEquiv fun v => by
      constructor
      · intro h i
        have := congrFun (hkey v) i
        rw [h] at this
        exact this.symm
      · intro h
        apply b.equivFun.injective
        rw [hkey v]
        funext i
        exact h i
  rw [Nat.card_congr (e1.trans (Equiv.subtypePiEquivPi (p := fun _ c => c ^ p ^ e = c))), Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _),
    Fintype.card_fin, langCount_card_fixed F p e he]

theorem langCount : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ)
    [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e →
    ∀ A : Matrix m m F, (∀ i j, ‖A i j‖ ≤ 1) → A.det ≠ 0 →
    (∀ x : m → F, (∀ i, x i ^ p ^ e = A.mulVec x i) → Integral x) ∧
    Nat.card {x : m → F // ∀ i, x i ^ p ^ e = A.mulVec x i} = (p ^ e) ^ Fintype.card m := by
  intro F _ _ _ p _ _ m _ _ e he A hA hdet
  have hq : 1 < p ^ e := Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt
  refine ⟨fun x hx => langCount_integral (p ^ e) hq A hA x hx, ?_⟩
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  let Φ : (m → F) →+ (m → F) := AddMonoidHom.mk' (fun x => A⁻¹.mulVec (fun i => x i ^ p ^ e)) (by
    intro a b
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp only [Pi.add_apply]
    rw [add_pow_char_pow])
  have hΦ : ∀ (c : F) (v : m → F), Φ (c • v) = c ^ p ^ e • Φ v := by
    intro c v
    show A⁻¹.mulVec (fun i => (c • v) i ^ p ^ e) = c ^ p ^ e • A⁻¹.mulVec (fun i => v i ^ p ^ e)
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp [mul_pow]
  have hfix : ∀ x : m → F, Φ x = x ↔ ∀ i, x i ^ p ^ e = A.mulVec x i := by
    intro x
    change A⁻¹.mulVec (fun i => x i ^ p ^ e) = x ↔ _
    constructor
    · intro h i
      have h2 := congrArg A.mulVec h
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hu, Matrix.one_mulVec] at h2
      exact congrFun h2 i
    · intro h
      have h2 : (fun i => x i ^ p ^ e) = A.mulVec x := funext h
      rw [h2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hu, Matrix.one_mulVec]
  have hinj : Function.Injective Φ := by
    intro x y hxy
    change A⁻¹.mulVec (fun i => x i ^ p ^ e) = A⁻¹.mulVec (fun i => y i ^ p ^ e) at hxy
    have h2 := congrArg A.mulVec hxy
    simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hu, Matrix.one_mulVec] at h2
    funext i
    have h3 := congrFun h2 i
    rw [← iterateFrobenius_def, ← iterateFrobenius_def] at h3
    exact (iterateFrobenius F p e).injective h3
  have hc := langCount_card_semilinear F p e he Φ hΦ hinj
  rw [Module.finrank_fintype_fun_eq_card] at hc
  rw [← hc]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => (hfix x).symm)

end GlobalTheory.PMonE

end

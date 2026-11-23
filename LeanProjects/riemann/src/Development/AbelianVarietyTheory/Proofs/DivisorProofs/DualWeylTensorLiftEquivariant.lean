import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead.LiftEquiv

theorem map_rowAct_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (M : Matrix (Fin r) (Fin r) R) (f : MvPolynomial (Fin r × Fin n) R) :
    MvPolynomial.map φ (rowAct R M f) = rowAct S (M.map φ) (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp, map_X]
    congr 1
    simp [rowAct, map_sum, Matrix.map_apply]

theorem rowAct_detPol_eq {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    rowAct R M (detPol R n) = MvPolynomial.C M.det * detPol R n := by
  unfold detPol
  rw [AlgHom.map_det, RingHom.map_det (MvPolynomial.C : R →+* MvPolynomial (Fin n × Fin n) R), ← Matrix.det_mul]
  congr 1
  ext1 a s
  simp [rowAct, Matrix.mul_apply]

theorem rowAct_liftPol_eq {K C : Type} [CommRing K] [CommRing C] {n : ℕ} (e0 : K →+* C) (k : ℕ)
    (M : Matrix (Fin n) (Fin n) K) (f : MvPolynomial (Fin n × Fin n) K) :
    rowAct C (M.map e0) (liftPol e0 k f) = (e0 M.det) ^ k • liftPol e0 k (rowAct K M f) := by
  unfold liftPol
  have hd : (M.map e0).det = e0 M.det := (RingHom.map_det e0 M).symm
  rw [map_mul, map_pow, rowAct_detPol_eq, map_rowAct_eq, mul_pow, smul_eq_C_mul, map_pow, mul_assoc, hd]

theorem grp_tprod_eq (C : Type) [CommRing C] {ι : Type} (n : ℕ) (lamW : ι → ℕ → ℕ) (g : ι → GL (Fin n) C)
    (y : ∀ τ, dualWeyl C n n (res n (lamW τ))) :
    grp C n lamW g (PiTensorProduct.tprod C y) =
      PiTensorProduct.tprod C (fun τ => Formalism.UG.dualWeylRep C n n (res n (lamW τ)) (g τ) (y τ)) :=
  PiTensorProduct.map_tprod _ _

theorem scalar_eq {K C : Type} [Field K] [Field C] (e0 : K →+* C) {n : ℕ} (lam : DomWeight n) (k : ℕ) (c : ℤ)
    (h : ∀ hn : 0 < n, (k : ℤ) = lam.w ⟨n - 1, by omega⟩ + c) (g : GL (Fin n) K) :
    e0 (detPow K n (inside₂ K n g) lam.detShift) =
      ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map e0 g) ^ c : Cˣ) : C) *
        e0 ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ^ k := by
  have h1 : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = ((g : Matrix (Fin n) (Fin n) K).det)⁻¹ := by
    rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have h2 : ((inside₂ K n g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = ((g : Matrix (Fin n) (Fin n) K).det)⁻¹ := by
    rw [← h1]; exact Matrix.det_transpose _
  have h3 : ((Matrix.GeneralLinearGroup.map e0 g : GL (Fin n) C) : Matrix (Fin n) (Fin n) C).det =
      e0 (g : Matrix (Fin n) (Fin n) K).det := (RingHom.map_det e0 _).symm
  have h0 : e0 (g : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
    rw [map_ne_zero]; exact g.det_ne_zero
  simp only [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, h1, h2, h3, map_zpow₀, map_inv₀]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have he : lam.detShift = k - c := by
      rw [h hn]; simp [DomWeight.detShift, hn]
    rw [he, inv_zpow', inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ h0]
    congr 1
    ring

theorem phi_equivariant : ∀ (K C : Type) [Field K] [Field C] (e0 : K →+* C) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (Φ : VV K lam →ₛₗ[e0] NablaT C n lamW), Shift lam lamW c → IsPhi e0 lam lamW Φ → ∀ (g : ι → GL (Fin n) K) (v : VV K lam), Φ (rhoK lam (invTrK g) v) = lamG C n lamW c (fun τ => Matrix.GeneralLinearGroup.map e0 (g τ)) (Φ v) := by
  intro K C _ _ e0 ι _ _ n lam lamW c Φ hS hΦ g v
  obtain ⟨v, hv⟩ := v
  induction hv using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨x, hx, rfl⟩ := hP
    let M : ι → Matrix (Fin n) (Fin n) K := fun τ => ((g τ)⁻¹ : GL (Fin n) K)
    have hx' : ∀ τ, rowAct K (M τ) (x τ) ∈ nablaSq K n (lam τ) := fun τ =>
      Formalism.GradedWeylDivisibility.dualWeylRowStable K n n _ _ _ (hx τ)
    let w : VV K lam := ⟨Formalism.L2.DIV.ten fun τ => rowAct K (M τ) (x τ),
      Submodule.subset_span ⟨_, hx', rfl⟩⟩
    obtain ⟨y, hy, hyv⟩ := hΦ x ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩⟩ hx rfl
    obtain ⟨y', hy', hyw⟩ := hΦ _ w hx' rfl
    have hr : rhoK lam (invTrK g) ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩⟩ = detTwK lam (invTrK g) • w := by
      apply Subtype.ext
      show detTwK lam (invTrK g) • trAct (invTrK g) (∏ τ, blockEmb K τ (x τ)) =
        detTwK lam (invTrK g) • ∏ τ, blockEmb K τ (rowAct K (M τ) (x τ))
      congr 1
      rw [map_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      exact (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n M).1 τ (x τ)
    have hg : (fun τ => Formalism.UG.dualWeylRep C n n (res n (lamW τ)) (Matrix.GeneralLinearGroup.map e0 (g τ)) (y τ)) =
        fun τ => (e0 (M τ).det) ^ (lamW τ (n - 1)) • y' τ := by
      funext τ
      apply Subtype.ext
      show rowAct C (((Matrix.GeneralLinearGroup.map e0 (g τ))⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) (y τ) =
        (e0 (M τ).det) ^ (lamW τ (n - 1)) • (y' τ : MvPolynomial (Fin n × Fin n) C)
      rw [hy, hy', ← map_inv]
      exact rowAct_liftPol_eq e0 _ (M τ) (x τ)
    rw [hr, LinearMap.map_smulₛₗ, hyw, hyv, lamG_apply, grp_tprod_eq, hg, MultilinearMap.map_smul_univ, smul_smul]
    congr 1
    rw [detTwK, map_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact scalar_eq e0 (lam τ) _ (c τ) (fun hn => hS τ ⟨n - 1, by omega⟩) (g τ)
  | zero =>
    show Φ (rhoK lam (invTrK g) 0) = lamG C n lamW c _ (Φ 0)
    simp only [map_zero]
  | add a b ha hb iha ihb =>
    show Φ (rhoK lam (invTrK g) (⟨a, ha⟩ + ⟨b, hb⟩)) = lamG C n lamW c _ (Φ (⟨a, ha⟩ + ⟨b, hb⟩))
    simp only [map_add]
    rw [iha, ihb]
  | smul r a ha iha =>
    show Φ (rhoK lam (invTrK g) (r • ⟨a, ha⟩)) = lamG C n lamW c _ (Φ (r • ⟨a, ha⟩))
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_smul, iha]

end GlobalTheory.FrameRead.LiftEquiv

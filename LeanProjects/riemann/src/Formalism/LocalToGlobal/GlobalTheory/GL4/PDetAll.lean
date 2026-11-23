import Mathlib
import Formalism.LocalToGlobal.Columns.BrpAevalScaleMonomial

open MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

section Char

variable (K : Type) [Field K] [CharZero K] {n : ℕ} (χ : GL (Fin n) K →* K)

theorem glChar_ne_zero (g : GL (Fin n) K) : χ g ≠ 0 := by
  intro h
  have h1 : χ g * χ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem glChar_transvection (i j : Fin n) (hij : i ≠ j) (c : K) :
    χ (brpGL K (Matrix.transvection i j c) (brp_isUnit_transvection K i j hij c)) = 1 := by
  set T : K → GL (Fin n) K := fun c => brpGL K (Matrix.transvection i j c) (brp_isUnit_transvection K i j hij c) with hT
  have hdet2 : IsUnit (Matrix.diagonal (Function.update (1 : Fin n → K) i 2)).det := by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  set D := brpGL K _ hdet2
  have h2 : T c * T c = T (2 * c) := by
    apply Units.ext
    simp only [hT, Units.val_mul, brpGL_coe]
    rw [Matrix.transvection_mul_transvection_same i j hij, two_mul]
  have hDT : D * T c = T (2 * c) * D := by
    apply Units.ext
    simp only [hT, D, Units.val_mul, brpGL_coe]
    exact brp_diag_transvection K i j hij c
  have e1 := congrArg χ hDT
  rw [map_mul, map_mul, mul_comm (χ (T (2 * c)))] at e1
  have e2 : χ (T c) = χ (T (2 * c)) := mul_left_cancel₀ (glChar_ne_zero K χ D) e1
  rw [← h2, map_mul] at e2
  have hx := glChar_ne_zero K χ (T c)
  have : χ (T c) * (χ (T c) - 1) = 0 := by rw [mul_sub, mul_one, ← e2, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hx
  · exact (sub_eq_zero.1 h)

theorem glChar_single_eq (a b : Fin n) (t : Kˣ) :
    χ (brpDiag K (Pi.mulSingle a t)) = χ (brpDiag K (Pi.mulSingle b t)) := by
  set P := brpGL K _ (brp_isUnit_perm K (Equiv.swap a b))
  have hP : P * brpDiag K (Pi.mulSingle a t) = brpDiag K (Pi.mulSingle b t) * P := by
    apply Units.ext
    simp only [P, Units.val_mul, brpGL_coe, brpDiag_coe]
    rw [brp_perm_diag]
    congr 2
    funext x
    simp only [Function.comp_apply, Pi.mulSingle_apply]
    by_cases hx : x = b
    · subst hx; simp
    · by_cases hxa : x = a
      · subst hxa
        rw [Equiv.swap_apply_left]
        simp [hx, Ne.symm hx]
      · rw [Equiv.swap_apply_of_ne_of_ne hxa hx]
        simp [hx, hxa]
  have e := congrArg χ hP
  rw [map_mul, map_mul, mul_comm (χ (brpDiag K (Pi.mulSingle b t)))] at e
  exact mul_left_cancel₀ (glChar_ne_zero K χ P) e

theorem glChar_diag_pow (N : ℤ) (hs : ∀ t : Kˣ, χ (brpSc K t) = (t : K) ^ N) (d : Fin n → Kˣ) :
    χ (brpDiag K d) ^ n = (∏ a, (d a : K)) ^ N := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  set a0 : Fin n := ⟨0, hn⟩
  set φ : Kˣ → K := fun t => χ (brpDiag K (Pi.mulSingle a0 t))
  have h1 : χ (brpDiag K d) = ∏ a, φ (d a) := by
    conv_lhs => rw [← Finset.univ_prod_mulSingle d]
    change (χ.comp (brpDiag K)) _ = _
    rw [map_prod]
    exact Finset.prod_congr rfl fun a _ => glChar_single_eq K χ a a0 (d a)
  have h2 : ∀ t : Kˣ, φ t ^ n = (t : K) ^ N := by
    intro t
    have : φ t ^ n = ∏ a : Fin n, χ (brpDiag K (Pi.mulSingle a t)) := by
      rw [Finset.prod_congr rfl fun a _ => glChar_single_eq K χ a a0 t, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    rw [this]
    have hc : (∏ a : Fin n, Pi.mulSingle a t) = fun _ => t := Finset.univ_prod_mulSingle (fun _ : Fin n => t)
    have e : (∏ a : Fin n, χ (brpDiag K (Pi.mulSingle a t))) = (χ.comp (brpDiag K)) (∏ a : Fin n, Pi.mulSingle a t) := by
      rw [map_prod]; rfl
    rw [e, hc, MonoidHom.comp_apply, brpDiag_const, hs]
  rw [h1, ← Finset.prod_pow, Finset.prod_congr rfl fun a _ => h2 (d a), Finset.prod_zpow]

theorem glChar_list_transvec (L : List (Matrix.TransvectionStruct (Fin n) K)) :
    χ (L.map fun t => brpGL K t.toMatrix (by rw [t.det]; exact isUnit_one)).prod = 1 := by
  rw [map_list_prod, List.map_map]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx
  exact glChar_transvection K χ t.i t.j t.hij t.c

theorem glChar_pow (N : ℤ) (hs : ∀ t : Kˣ, χ (brpSc K t) = (t : K) ^ N) (g : GL (Fin n) K) :
    χ g ^ n = ((g : Matrix (Fin n) (Fin n) K).det) ^ N := by
  classical
  obtain ⟨L, L', D, hM⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (g : Matrix (Fin n) (Fin n) K)
  have hdet : (g : Matrix (Fin n) (Fin n) K).det = ∏ a, D a := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, brp_det_list_transvec, brp_det_list_transvec, Matrix.det_diagonal, one_mul, mul_one]
  have hD : ∀ a, D a ≠ 0 := by
    have h0 : (g : Matrix (Fin n) (Fin n) K).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
    rw [hdet] at h0
    exact fun a => (Finset.prod_ne_zero_iff.1 h0) a (Finset.mem_univ a)
  set Du : Fin n → Kˣ := fun a => Units.mk0 (D a) (hD a)
  have hg : g = (L.map fun t => brpGL K t.toMatrix (by rw [t.det]; exact isUnit_one)).prod * brpDiag K Du *
      (L'.map fun t => brpGL K t.toMatrix (by rw [t.det]; exact isUnit_one)).prod := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, brp_coe_list_transvec, brp_coe_list_transvec, brpDiag_coe, hM]
    simp [Du]
  conv_lhs => rw [hg]
  rw [map_mul, map_mul, glChar_list_transvec, glChar_list_transvec, one_mul, mul_one, glChar_diag_pow K χ N hs, hdet]
  simp [Du]

end Char

section Single

variable (K : Type) [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem rowAct_scalar (t : K) :
    Formalism.GradedWeylDivisibility.rowAct K (r := n) (n := n) ((t • 1 : Matrix (Fin n) (Fin n) K))ᵀ = aeval fun v => C t * X v := by
  unfold Formalism.GradedWeylDivisibility.rowAct
  congr 1
  funext v
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro b _ hb
    simp [Matrix.one_apply]
    intro h; exact absurd h hb
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rowAct_one_tr (F : MvPolynomial (Fin n × Fin n) K) :
    Formalism.GradedWeylDivisibility.rowAct K (r := n) (n := n) ((1 : Matrix (Fin n) (Fin n) K))ᵀ F = F := by
  have h := rowAct_scalar (n := n) K 1
  rw [one_smul] at h
  rw [h]
  simp

theorem trAct_single_scalar (lam : ι → DomWeight n) (τ : ι) (t : Kˣ) (F : Pol K ι n) (hF : F ∈ VV K lam) :
    trAct (Pi.mulSingle τ (brpSc K t)) F = (t : K) ^ (∑ i, (lam τ).natW i) • F := by
  unfold trAct
  induction hF using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨G, hG, rfl⟩ := hP
    rw [map_prod]
    have hfac : ∀ s, Formalism.GradedWeylDivisibility.blockAct K (fun σ => (((Pi.mulSingle τ (brpSc K t) : ι → GL (Fin n) K) σ : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)ᵀ) (Formalism.GradedWeylDivisibility.blockEmb K s (G s)) =
        (if s = τ then (t : K) ^ (∑ i, (lam τ).natW i) else 1) • Formalism.GradedWeylDivisibility.blockEmb K s (G s) := by
      intro s
      rw [(Formalism.GradedWeylDivisibility.blockActTensor K K ι n n _).1 s (G s)]
      by_cases hs : s = τ
      · subst hs
        rw [if_pos rfl, Pi.mulSingle_eq_same, brpSc_coe, rowAct_scalar]
        have hW : G s ∈ weightedHomogeneousSubmodule K (Formalism.GradedWeylDivisibility.colW n n) (lam s).natW :=
          (Submodule.mem_inf.1 (hG s)).1
        rw [brp_aeval_scale_whom _ _ hW, map_smul]
      · rw [if_neg hs, Pi.mulSingle_eq_of_ne hs, Units.val_one, rowAct_one_tr, one_smul]
    rw [Finset.prod_congr rfl fun s _ => hfac s, Finset.prod_smul, Finset.prod_ite_eq' Finset.univ τ, if_pos (Finset.mem_univ τ)]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

theorem detTwK_single_scalar (lam : ι → DomWeight n) (τ : ι) (t : Kˣ) :
    detTwK lam (Pi.mulSingle τ (brpSc K t)) = (t : K) ^ ((n : ℤ) * (lam τ).detShift) := by
  unfold detTwK
  rw [Finset.prod_eq_single τ]
  · rw [Pi.mulSingle_eq_same]
    unfold detPow
    have hdet : (Matrix.GeneralLinearGroup.det (brpSc K t : GL (Fin n) K) : K) = (t : K) ^ n := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, brpSc_coe]
      simp
    rw [Units.val_zpow_eq_zpow_val, hdet, ← zpow_natCast, ← zpow_mul]
  · intro s _ hs
    rw [Pi.mulSingle_eq_of_ne hs]
    simp [detPow]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rhoK_single_scalar (lam : ι → DomWeight n) (τ : ι) (t : Kˣ) :
    rhoK lam (Pi.mulSingle τ (brpSc K t)) = ((t : K) ^ wsum (lam τ)) • (1 : Module.End K (VV K lam)) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  show actP lam (Pi.mulSingle τ (brpSc K t)) F.1 = ((t : K) ^ wsum (lam τ)) • F.1
  unfold actP
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply, trAct_single_scalar K lam τ t F.1 F.2, detTwK_single_scalar, smul_smul]
  congr 1
  have ht : (t : K) ≠ 0 := t.ne_zero
  rw [wsum, brp_wsum, ← zpow_natCast, ← zpow_add₀ ht]
  congr 1
  push_cast
  ring

def chiAt (lam : ι → DomWeight n) (τ : ι) : GL (Fin n) K →* K :=
  (LinearMap.det : Module.End K (VV K lam) →* K).comp
    ((rhoK lam).comp (MonoidHom.mulSingle (fun _ : ι => GL (Fin n) K) τ))

theorem chiAt_scalar (lam : ι → DomWeight n) (τ : ι) (t : Kˣ) :
    chiAt K lam τ (brpSc K t) = (t : K) ^ (wsum (lam τ) * (Module.finrank K (VV K lam) : ℤ)) := by
  show LinearMap.det (rhoK lam (Pi.mulSingle τ (brpSc K t))) = _
  rw [rhoK_single_scalar, LinearMap.det_smul, map_one, mul_one, ← zpow_natCast, ← zpow_mul]

theorem detAll_pow [CharZero K] (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) :
    LinearMap.det (rhoK lam g) ^ n =
      ∏ τ, ((g τ : Matrix (Fin n) (Fin n) K).det) ^ (wsum (lam τ) * (Module.finrank K (VV K lam) : ℤ)) := by
  have h1 : LinearMap.det (rhoK lam g) = ∏ τ, chiAt K lam τ (g τ) := by
    have h0 := Finset.map_noncommProd Finset.univ (fun i => Pi.mulSingle i (g i))
      (fun i _ j _ _ => Pi.mulSingle_apply_commute g i j) ((LinearMap.det : Module.End K (VV K lam) →* K).comp (rhoK lam))
    rw [Finset.noncommProd_mulSingle g, Finset.noncommProd_eq_prod] at h0
    exact h0
  rw [h1, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun τ _ => glChar_pow K (chiAt K lam τ) _ (chiAt_scalar K lam τ) (g τ)

end Single

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorRight

noncomputable section

open Polynomial

namespace GlobalTheory.Per.LangUnit

open GlobalTheory.Cyc.FontW

theorem onto_of_cpl' {l : ℕ} {M : Type} [AddCommGroup M] (hM : Cpl l M) (f : M →+ M)
    (h : ∀ y, ∃ x z, f x - y = l • z) : Function.Surjective f := by
  intro y
  have hstep : ∀ (r : ℕ) (x : M), f x - y ∈ Dv l r M →
      ∃ x', f x' - y ∈ Dv l (r + 1) M ∧ x' - x ∈ Dv l r M := by
    intro r x hx
    obtain ⟨u, hu⟩ := mem_Dv.1 hx
    obtain ⟨a, z, haz⟩ := h (-u)
    refine ⟨x + l ^ r • a, mem_Dv.2 ⟨z, ?_⟩, mem_Dv.2 ⟨a, by abel⟩⟩
    rw [pow_succ, mul_smul, ← haz, map_add, map_nsmul, add_sub_right_comm, ← hu, sub_neg_eq_add,
      smul_add, add_comm]
  choose nx hnx using hstep
  let g : (r : ℕ) → {x // f x - y ∈ Dv l r M} := fun r =>
    Nat.rec ⟨0, mem_Dv.2 ⟨_, by rw [pow_zero, one_smul]⟩⟩
      (fun r b => ⟨nx r b.1 b.2, (hnx r b.1 b.2).1⟩) r
  obtain ⟨L, hL⟩ := hM.2 (fun r => (g r).1) fun r => (hnx r (g r).1 (g r).2).2
  refine ⟨L, sub_eq_zero.1 (hM.1 _ fun r => ?_)⟩
  have e : f L - y = f (L - (g r).1) + (f (g r).1 - y) := by rw [map_sub]; abel
  rw [e]
  exact add_mem (Dv_map f (hL r)) (g r).2

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [CommRing k] [CharP k p] [PerfectRing k p]

theorem eq_smul_of_coeff_zero {A : WittVector p k} (hA : A.coeff 0 = 0) : ∃ Z, A = p • Z := by
  have h0 : A ∈ Ideal.span {(p : WittVector p k)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, WittVector.constantCoeff_apply]
    exact hA
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 h0
  exact ⟨u, by rw [← hu, nsmul_eq_mul, mul_comm]⟩

theorem coeff_zero_frob_sub (ω X : WittVector p k) :
    (WittVector.frobenius X - ω * X).coeff 0 = X.coeff 0 ^ p - ω.coeff 0 * X.coeff 0 := by
  simp only [← WittVector.constantCoeff_apply, map_sub, map_mul]
  rw [WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP]
  simp only [WittVector.constantCoeff_apply]

theorem lang_unit
    (hroot : ∀ f : k[X], f.Monic → 0 < f.natDegree → ∃ x, f.IsRoot x)
    (ω : WittVector p k) (hω : IsUnit ω) :
    ∃ η : WittVector p k, IsUnit η ∧ WittVector.frobenius η = ω * η := by
  have hp1 : 1 < p := hp.out.one_lt
  haveI : Nontrivial k := CharP.nontrivial_of_char_ne_one hp.out.ne_one
  set ω₀ := ω.coeff 0 with hω₀
  have hu0 : IsUnit ω₀ := by
    rw [hω₀, ← WittVector.constantCoeff_apply]; exact hω.map _
  let f : WittVector p k →+ WittVector p k :=
    (WittVector.frobenius : WittVector p k →+* WittVector p k).toAddMonoidHom -
      AddMonoidHom.mulLeft ω
  have hf : ∀ X, f X = WittVector.frobenius X - ω * X := fun X => rfl

  have hmod : ∀ Y, ∃ X Z, f X - Y = p • Z := by
    intro Y
    obtain ⟨x, hx⟩ := hroot (X ^ p - (C ω₀ * X + C (Y.coeff 0)))
      (monic_X_pow_sub (by
        refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
        · exact (degree_C_mul_X_le _).trans_lt (by exact_mod_cast hp1)
        · exact (degree_C_le).trans_lt (by exact_mod_cast (by omega : 0 < p))))
      (by
        have hlow : (C ω₀ * X + C (Y.coeff 0)).natDegree < p := by
          refine (natDegree_add_le _ _).trans_lt (max_lt ?_ ?_)
          · exact ((natDegree_C_mul_le _ _).trans natDegree_X_le).trans_lt hp1
          · rw [natDegree_C]; omega
        rw [natDegree_sub_eq_left_of_natDegree_lt (by rwa [natDegree_X_pow]), natDegree_X_pow]
        omega)
    refine ⟨WittVector.teichmuller p x, eq_smul_of_coeff_zero ?_⟩
    have hx' : x ^ p - (ω₀ * x + Y.coeff 0) = 0 := by simpa using hx
    rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, hf, coeff_zero_frob_sub, WittVector.teichmuller_coeff_zero,
      ← hω₀]
    rw [← hx']; ring

  obtain ⟨t₀, ht₀⟩ := hroot (X ^ (p - 1) - C ω₀) (monic_X_pow_sub_C _ (by omega))
    (by rw [natDegree_X_pow_sub_C]; omega)
  have ht₀' : t₀ ^ (p - 1) = ω₀ := by simpa [sub_eq_zero] using ht₀
  have hut : IsUnit t₀ := (isUnit_pow_iff (by omega : p - 1 ≠ 0)).1 (ht₀' ▸ hu0)
  have htp : t₀ ^ p = ω₀ * t₀ := by
    rw [← ht₀', ← pow_succ, Nat.sub_add_cancel hp.out.one_le]
  set t := WittVector.teichmuller p t₀ with ht
  obtain ⟨Y, hY⟩ := eq_smul_of_coeff_zero (A := f t) (by
    rw [hf, coeff_zero_frob_sub, ht, WittVector.teichmuller_coeff_zero, ← hω₀, htp, sub_self])
  obtain ⟨Z, rfl⟩ := onto_of_cpl' (cpl_witt p k) f hmod Y
  refine ⟨t - p • Z, ?_, ?_⟩
  · have hj : -(p • Z) ∈ (⊥ : Ideal (WittVector p k)).jacobson :=
      IsAdicComplete.le_jacobson_bot (Ideal.span {(p : WittVector p k)})
        (neg_mem (Ideal.mem_span_singleton'.2 ⟨Z, by rw [nsmul_eq_mul, mul_comm]⟩))
    obtain ⟨u, hu⟩ : IsUnit t := hut.map (WittVector.teichmuller p)
    have h1 := Ideal.mem_jacobson_bot.1 hj (↑u⁻¹)
    have e : t - p • Z = (-(p • Z) * ↑u⁻¹ + 1) * u := by
      rw [add_mul, mul_assoc, Units.inv_mul, mul_one, one_mul, hu]; abel
    rw [e]
    exact h1.mul u.isUnit
  · rw [← sub_eq_zero, ← hf, map_sub, map_nsmul, hY, sub_self]

end GlobalTheory.Per.LangUnit

namespace GlobalTheory.Per

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

set_option synthInstance.maxHeartbeats 400000 in

theorem OCb_exists_root (l : ℕ) [Fact l.Prime] (f : (OCb l)[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) : ∃ x, f.IsRoot x := by
  haveI : IsAlgClosed (Cb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  haveI : ValuationRing (OCb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).2
  haveI : IsIntegrallyClosed (OCb l) := inferInstance
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (f.map (algebraMap (OCb l) (Cb l))) (by
    rw [degree_map_eq_of_injective (IsFractionRing.injective (OCb l) (Cb l)),
      degree_eq_natDegree hf.ne_zero]
    exact_mod_cast hd.ne')
  have hint : IsIntegral (OCb l) z := ⟨f, hf, by rwa [IsRoot, eval_map_algebraMap] at hz⟩
  obtain ⟨x, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨x, IsFractionRing.injective (OCb l) (Cb l) ?_⟩
  rw [IsRoot, eval_map_algebraMap, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at hz
  rw [hz, map_zero]

theorem frobenius_eq_mul_solvable :
    ∀ (l : ℕ) [Fact l.Prime] (ω : (Ainf l)ˣ), ∃ η : (Ainf l)ˣ, WittVector.frobenius (η : Ainf l) = ω * η := by
  intro l _ ω
  obtain ⟨η, ⟨u, rfl⟩, h⟩ := GlobalTheory.Per.LangUnit.lang_unit (p := l) (k := OCb l)
    (OCb_exists_root l) (ω : Ainf l) ω.isUnit
  exact ⟨u, h⟩

end GlobalTheory.Per

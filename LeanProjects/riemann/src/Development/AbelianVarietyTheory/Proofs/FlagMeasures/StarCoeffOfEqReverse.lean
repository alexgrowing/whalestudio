import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop

open Formalism.BasicNotions Formalism.MainNotions.N Polynomial

namespace GlobalTheory.GoodIdemReal

open GlobalTheory.SeriesSupportTest

theorem star_coeff_of_reverse : ∀ D : D7, (∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]), f.Monic → f.coeff 0 ≠ 0 →
      ∀ x, star ((D.ntypes.eSer k f).coeff x) = (D.ntypes.eSer k (C (f.coeff 0)⁻¹ * f.reverse)).coeff x) →
    (∀ γ : G0g D.nd, star (D.ntypes.e0.coeff γ) = D.ntypes.e0.coeff γ) := by
  intro D hS γ
  classical
  have : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  have : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩

  let ψ : ∀ k : Fin 2, (Fin D.R.r → ZMod (D.host.g k)) → (Fin D.R.r → ZMod (D.host.g k)) :=
    fun k a => if (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 then fun i => (dl (Formalism.CyclotomicNorms.monicOf a)).coeff i else a
  have hlab : ∀ k (a : Fin D.R.r → ZMod (D.host.g k)), (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 →
      (Formalism.CyclotomicNorms.monicOf a).Monic ∧ (Formalism.CyclotomicNorms.monicOf a).natDegree = D.R.r ∧ (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 :=
    fun k a ha => ⟨Formalism.CyclotomicNorms.Sqf.monic_monicOf a, Formalism.CyclotomicNorms.Sqf.natDegree_monicOf a, ha⟩
  have hψm : ∀ k a, (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 → Formalism.CyclotomicNorms.monicOf (ψ k a) = dl (Formalism.CyclotomicNorms.monicOf a) := by
    intro k a ha
    have hd := dl_lab (hlab k a ha)
    simp only [ψ, if_pos ha]
    exact Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ hd.1 hd.2.1
  have hψ0 : ∀ k a, (Formalism.CyclotomicNorms.monicOf a).coeff 0 = 0 → ψ k a = a := by
    intro k a ha
    simp only [ψ, ha, ne_eq, not_true_eq_false, if_false]
  have hψc : ∀ k a, (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 → (Formalism.CyclotomicNorms.monicOf (ψ k a)).coeff 0 ≠ 0 := by
    intro k a ha
    rw [hψm k a ha, (dl_lab (hlab k a ha)).2.2]
    exact inv_ne_zero ha
  have hψinv : ∀ k, Function.Involutive (ψ k) := by
    intro k a
    by_cases ha : (Formalism.CyclotomicNorms.monicOf a).coeff 0 = 0
    · rw [hψ0 k a ha, hψ0 k a ha]
    · funext i
      rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt (ψ k (ψ k a)) i, hψm k _ (hψc k a ha), hψm k a ha,
        dl_dl (hlab k a ha), Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]

  let Φ : Equiv.Perm (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) :=
    Function.Involutive.toPerm (fun a kv => ψ kv.1 (a kv)) (fun a => funext fun kv => hψinv kv.1 (a kv))
  have hΦ : ∀ a kv, Φ a kv = ψ kv.1 (a kv) := fun _ _ => rfl
  let good : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) → Prop :=
    fun a => D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))
  let T : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) → ℂ := fun a =>
    if good a then ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv)
    else 0
  have he : D.ntypes.e0.coeff γ = ∑ᶠ a, T a := rfl

  have hgood : ∀ a, (∀ kv, (Formalism.CyclotomicNorms.monicOf (a kv)).coeff 0 ≠ 0) → good a → good (Φ a) := by
    intro a ha h
    simp only [good] at h ⊢
    unfold NTypes.goodTuple at h ⊢
    intro k
    have hf : (fun v => Formalism.CyclotomicNorms.monicOf (Φ a ⟨k, v⟩)) = fun v => dl (Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) :=
      funext fun v => hψm k _ (ha ⟨k, v⟩)
    have h1 := good_dl _ _ (h k).1
    have h2 := good_dl _ _ (h k).2
    simp only [inv_inv] at h1 h2
    simp only [hf]
    exact ⟨h2, h1⟩

  have hzero : ∀ a, ∀ kv, (Formalism.CyclotomicNorms.monicOf (a kv)).coeff 0 = 0 → T a = 0 := by
    intro a kv h0
    simp only [T]
    split_ifs
    · refine Finset.prod_eq_zero (Finset.mem_univ kv) ?_
      rw [D.ntypes.eSer_zero _ _ (fun h => h.2.2 h0)]
      first
        | rfl
        | simp
    · rfl
  have key : ∀ a, star (T a) = T (Φ a) := by
    intro a
    by_cases hz : ∀ kv, (Formalism.CyclotomicNorms.monicOf (a kv)).coeff 0 ≠ 0
    · have hz' : ∀ kv, (Formalism.CyclotomicNorms.monicOf (Φ a kv)).coeff 0 ≠ 0 := fun kv => hψc _ _ (hz kv)
      have hiff : good (Φ a) ↔ good a := by
        refine ⟨fun h => ?_, hgood a hz⟩
        have := hgood (Φ a) hz' h
        have e : Φ (Φ a) = a := funext fun kv => hψinv kv.1 (a kv)
        rwa [e] at this
      simp only [T, hiff]
      split_ifs
      · rw [star_prod]
        refine Finset.prod_congr rfl fun kv _ => ?_
        rw [hS kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) (Formalism.CyclotomicNorms.Sqf.monic_monicOf _) (hz kv), hΦ, hψm _ _ (hz kv)]
        rfl
      · exact star_zero _
    · push_neg at hz
      obtain ⟨kv, h0⟩ := hz
      rw [hzero a kv h0, hzero (Φ a) kv (by rw [hΦ, hψ0 _ _ h0]; exact h0), star_zero]
  have hfin : (Function.support T).Finite := Set.toFinite _
  have hstar : star (∑ᶠ a, T a) = ∑ᶠ a, star (T a) := by
    have := map_finsum (starAddEquiv (R := ℂ)) hfin
    simpa only [starAddEquiv_apply] using this
  rw [he, hstar]
  simp_rw [key]
  exact finsum_comp_equiv Φ

end GlobalTheory.GoodIdemReal

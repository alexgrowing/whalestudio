import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module Polynomial

namespace GlobalTheory.BadCount

open Classical

variable (D : D7)

theorem neZeroG (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

theorem factG (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

attribute [local instance] neZeroG factG

def allTup (k : Fin 2) : Finset (Tup D k) :=
  Finset.univ.image fun a : D.nd.PlG k → (Fin D.R.r → ZMod (D.host.g k)) => fun v => Formalism.CyclotomicNorms.monicOf (a v)

theorem monicOf_injective (k : Fin 2) :
    Function.Injective (Formalism.CyclotomicNorms.monicOf : (Fin D.R.r → ZMod (D.host.g k)) → (ZMod (D.host.g k))[X]) := by
  intro a b h
  funext i
  rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt a i, h, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]

theorem tupOf_injective (k : Fin 2) :
    Function.Injective fun a : D.nd.PlG k → (Fin D.R.r → ZMod (D.host.g k)) => fun v => Formalism.CyclotomicNorms.monicOf (a v) := by
  intro a b h
  funext v
  exact monicOf_injective D k (congrFun h v)

theorem badElt_coeff (k : Fin 2) (S : Finset (Tup D k)) (g : G0g D.nd) :
    (badElt D k S).coeff g = if ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → g kv = 1 then
      ∑ t ∈ S, ∏ v : D.nd.PlG k, (D.ntypes.eSer k (t v)).coeff (g ⟨k, v⟩) else 0 := by
  unfold badElt
  rfl

theorem sum_eSer_monicOf (k : Fin 2) :
    ∑ b : Fin D.R.r → ZMod (D.host.g k), D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf b) = 1 := by
  obtain ⟨S, hS, hsum⟩ := D.ntypes.eSer_sum k
  rw [← hsum, ← Finset.sum_image (fun a _ b _ h => monicOf_injective D k h)]
  symm
  apply Finset.sum_subset
  · intro f hf
    obtain ⟨h1, h2, -⟩ := (hS f).1 hf
    exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, Formalism.CyclotomicNorms.Sqf.monicOf_coeffs f h1 h2⟩
  · intro f _ hf
    exact D.ntypes.eSer_zero k f fun h => hf ((hS f).2 h)

theorem badElt_all (k : Fin 2) : badElt D k (allTup D k) = 1 := by
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [badElt_coeff, allTup, Finset.sum_image (fun a _ b _ h => tupOf_injective D k h)]
  have e : ∑ a : D.nd.PlG k → (Fin D.R.r → ZMod (D.host.g k)),
      ∏ v, (D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf (a v))).coeff (g ⟨k, v⟩) =
      ∏ v, (1 : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))).coeff (g ⟨k, v⟩) := by
    refine (Fintype.prod_sum (fun v (b : Fin D.R.r → ZMod (D.host.g k)) =>
      (D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf b)).coeff (g ⟨k, v⟩))).symm.trans ?_
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← sum_eSer_monicOf D k, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [e, MonoidAlgebra.one_def, MonoidAlgebra.one_def]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h1 : g = 1
  · subst h1; simp
  · rw [if_neg (Ne.symm h1)]
    split_ifs with hs
    · obtain ⟨kv, hkv⟩ := Function.ne_iff.1 h1
      obtain ⟨k', v⟩ := kv
      by_cases hk : k' = k
      · subst hk
        exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg fun h => hkv h.symm)
      · exact absurd (hs ⟨k', v⟩ hk) hkv
    · rfl

def goodSet (k : Fin 2) : Finset (Tup D k) := (allTup D k).filter (goodAt D k)

def badSet (k : Fin 2) : Finset (Tup D k) := (allTup D k).filter fun t => ¬ goodAt D k t

theorem badElt_good_add_bad (k : Fin 2) : badElt D k (goodSet D k) + badElt D k (badSet D k) = 1 := by
  rw [← badElt_all D k]
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, badElt_coeff, badElt_coeff, badElt_coeff]
  split_ifs
  · exact Finset.sum_filter_add_sum_filter_not _ _ _
  · simp

theorem badElt_coeff_off (k : Fin 2) (S : Finset (Tup D k)) (h : G0g D.nd)
    (hh : ∃ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k ∧ h kv ≠ 1) : (badElt D k S).coeff h = 0 := by
  rw [badElt_coeff, if_neg]
  obtain ⟨kv, h1, h2⟩ := hh
  exact fun hs => h2 (hs kv h1)

theorem coeff_mul_factors (x y : MonoidAlgebra ℂ (G0g D.nd))
    (hx : ∀ h : G0g D.nd, (∃ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ 0 ∧ h kv ≠ 1) → x.coeff h = 0)
    (hy : ∀ h : G0g D.nd, (∃ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ 1 ∧ h kv ≠ 1) → y.coeff h = 0)
    (g : G0g D.nd) :
    (x * y).coeff g = x.coeff (fun kv => if kv.1 = 0 then g kv else 1) *
      y.coeff (fun kv => if kv.1 = 0 then 1 else g kv) := by
  rw [MonoidAlgebra.coeff_mul_apply_left]
  rw [Finsupp.sum_eq_single (fun kv => if kv.1 = 0 then g kv else 1)]
  · congr 2
    funext kv
    by_cases h0 : kv.1 = 0
    · simp [h0]
    · simp [h0]
  · intro b hb hne
    have hb0 : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ 0 → b kv = 1 := by
      intro kv hkv
      by_contra hc
      exact hb (hx b ⟨kv, hkv, hc⟩)
    obtain ⟨kv, hkv⟩ := Function.ne_iff.1 hne
    by_cases h0 : kv.1 = 0
    · rw [hy _ ⟨kv, by rw [h0]; decide, ?_⟩, mul_zero]
      intro hc
      apply hkv
      simp only [h0, if_true]
      have : (b⁻¹ * g) kv = 1 := hc
      rw [Pi.mul_apply, Pi.inv_apply, inv_mul_eq_one] at this
      exact this
    · exact absurd (by simp [h0, hb0 kv h0]) hkv
  · intro _
    exact zero_mul _

theorem e0_eq : D.ntypes.e0 = badElt D 0 (goodSet D 0) * badElt D 1 (goodSet D 1) := by
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [coeff_mul_factors D _ _ (fun h hh => badElt_coeff_off D 0 _ h hh) (fun h hh => badElt_coeff_off D 1 _ h hh),
    badElt_coeff, badElt_coeff, if_pos, if_pos]
  rotate_left
  · rintro ⟨k, v⟩ hk
    fin_cases k
    · simp
    · exact absurd rfl hk
  · rintro ⟨k, v⟩ hk
    fin_cases k
    · exact absurd rfl hk
    · simp
  have he : D.ntypes.e0.coeff g =
      ∑ᶠ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
        (if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
          ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (g kv) else 0) := rfl
  rw [he, finsum_eq_sum_of_fintype, goodSet, goodSet, Finset.sum_filter, Finset.sum_filter, allTup, allTup,
    Finset.sum_image (fun a _ b _ h => tupOf_injective D 0 h),
    Finset.sum_image (fun a _ b _ h => tupOf_injective D 1 h),
    Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv ((Equiv.piCurry fun k (_ : D.nd.PlG k) => Fin D.R.r → ZMod (D.host.g k)).trans
    (piFinTwoEquiv _)) _ _ fun a => ?_
  have hg : D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) ↔
      goodAt D 0 (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨0, v⟩)) ∧ goodAt D 1 (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨1, v⟩)) :=
    Fin.forall_fin_two
  rw [Fintype.prod_sigma, Fin.prod_univ_two]
  by_cases h0 : goodAt D 0 (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨0, v⟩)) <;>
  by_cases h1 : goodAt D 1 (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨1, v⟩)) <;>
  simp [hg, h0, h1, piFinTwoEquiv_apply, Equiv.piCurry_apply, Sigma.curry]

theorem one_sub_goodTypeIdempotent_eq_badTupleSums : ∃ S : ∀ k : Fin 2, Finset (Tup D k), (∀ k, ∀ t ∈ S k, ¬ goodAt D k t) ∧
    1 - D.ntypes.e0 = badElt D 0 (S 0) + badElt D 1 (S 1) - badElt D 0 (S 0) * badElt D 1 (S 1) := by
  refine ⟨badSet D, fun k t ht => (Finset.mem_filter.1 ht).2, ?_⟩
  rw [e0_eq, ← sub_eq_iff_eq_add'.2 (badElt_good_add_bad D 0).symm,
    ← sub_eq_iff_eq_add'.2 (badElt_good_add_bad D 1).symm]
  noncomm_ring

end GlobalTheory.BadCount

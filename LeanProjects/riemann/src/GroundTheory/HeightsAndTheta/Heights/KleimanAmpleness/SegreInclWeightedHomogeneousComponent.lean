import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime)

noncomputable section

section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type} [Field F]

omit [Fintype K] in

theorem segre_weight_mapDomain (e : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight (segreIdx ι))
        (Finsupp.mapDomain (fun v : Σ k, ι k => (⟨Sum.inr v.1, v.2⟩ : Σ c, segreIdx ι c)) e) =
      Sum.elim (fun _ => 0) (Finsupp.weight (NumbersDVR.blockWeight ι) e) := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index
      (h := fun (v : Σ c, segreIdx ι c) (n : ℕ) => n • NumbersDVR.blockWeight (segreIdx ι) v)
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  funext c
  rcases c with ⟨⟨⟩⟩ | k
  · simp [Finsupp.sum, Finset.sum_apply, NumbersDVR.blockWeight]
  · simp [Finsupp.sum, Finset.sum_apply, NumbersDVR.blockWeight, Pi.single_apply]

theorem segreIncl_weightedHomogeneousComponent (b : K → ℕ) (f : MRing ι F) :
    segreIncl ι F (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) =
      weightedHomogeneousComponent (NumbersDVR.blockWeight (segreIdx ι)) (Sum.elim (fun _ => 0) b)
        (segreIncl ι F f) := by
  classical
  have hinj : Function.Injective (fun v : Σ k, ι k => (⟨Sum.inr v.1, v.2⟩ : Σ c, segreIdx ι c)) := by
    rintro ⟨k, i⟩ ⟨k', i'⟩ h
    have h1 := Sigma.mk.inj h
    obtain rfl := Sum.inr_injective h1.1
    obtain rfl := eq_of_heq h1.2
    rfl
  ext e'
  rw [coeff_weightedHomogeneousComponent]
  by_cases he : ∃ e, Finsupp.mapDomain
      (fun v : Σ k, ι k => (⟨Sum.inr v.1, v.2⟩ : Σ c, segreIdx ι c)) e = e'
  · obtain ⟨e, rfl⟩ := he
    rw [segreIncl, coeff_rename_mapDomain _ hinj, coeff_rename_mapDomain _ hinj,
      coeff_weightedHomogeneousComponent, segre_weight_mapDomain]
    by_cases hd : Finsupp.weight (NumbersDVR.blockWeight ι) e = b
    · rw [if_pos hd, if_pos (by rw [hd])]
    · rw [if_neg hd, if_neg fun h => hd (funext fun k => congrFun h (Sum.inr k))]
  · push Not at he
    rw [segreIncl, coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    split_ifs
    · rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    · rfl

theorem segreLiftVal_eq (W : Ideal (MRing ι F)) (v : Σ c, segreIdx ι c) :
    ∃ β, segreLiftVal ι F W v =
      Polynomial.X ^ (NumbersDVR.blockWeight (segreIdx ι) v (Sum.inl ())) * Polynomial.C β := by
  rcases v with ⟨⟨⟨⟩⟩ | k, i⟩
  · exact ⟨Ideal.Quotient.mk W (∏ k, X ⟨k, i k⟩), by
      simp [segreLiftVal, NumbersDVR.blockWeight]⟩
  · exact ⟨Ideal.Quotient.mk W (X ⟨k, i⟩), by simp [segreLiftVal, NumbersDVR.blockWeight]⟩

theorem segreLiftMap_monomial (W : Ideal (MRing ι F)) (s : (Σ c, segreIdx ι c) →₀ ℕ) :
    ∀ r : F, ∃ a, segreLiftMap ι F W (monomial s r) =
      Polynomial.X ^ (Finsupp.weight (NumbersDVR.blockWeight (segreIdx ι)) s (Sum.inl ())) *
        Polynomial.C a := by
  refine Finsupp.induction s ?_ ?_
  · intro r
    refine ⟨algebraMap F _ r, ?_⟩
    simp [segreLiftMap, Polynomial.algebraMap_apply]
  · intro v n s _ _ ih r
    obtain ⟨a, ha⟩ := ih r
    obtain ⟨β, hβ⟩ := segreLiftVal_eq W v
    refine ⟨β ^ n * a, ?_⟩
    have hm : (monomial (Finsupp.single v n + s) r : MRing (segreIdx ι) F) =
        X v ^ n * monomial s r := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    rw [hm, map_mul, map_pow, ha, segreLiftMap, aeval_X, hβ, map_add, Pi.add_apply,
      Finsupp.weight_single, Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
    ring

theorem segreLiftMap_of_isWeightedHomogeneous (W : Ideal (MRing ι F)) {f : MRing (segreIdx ι) F}
    {e : Unit ⊕ K → ℕ} (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight (segreIdx ι)) f e) :
    ∃ a, segreLiftMap ι F W f = Polynomial.X ^ e (Sum.inl ()) * Polynomial.C a := by
  classical
  choose a ha using fun s => segreLiftMap_monomial W s (coeff s f)
  refine ⟨∑ s ∈ f.support, a s, ?_⟩
  conv_lhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [ha s, hf (mem_support_iff.mp hs)]

end

theorem SegreLiftComap.proof : SegreLiftComap.Statement := by
  intro F _ K _ _ ι _ W' hW' hrel
  classical
  have := hW'.isPrime
  have hW : IsMultiProjPrime (W'.comap (segreIncl ι F)) := by
    refine ⟨inferInstance, ?_, ?_⟩
    · intro f hf b
      rw [Ideal.mem_comap, segreIncl_weightedHomogeneousComponent]
      exact hW'.multiHomog _ hf _
    · intro k
      obtain ⟨i, hi⟩ := hW'.relevant (Sum.inr k)
      exact ⟨i, by rwa [Ideal.mem_comap, segreIncl, rename_X]⟩
  refine ⟨hW, ?_⟩
  set W := W'.comap (segreIncl ι F) with hWdef

  choose c' hc using fun k => hW'.relevant (Sum.inr k)
  let c : ∀ k, ι k := c'
  let D := MRing (segreIdx ι) F ⧸ W'
  let L := FractionRing D
  let π : MRing (segreIdx ι) F →+* L := (algebraMap D L).comp (Ideal.Quotient.mk W')
  have hπ : ∀ f, π f = 0 ↔ f ∈ W' := by
    intro f
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (IsFractionRing.injective D L).eq_iff' (map_zero _)
  have hmc : segreMon (R := F) c ∉ W' := by
    intro h
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hc k hk
  have hYc : segreY (R := F) c ∉ W' := by
    intro h
    obtain ⟨d, hd⟩ := hW'.relevant (Sum.inl ())
    have hr : segreY c * segreMon d - segreY d * segreMon c ∈ W' := hrel ⟨c, d, rfl⟩
    have : segreY (R := F) d * segreMon c ∈ W' := by
      have := W'.sub_mem (W'.mul_mem_right (segreMon d) h) hr
      rwa [sub_sub_cancel] at this
    exact (hW'.isPrime.mem_or_mem this).elim hd hmc
  have hMc : π (segreMon c) ≠ 0 := fun h => hmc ((hπ _).mp h)
  let u : L := π (segreY c) / π (segreMon c)
  have hu : u ≠ 0 := div_ne_zero (fun h => hYc ((hπ _).mp h)) hMc
  let j : MRing ι F ⧸ W →+* D :=
    Ideal.quotientMap W' (segreIncl ι F : MRing ι F →+* MRing (segreIdx ι) F) le_rfl
  have hj : Function.Injective j := Ideal.quotientMap_injective' le_rfl
  have hjmk : ∀ x, j (Ideal.Quotient.mk W x) = Ideal.Quotient.mk W' (segreIncl ι F x) :=
    fun x => Ideal.quotientMap_mk
  let Φ : Polynomial (MRing ι F ⧸ W) →+* L := Polynomial.eval₂RingHom ((algebraMap D L).comp j) u
  have hΦ : ∀ a, Φ (Polynomial.C a) = algebraMap D L (j a) := fun a => by
    simp [Φ]
  have hkey : ∀ f, Φ (segreLiftMap ι F W f) = π f := by
    have : Φ.comp (segreLiftMap ι F W : MRing (segreIdx ι) F →+* Polynomial (MRing ι F ⧸ W)) = π := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
      · simp only [RingHom.comp_apply, RingHom.coe_coe, segreLiftMap, aeval_C,
          Polynomial.algebraMap_apply, hΦ]
        rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, hjmk, segreIncl, rename_C]
        rfl
      · rcases v with ⟨⟨⟨⟩⟩ | k, i⟩
        · have hs : π (segreY c) * π (segreMon i) = π (segreY i) * π (segreMon c) := by
            have := (hπ _).mpr (hrel ⟨c, i, rfl⟩)
            rwa [map_sub, map_mul, map_mul, sub_eq_zero] at this
          have hinc : segreIncl ι F (∏ k, X ⟨k, i k⟩) = segreMon i := by
            simp [segreIncl, segreMon, map_prod]
          simp only [RingHom.comp_apply, RingHom.coe_coe, segreLiftMap, aeval_X, segreLiftVal,
            map_mul, hΦ]
          simp only [Φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
          rw [hjmk, hinc]
          change u * π (segreMon i) = π (segreY i)
          rw [div_mul_eq_mul_div, div_eq_iff hMc, hs]
        · simp only [RingHom.comp_apply, RingHom.coe_coe, segreLiftMap, aeval_X, segreLiftVal, hΦ]
          rw [hjmk, segreIncl, rename_X]
          rfl
    intro f
    exact RingHom.congr_fun this f
  ext f
  rw [segreLift, RingHom.mem_ker]
  constructor
  · intro hf
    rw [← sum_weightedHomogeneousComponent (NumbersDVR.blockWeight (segreIdx ι)) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]
    refine Finset.sum_eq_zero fun e _ => ?_
    obtain ⟨a, ha⟩ := segreLiftMap_of_isWeightedHomogeneous W
      (weightedHomogeneousComponent_isWeightedHomogeneous
        (w := NumbersDVR.blockWeight (segreIdx ι)) e f)
    have h0 : Φ (Polynomial.X ^ e (Sum.inl ()) * Polynomial.C a) = 0 := by
      rw [← ha, hkey]
      exact (hπ _).mpr (hW'.multiHomog f hf e)
    rw [map_mul, map_pow, hΦ] at h0
    have h1 := (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (by simpa [Φ] using hu))
    have h2 : j a = 0 := (IsFractionRing.injective D L) (by rw [h1, map_zero])
    have h3 : a = 0 := hj (by rw [h2, map_zero])
    rw [ha, h3, map_zero, mul_zero]
  · intro hf
    exact (hπ f).mp (by rw [← hkey, hf, map_zero])

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

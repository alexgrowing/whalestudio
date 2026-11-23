import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingUnits
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

theorem exists_two_mem_place (K : FiniteSubfield) :
    ∃ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal := by
  have hnu : ¬ IsUnit ((2 : ℕ) : 𝓞 K.1) := by
    rintro ⟨u, hu⟩
    have h : ((2 : ℕ) : 𝓞 K.1) * ((u⁻¹ : (𝓞 K.1)ˣ) : 𝓞 K.1) = 1 := by
      rw [← hu]
      exact u.mul_inv
    have hK : ((2 : ℕ) : K.1) * (((u⁻¹ : (𝓞 K.1)ˣ) : 𝓞 K.1) : K.1) = 1 := by
      have := congrArg (algebraMap (𝓞 K.1) K.1) h
      rwa [map_mul, map_natCast, map_one] at this
    have hint : IsIntegral ℤ (((u⁻¹ : (𝓞 K.1)ˣ) : 𝓞 K.1) : K.1) :=
      NumberField.RingOfIntegers.isIntegral_coe _
    have heq : (((u⁻¹ : (𝓞 K.1)ˣ) : 𝓞 K.1) : K.1) = algebraMap ℚ K.1 (1 / 2) := by
      rw [eq_inv_of_mul_eq_one_right hK]
      simp
    rw [heq, isIntegral_algebraMap_iff (algebraMap ℚ K.1).injective] at hint
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hy' : ((2 * y : ℤ) : ℚ) = 1 := by
      rw [Int.cast_mul, show ((y : ℤ) : ℚ) = algebraMap ℤ ℚ y from rfl, hy]
      norm_num
    have h2 : 2 * y = 1 := by exact_mod_cast hy'
    omega
  have hne : Ideal.span {((2 : ℕ) : 𝓞 K.1)} ≠ ⊤ := fun h => hnu (Ideal.span_singleton_eq_top.1 h)
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have h2M : ((2 : ℕ) : 𝓞 K.1) ∈ M := hle (Ideal.subset_span rfl)
  have hMbot : M ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at h2M
    have : ((2 : ℕ) : K.1) = 0 := by
      have := congrArg (algebraMap (𝓞 K.1) K.1) h2M
      rwa [map_natCast, map_zero] at this
    norm_num at this
  exact ⟨⟨M, hM.isPrime, hMbot⟩, h2M⟩

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

set_option maxHeartbeats 1000000 in

theorem exists_two_nsmul_finLocal (v : HeightOneSpectrum (𝓞 K.1))
    (a : cohomology (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) 2) :
    ∃ u, 2 • u = a := by
  obtain ⟨u₀, hu₀⟩ := (placeInv_bijective_inr (K := K) v).2
    (qzDiv 2 (placeInv (K := K) (.inr v) (finLocalEquiv (K := K) v 2 a)))
  refine ⟨(finLocalEquiv (K := K) v 2).symm u₀, (finLocalEquiv (K := K) v 2).injective ?_⟩
  rw [map_nsmul, AddEquiv.apply_symm_apply]
  apply (placeInv_bijective_inr (K := K) v).1
  rw [map_nsmul, hu₀, nsmul_qzDiv two_ne_zero]

section Maps

abbrev UnitsLoc (n : ℕ) : Type :=
  (∀ v : S, cohomology (finUnits S v) n) × (∀ w : {v : InfinitePlace K.1 // v.IsReal}, cohomology (realUnits w) n)

def unitsToGlobal (n : ℕ) : unitsTateCohomology S ιr ιs n →+ cohomology (galSUnitsMax K.1 ℚ̄ S) n :=
  (tateToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S)
    (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) n).hom.toAddMonoidHom

def unitsGlobalToLocal (n : ℕ) : cohomology (galSUnitsMax K.1 ℚ̄ S) n →+ UnitsLoc S n :=
  (tateGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S)
    (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) n).hom.toAddMonoidHom

def unitsLocalToCompact (n : ℕ) : UnitsLoc S n →+ unitsTateCohomology S ιr ιs (n + 1) :=
  (tateLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S)
    (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) n).hom.toAddMonoidHom

set_option maxHeartbeats 1000000 in
theorem exists_unitsLocalToCompact_eq (n : ℕ) (x : unitsTateCohomology S ιr ιs (n + 1))
    (hx : unitsToGlobal S ιr ιs (n + 1) x = 0) : ∃ t, unitsLocalToCompact S ιr ιs n t = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (tateCompactCohomology_exact_compact
    (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S) (finUnitsMor S ιs)
    realUnits (realUnitsMor S ιr) n) x hx

set_option maxHeartbeats 1000000 in
theorem unitsLocalToCompact_unitsGlobalToLocal (n : ℕ) (g : cohomology (galSUnitsMax K.1 ℚ̄ S) (n + 1)) :
    unitsLocalToCompact S ιr ιs (n + 1) (unitsGlobalToLocal S ιr ιs (n + 1) g) = 0 :=
  hom_apply_hom_apply_of_comp_eq (tateGlobalToLocal_tateLocalToCompact (gsFinFamily S ιs)
    (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S) (finUnitsMor S ιs) realUnits
    (realUnitsMor S ιr) n) g

set_option maxHeartbeats 1000000 in
theorem unitsLocalToCompact_two_unitsGlobalToLocal (g : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) :
    unitsLocalToCompact S ιr ιs 2 (unitsGlobalToLocal S ιr ιs 2 g) = 0 :=
  unitsLocalToCompact_unitsGlobalToLocal S ιr ιs 1 g

theorem unitsGlobalToLocal_fst (n : ℕ) (g : cohomology (galSUnitsMax K.1 ℚ̄ S) n) :
    (unitsGlobalToLocal S ιr ιs n g).1 =
      (globalToLocal (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (finUnits S) (finUnitsMor S ιs) n).hom g :=
  rfl

theorem unitsGlobalToLocal_snd (n : ℕ) (g : cohomology (galSUnitsMax K.1 ℚ̄ S) n) (w) :
    (unitsGlobalToLocal S ιr ιs n g).2 w = (realUnitsRes S ιr n w).hom g :=
  rfl

end Maps

section Div

variable (h2S : ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

set_option maxHeartbeats 2000000 in
include h2S in

theorem exists_realUnitsRes_two_eq
    (t : ∀ w : {v : InfinitePlace K.1 // v.IsReal}, cohomology (realUnits w) 2) :
    ∃ g : cohomology (galSUnitsMax K.1 ℚ̄ S) 2, ∀ w, (realUnitsRes S ιr 2 w).hom g = t w := by
  classical
  let ι : LocalEmbeddings K := (nonempty_localEmbeddings K).some
  obtain ⟨v₀, hv₀⟩ := exists_two_mem_place K
  have hv₀S : v₀ ∈ S := h2S v₀ hv₀
  let s : QZ := ∑ w, placeInv (K := K) (.inl w.1) (realLocalEquiv w 2 (t w))
  obtain ⟨c, hc⟩ := (placeInv_bijective_inr (K := K) v₀).2 (-s)
  let T : ⨁ v : Place K.1, localGaloisCohomology K 2 v :=
    (∑ w, DirectSum.of (localGaloisCohomology K 2) (.inl w.1) (realLocalEquiv w 2 (t w))) +
      DirectSum.of (localGaloisCohomology K 2) (.inr v₀) c
  have h2t : ∀ w, 2 • realLocalEquiv w 2 (t w) = 0 := fun w => by
    rw [← map_nsmul, two_nsmul_realLocal w (by norm_num) (t w), map_zero]
  have h2s : 2 • s = 0 := by
    change 2 • (∑ w, placeInv (K := K) (.inl w.1) (realLocalEquiv w 2 (t w))) = 0
    rw [Finset.smul_sum]
    exact Finset.sum_eq_zero fun w _ => by rw [← map_nsmul, h2t w, map_zero]
  have h2c : 2 • c = 0 := by
    apply (placeInv_bijective_inr (K := K) v₀).1
    rw [map_nsmul, hc, map_zero, smul_neg, h2s, neg_zero]
  have hT : T ∈ localPrimaryKernel K S 2 := by
    refine ⟨⟨1, ?_⟩, fun v hv => ?_, ?_⟩
    · rw [pow_one]
      change 2 • ((∑ w, DirectSum.of (localGaloisCohomology K 2) (.inl w.1) (realLocalEquiv w 2 (t w))) +
        DirectSum.of (localGaloisCohomology K 2) (.inr v₀) c) = 0
      rw [smul_add, Finset.smul_sum, ← map_nsmul, h2c, map_zero, add_zero]
      exact Finset.sum_eq_zero fun w _ => by rw [← map_nsmul, h2t w, map_zero]
    · change ((∑ w, DirectSum.of (localGaloisCohomology K 2) (.inl w.1) (realLocalEquiv w 2 (t w))) +
        DirectSum.of (localGaloisCohomology K 2) (.inr v₀) c) (.inr v) = 0
      rw [DirectSum.add_apply, DFinsupp.finsetSum_apply,
        Finset.sum_eq_zero fun w _ => DirectSum.of_eq_of_ne _ _ _ (by simp),
        DirectSum.of_eq_of_ne _ _ _ (fun (h : (Sum.inr v : Place K.1) = .inr v₀) =>
          hv (by rw [Sum.inr_injective h]; exact hv₀S)), add_zero]
    · change sumPlaceInv K ((∑ w, DirectSum.of (localGaloisCohomology K 2) (.inl w.1)
        (realLocalEquiv w 2 (t w))) + DirectSum.of (localGaloisCohomology K 2) (.inr v₀) c) = 0
      rw [map_add, map_sum, sumPlaceInv_of, hc]
      simp only [sumPlaceInv_of]
      exact add_neg_cancel s
  let g₀ := (sUnitsH2PrimaryEquiv K S 2 Nat.prime_two h2S ι).symm ⟨T, hT⟩
  refine ⟨g₀.1, fun w => (realLocalEquiv w 2).injective ?_⟩
  have hg : brauerLocal ι (sUnitsBrauer K S g₀.1) = T := by
    have := coe_sUnitsH2PrimaryEquiv_apply K S 2 Nat.prime_two h2S ι g₀
    rw [AddEquiv.apply_symm_apply] at this
    exact this.symm
  have hw : brauerLocal ι (sUnitsBrauer K S g₀.1) (.inl w.1) =
      realLocalization ι (by norm_num : 1 ≤ 2) (sUnitsInfl K S 2 g₀.1) w := rfl
  rw [← realLocalEquiv_realUnitsRes S ιr ι (by norm_num) w, ← hw, hg]
  change ((∑ w, DirectSum.of (localGaloisCohomology K 2) (.inl w.1) (realLocalEquiv w 2 (t w))) +
    DirectSum.of (localGaloisCohomology K 2) (.inr v₀) c) (.inl w.1) = _
  rw [DirectSum.add_apply, DFinsupp.finsetSum_apply, DirectSum.of_eq_of_ne _ _ _ (by simp), add_zero,
    Finset.sum_eq_single w]
  · exact DirectSum.of_eq_same _ _
  · intro w' _ hw'
    exact DirectSum.of_eq_of_ne _ _ _ fun h => hw' (Subtype.ext (Sum.inl_injective h).symm)
  · intro h
    exact absurd (Finset.mem_univ w) h

set_option maxHeartbeats 1000000 in
include h2S in

theorem exists_eq_two_nsmul_add_unitsGlobalToLocal (t : UnitsLoc S 2) :
    ∃ (t' : UnitsLoc S 2) (g : cohomology (galSUnitsMax K.1 ℚ̄ S) 2),
      t = 2 • t' + unitsGlobalToLocal S ιr ιs 2 g := by
  refine (exists_realUnitsRes_two_eq S ιr h2S t.2).elim fun g hg => ?_
  have hu : ∀ v : S, ∃ u : cohomology (finUnits S v) 2, 2 • u = t.1 v - (unitsGlobalToLocal S ιr ιs 2 g).1 v :=
    fun v => exists_two_nsmul_finLocal (K := K) v.1 _
  choose u hu using hu
  refine ⟨(u, 0), g, Prod.ext (funext fun v => ?_) (funext fun w => ?_)⟩
  · change t.1 v = 2 • u v + (unitsGlobalToLocal S ιr ιs 2 g).1 v
    rw [hu v, sub_add_cancel]
  · change t.2 w = 2 • (0 : cohomology (realUnits w) 2) + (unitsGlobalToLocal S ιr ιs 2 g).2 w
    rw [smul_zero, zero_add, unitsGlobalToLocal_snd, hg w]

set_option maxHeartbeats 1000000 in
include h2S in

theorem exists_two_nsmul_unitsTate_three (z : unitsTateCohomology S ιr ιs (2 + 1)) : ∃ z', 2 • z' = z := by
  obtain ⟨N, hN⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1
    (isTorsion_cohomology (galSUnitsMax K.1 ℚ̄ S) (n := 2 + 1) (by norm_num) (unitsToGlobal S ιr ιs (2 + 1) z))
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd hN.1.ne'
  have hby : unitsToGlobal S ιr ιs (2 + 1) (b • z) = 0 := by
    rw [map_nsmul]
    refine eq_zero_of_h3_sUnits K S 2 Nat.prime_two h2S _ a ?_
    rw [smul_smul, ← hab, hN.2]
  obtain ⟨t, ht⟩ := exists_unitsLocalToCompact_eq S ιr ιs 2 (b • z) hby
  obtain ⟨t', g, htg⟩ := exists_eq_two_nsmul_add_unitsGlobalToLocal S ιr ιs h2S t
  have hbz : b • z = 2 • unitsLocalToCompact S ιr ιs 2 t' :=
    ht.symm.trans ((congrArg (unitsLocalToCompact S ιr ιs 2) htg).trans ((map_add _ _ _).trans
      ((congrArg₂ (· + ·) (map_nsmul _ 2 t') (unitsLocalToCompact_two_unitsGlobalToLocal S ιr ιs g)).trans
        (add_zero _))))
  obtain ⟨c, rfl⟩ := hb
  refine ⟨unitsLocalToCompact S ιr ιs 2 t' - c • z, ?_⟩
  refine (smul_sub 2 (unitsLocalToCompact S ιr ιs 2 t') (c • z)).trans ?_
  refine (congrArg₂ (· - ·) hbz.symm (smul_smul 2 c z)).trans ?_
  rw [add_smul, one_smul, add_sub_cancel_left]

set_option maxHeartbeats 1000000 in
include h2S in

theorem exists_two_nsmul_unitsTate_of_four_le {m : ℕ} (hm : 3 ≤ m + 1)
    (x : unitsTateCohomology S ιr ιs (m + 1 + 1)) : ∃ x', 2 • x' = x := by
  obtain ⟨N, hN⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1
    (isTorsion_cohomology (galSUnitsMax K.1 ℚ̄ S) (n := m + 1 + 1) (by omega)
      (unitsToGlobal S ιr ιs (m + 1 + 1) x))
  obtain ⟨t, ht⟩ := exists_unitsLocalToCompact_eq S ιr ιs (m + 1) (N • x) (by rw [map_nsmul, hN.2])
  have h2t : 2 • t = 0 := Prod.ext
    (funext fun v => @Subsingleton.elim _ (subsingleton_finLocal S v hm) _ _)
    (funext fun w => two_nsmul_realLocal w (by omega) (t.2 w))
  have hx : (2 * N) • x = 0 := by
    rw [mul_smul, ← ht, ← map_nsmul, h2t, map_zero]
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : 2 * N ≠ 0)
  have hbx : b • x = 0 := eq_zero_unitsTateCohomology_of_two_pow_nsmul S ιr ιs h2S (by omega) (b • x)
    (k := a) (by rw [smul_smul, ← hab, hx])
  obtain ⟨c, rfl⟩ := hb
  refine ⟨(c + 1) • x, ?_⟩
  rw [smul_smul, show 2 * (c + 1) = (2 * c + 1) + 1 by ring, add_smul, hbx, one_smul, zero_add]

include h2S in

theorem exists_two_nsmul_unitsTateCohomology {r : ℕ} (hr : 3 ≤ r) (x : unitsTateCohomology S ιr ιs r) :
    ∃ x', 2 • x' = x := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 + 1 := ⟨r - 2, by omega⟩
  rcases Nat.lt_or_ge m 2 with h | h
  · obtain rfl : m = 1 := by omega
    exact exists_two_nsmul_unitsTate_three S ιr ιs h2S x
  · exact exists_two_nsmul_unitsTate_of_four_le S ιr ιs h2S (by omega) x

end Div

end

end GroundTheory.ProfCoh

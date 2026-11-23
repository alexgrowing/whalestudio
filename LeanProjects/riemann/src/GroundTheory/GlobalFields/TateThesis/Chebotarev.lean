import Mathlib
import GroundTheory.GlobalFields.TateThesis.ChebotarevCount
import GroundTheory.GlobalFields.TateThesis.ChebotarevAbelian
import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity

namespace GroundTheory.Global

open NumberField IsDedekindDomain IntermediateField AdeleBaseChange Filter Topology Set

noncomputable section

universe u

section Sums

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E]

theorem primeIdealZetaSum_eq_mul_of_card_fiber {A : Set (HeightOneSpectrum (𝓞 E))}
    {T : Set (HeightOneSpectrum (𝓞 K))} (π : HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 K))
    (hπ : ∀ u ∈ A, π u ∈ T) (hN : ∀ u ∈ A, Ideal.absNorm u.asIdeal = Ideal.absNorm (π u).asIdeal)
    {n : ℕ} (hn : n ≠ 0) (hcard : ∀ v ∈ T, Nat.card {u // u ∈ A ∧ π u = v} = n) {s : ℝ}
    (hs : 1 < s) : A.primeIdealZetaSum s = n * T.primeIdealZetaSum s := by
  classical
  let p : A → T := fun u ↦ ⟨π u, hπ u u.2⟩
  have hcard' : ∀ v : T, Nat.card {u // p u = v} = n := by
    intro v
    rw [← hcard v.1 v.2]
    exact Nat.card_congr
      { toFun := fun u ↦ ⟨u.1.1, u.1.2, congrArg Subtype.val u.2⟩
        invFun := fun u ↦ ⟨⟨u.1, u.2.1⟩, Subtype.ext u.2.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  have hfin : ∀ v : T, Finite {u // p u = v} := fun v ↦
    Nat.finite_of_card_ne_zero (by rw [hcard']; exact hn)
  have hsumA := summable_absNorm_rpow_neg_subtype A hs
  rw [Set.primeIdealZetaSum_def, Set.primeIdealZetaSum_def,
    ← (Equiv.sigmaFiberEquiv p).tsum_eq,
    Summable.tsum_sigma'
      (f := fun q ↦ (Ideal.absNorm ((Equiv.sigmaFiberEquiv p) q).1.asIdeal : ℝ) ^ (-s))
      (fun v ↦ by have := hfin v; exact Summable.of_finite)
      ((Equiv.sigmaFiberEquiv p).summable_iff.mpr hsumA :),
    ← tsum_mul_left]
  refine tsum_congr fun v ↦ ?_
  have := hfin v
  let _ := Fintype.ofFinite {u // p u = v}
  rw [tsum_fintype]
  calc ∑ u : {u // p u = v}, (Ideal.absNorm (Equiv.sigmaFiberEquiv p ⟨v, u⟩).1.asIdeal : ℝ) ^ (-s)
      = ∑ _u : {u // p u = v}, (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-s) :=
        Finset.sum_congr rfl fun u _ ↦ by
          rw [Equiv.sigmaFiberEquiv_apply, hN u.1.1 u.1.2,
            show π u.1.1 = v.1 from congrArg Subtype.val u.2]
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard', nsmul_eq_mul]

theorem HasDirichletDensity.union {A B : Set (HeightOneSpectrum (𝓞 K))} {a b : ℝ}
    (hA : A.HasDirichletDensity a) (hB : B.HasDirichletDensity b) (hd : Disjoint A B) :
    (A ∪ B).HasDirichletDensity (a + b) := by
  unfold Set.HasDirichletDensity at *
  refine (hA.add hB).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [primeIdealZetaSum_union hd hs, add_div]

end Sums

section Class

variable {G : Type*} [Group G]

theorem natCard_isConj_mul_natCard_centralizer (σ : G) :
    Nat.card {τ : G | IsConj σ τ} * Nat.card (Subgroup.centralizer {σ}) = Nat.card G := by
  have horb : MulAction.orbit (ConjAct G) σ = {τ : G | IsConj σ τ} := by
    ext τ
    rw [ConjAct.mem_orbit_conjAct, isConj_comm]
    rfl
  have hstab : Nat.card (Subgroup.centralizer {σ}) =
      Nat.card (MulAction.stabilizer (ConjAct G) σ) :=
    Nat.card_congr (Equiv.subtypeEquiv ConjAct.toConjAct.toEquiv fun g ↦ by
      rw [Subgroup.mem_centralizer_singleton_iff]
      change _ ↔ ConjAct.toConjAct g • σ = σ
      rw [ConjAct.toConjAct_smul, mul_inv_eq_iff_eq_mul])
  rw [Nat.card_coe_set_eq, ← horb, ← MulAction.index_stabilizer, hstab, mul_comm,
    Subgroup.card_mul_index]
  rfl

end Class

section Deuring

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem hasDirichletDensity_deuringSet (σ : Gal(L/K)) :
    (deuringSet σ).HasDirichletDensity (1 / orderOf σ) := by
  have := isMulCommutative_gal_fixedField_zpowers σ
  have hab := hasDirichletDensity_setOf_arithFrobAt_eq (K := fixedField (Subgroup.zpowers σ))
    (L := L) (galFixedZpowers σ)
  rw [natCard_gal_fixedField_zpowers] at hab
  have h1 := (hasDirichletDensity_inter_degreeOnePrimes_iff K _ _).2 hab
  refine (hasDirichletDensity_iff_of_subset_of_isBoundedUnder ?_
    (isBoundedUnder_primeIdealZetaSum_of_finite
      (((finite_setOf_ramificationIdx_ne_one K L).image
        (HeightOneSpectrum.under (𝓞 (fixedField (Subgroup.zpowers σ))))).subset ?_)) _).2 h1
  · intro u hu
    refine ⟨fun w hw ↦ ⟨?_, (hu.2 w hw).2⟩, hu.1⟩
    have h := Ideal.ramificationIdx_tower (R := 𝓞 K) u.asIdeal w.asIdeal
    rw [(hu.2 w hw).1] at h
    exact (mul_eq_one.1 h.symm).2
  · rintro u ⟨⟨hab, hdeg⟩, hnot⟩
    by_contra hu
    refine hnot ⟨hdeg, fun w hw ↦ ⟨?_, (hab w hw).2⟩⟩
    by_contra he
    exact hu ⟨w, he, HeightOneSpectrum.ext hw.over.symm⟩

theorem hasDirichletDensity_chebotarevSet_isConj (σ : Gal(L/K)) :
    (chebotarevSet {τ : Gal(L/K) | IsConj σ τ}).HasDirichletDensity
      (1 / Nat.card (Subgroup.centralizer {σ})) := by
  set E := fixedField (Subgroup.zpowers σ)
  set T := chebotarevSet {τ : Gal(L/K) | IsConj σ τ}
  set A := deuringSet σ
  set n := Nat.card (Subgroup.centralizer {σ}) / orderOf σ with hndef
  have hm : 0 < orderOf σ := orderOf_pos σ
  have hle : Subgroup.zpowers σ ≤ Subgroup.centralizer {σ} :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hZ : n * orderOf σ = Nat.card (Subgroup.centralizer {σ}) := by
    refine Nat.div_mul_cancel ?_
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hle
  have hn : n ≠ 0 := by
    intro h
    rw [h, zero_mul] at hZ
    exact Nat.card_pos.ne' hZ.symm
  have hcard : ∀ v ∈ T, Nat.card {u // u ∈ A ∧ HeightOneSpectrum.under (𝓞 K) u = v} = n :=
    fun v hv ↦ Nat.eq_of_mul_eq_mul_right hm ((card_fiber_deuringSet_mul_orderOf σ hv).trans hZ.symm)
  have hsum : ∀ s : ℝ, 1 < s → A.primeIdealZetaSum s = n * T.primeIdealZetaSum s := fun s hs ↦
    primeIdealZetaSum_eq_mul_of_card_fiber (HeightOneSpectrum.under (𝓞 K))
      (fun u hu ↦ under_mem_chebotarevSet σ hu)
      (fun u hu ↦ absNorm_eq_of_inertiaDeg_eq_one u hu.1) hn hcard hs
  have hA := hasDirichletDensity_deuringSet σ
  have hEK := tendsto_primeIdealZetaSum_univ_div_univ E K
  have hEpos := (tendsto_primeIdealZetaSum_univ_atTop E).eventually_gt_atTop 0
  have hKpos := (tendsto_primeIdealZetaSum_univ_atTop K).eventually_gt_atTop 0
  unfold Set.HasDirichletDensity at hA ⊢
  have hlim := (hA.const_mul (n : ℝ)⁻¹).mul hEK
  have hval : (n : ℝ)⁻¹ * (1 / orderOf σ) * 1 = 1 / Nat.card (Subgroup.centralizer {σ}) := by
    rw [← hZ]
    push_cast
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have : (orderOf σ : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hEpos, hKpos] with s hs hE hK
  rw [hsum s hs]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

end Deuring

section Main

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem isConj_arithFrobAt_of_liesOver {v : HeightOneSpectrum (𝓞 K)} (w w' : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal) (hw' : w'.asIdeal.LiesOver v.asIdeal) :
    IsConj (arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal) (arithFrobAt (𝓞 K) Gal(L/K) w'.asIdeal) :=
  isConj_arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal w'.asIdeal (hw.over.symm.trans hw'.over)

theorem chebotarevSet_empty : chebotarevSet (∅ : Set Gal(L/K)) = ∅ := by
  ext v
  simp only [mem_empty_iff_false, iff_false]
  intro hv
  obtain ⟨⟨w, hw⟩⟩ := nonempty_placesOver L v
  exact (hv w hw).2

theorem chebotarevSet_mono {C C' : Set Gal(L/K)} (h : C ⊆ C') :
    chebotarevSet C ⊆ chebotarevSet C' :=
  fun _ hv w hw ↦ ⟨(hv w hw).1, h (hv w hw).2⟩

theorem disjoint_chebotarevSet {C C' : Set Gal(L/K)} (h : Disjoint C C') :
    Disjoint (chebotarevSet C) (chebotarevSet C') := by
  refine Set.disjoint_left.2 fun v h1 h2 ↦ ?_
  obtain ⟨⟨w, hw⟩⟩ := nonempty_placesOver L v
  exact Set.disjoint_left.1 h (h1 w hw).2 (h2 w hw).2

theorem chebotarevSet_eq_union (C : Set Gal(L/K)) (σ : Gal(L/K)) :
    chebotarevSet C = chebotarevSet (C ∩ {τ | IsConj σ τ}) ∪
      chebotarevSet (C \ {τ | IsConj σ τ}) := by
  refine Subset.antisymm (fun v hv ↦ ?_)
    (union_subset (chebotarevSet_mono inter_subset_left) (chebotarevSet_mono sdiff_subset))
  obtain ⟨⟨w1, hw1⟩⟩ := nonempty_placesOver L v
  by_cases h : IsConj σ (arithFrobAt (𝓞 K) Gal(L/K) w1.asIdeal)
  · refine Or.inl fun w hw ↦ ⟨(hv w hw).1, (hv w hw).2, ?_⟩
    exact h.trans (isConj_arithFrobAt_of_liesOver w1 w hw1 hw)
  · refine Or.inr fun w hw ↦ ⟨(hv w hw).1, (hv w hw).2, fun h' ↦ h ?_⟩
    exact h'.trans (isConj_arithFrobAt_of_liesOver w w1 hw hw1)

theorem hasDirichletDensity_chebotarevSet (C : Set Gal(L/K))
    (hC : ∀ σ ∈ C, ∀ τ : Gal(L/K), τ * σ * τ⁻¹ ∈ C) :
    (chebotarevSet C).HasDirichletDensity (Nat.card C / Nat.card Gal(L/K)) := by
  suffices h : ∀ n : ℕ, ∀ C : Set Gal(L/K), (∀ σ ∈ C, ∀ τ : Gal(L/K), τ * σ * τ⁻¹ ∈ C) →
      Nat.card C = n → (chebotarevSet C).HasDirichletDensity (n / Nat.card Gal(L/K)) from
    h _ C hC rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C hC hn
  rcases C.eq_empty_or_nonempty with rfl | ⟨σ, hσ⟩
  · subst hn
    rw [chebotarevSet_empty]
    simpa using Set.hasDirichletDensity_empty
  set cl := {τ : Gal(L/K) | IsConj σ τ} with hcldef
  have hcl : cl ⊆ C := fun τ hτ ↦ by
    obtain ⟨c, rfl⟩ := isConj_iff.1 hτ
    exact hC σ hσ c
  have hC' : ∀ ρ ∈ C \ cl, ∀ τ : Gal(L/K), τ * ρ * τ⁻¹ ∈ C \ cl := fun ρ hρ τ ↦
    ⟨hC ρ hρ.1 τ, fun h ↦ hρ.2 (h.trans (isConj_iff.2 ⟨τ, rfl⟩).symm)⟩
  have hcard : Nat.card ↥(C \ cl) + Nat.card ↥cl = n := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      Set.ncard_sdiff_add_ncard_of_subset hcl (Set.toFinite C), ← Nat.card_coe_set_eq, hn]
  have hclpos : 0 < Nat.card ↥cl := by
    have : Nonempty ↥cl := ⟨⟨σ, IsConj.refl σ⟩⟩
    exact Nat.card_pos
  have h1 := ih _ (by omega) (C \ cl) hC' rfl
  have h2 := hasDirichletDensity_chebotarevSet_isConj σ
  have hd := disjoint_chebotarevSet (L := L) (disjoint_sdiff_right : Disjoint cl (C \ cl))
  have hU := HasDirichletDensity.union h2 h1 hd
  rw [chebotarevSet_eq_union C σ, inter_eq_right.2 hcl]
  convert hU using 1
  have hG := natCard_isConj_mul_natCard_centralizer σ
  rw [← hcldef] at hG
  have hZ : (Nat.card (Subgroup.centralizer {σ}) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hcl' : (Nat.card ↥cl : ℝ) ≠ 0 := by exact_mod_cast hclpos.ne'
  rw [← hcard, ← hG]
  push_cast
  field_simp
  ring

theorem hasDirichletDensity_setOf_arithFrobAt_mem (C : Set Gal(L/K))
    (hC : ∀ σ ∈ C, ∀ τ : Gal(L/K), τ * σ * τ⁻¹ ∈ C) :
    {v : HeightOneSpectrum (𝓞 K) | ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
      w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal ∈ C}.HasDirichletDensity
      (Nat.card C / Nat.card Gal(L/K)) :=
  hasDirichletDensity_chebotarevSet C hC

theorem hasDirichletDensity_setOf_exists_arithFrobAt_mem (C : Set Gal(L/K))
    (hC : ∀ σ ∈ C, ∀ τ : Gal(L/K), τ * σ * τ⁻¹ ∈ C) :
    {v : HeightOneSpectrum (𝓞 K) | (∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
      w.asIdeal.ramificationIdx (𝓞 K) = 1) ∧ ∃ w : HeightOneSpectrum (𝓞 L),
        w.asIdeal.LiesOver v.asIdeal ∧ arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal ∈ C}.HasDirichletDensity
      (Nat.card C / Nat.card Gal(L/K)) := by
  convert hasDirichletDensity_chebotarevSet C hC using 1
  ext v
  constructor
  · rintro ⟨he, w1, hw1, hC1⟩ w hw
    refine ⟨he w hw, ?_⟩
    obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_arithFrobAt_of_liesOver w1 w hw1 hw)
    rw [← hc]
    exact hC _ hC1 c
  · intro hv
    obtain ⟨⟨w, hw⟩⟩ := nonempty_placesOver L v
    exact ⟨fun w' hw' ↦ (hv w' hw').1, w, hw, (hv w hw).2⟩

end Main

end

end GroundTheory.Global

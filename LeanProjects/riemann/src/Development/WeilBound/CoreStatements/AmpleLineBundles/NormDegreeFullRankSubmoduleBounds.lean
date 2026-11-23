import Development.WeilBound.CoreStatements.AmpleLineBundles.NormDegreeLeOfMetricBoundedMap

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace CoverDenseAlt

private theorem card_quotient_span_eq_relIndex {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (G : Submodule R M) {ι : Type*} (s : ι → G) :
    Nat.card (G ⧸ Submodule.span R (Set.range s)) =
      (Submodule.span R (Set.range fun i => (s i : M))).toAddSubgroup.relIndex G.toAddSubgroup := by
  have h : Submodule.span R (Set.range s) =
      (Submodule.span R (Set.range fun i => (s i : M))).comap G.subtype := by
    have hr : (Set.range fun i => (s i : M)) = G.subtype '' Set.range s := by
      rw [← Set.range_comp]
      rfl
    rw [hr, ← Submodule.map_span, Submodule.comap_map_eq_of_injective G.injective_subtype]
  rw [h]
  rfl

private theorem index_span_ne_zero_of_linearIndependent {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    {n : ℕ} (hn : Module.finrank (𝓞 K) E.carrier = n) (v : Fin n → E.carrier)
    (hv : LinearIndependent (𝓞 K) v) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.index ≠ 0 := by
  classical
  have hfinZ : Module.Finite ℤ E.carrier := Module.Finite.trans (𝓞 K) E.carrier
  set S := Submodule.span (𝓞 K) (Set.range v) with hSdef
  have key : ∀ y : E.carrier, ∃ a : 𝓞 K, a ≠ 0 ∧ a • y ∈ S := by
    intro y
    have hnot : ¬ LinearIndependent (𝓞 K) (Fin.snoc (α := fun _ => E.carrier) v y) := by
      intro h
      have := h.fintype_card_le_finrank
      rw [hn] at this
      simp at this
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnot
    rw [Fin.sum_univ_castSucc] at hg
    simp only [Fin.snoc_castSucc, Fin.snoc_last] at hg
    by_cases hl : g (Fin.last n) = 0
    · exfalso
      rw [hl, zero_smul, add_zero] at hg
      have h0 := Fintype.linearIndependent_iff.mp hv (fun j => g j.castSucc) hg
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact hi (h0 j)
      · exact hi hl
    · refine ⟨g (Fin.last n), hl, ?_⟩
      rw [eq_neg_of_add_eq_zero_right hg]
      exact S.neg_mem (Submodule.sum_mem _ fun j _ => S.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩))
  have hfg : Module.Finite ℤ (E.carrier ⧸ S.toAddSubgroup) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' S.toAddSubgroup).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  have htor : Module.IsTorsion ℤ (E.carrier ⧸ S.toAddSubgroup) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective S.toAddSubgroup x
    obtain ⟨a, ha0, ha⟩ := key y
    have hN0 : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact ha0
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {a}))
    refine ⟨⟨(Ideal.absNorm (Ideal.span {a}) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN0)⟩, ?_⟩
    rw [Submonoid.smul_def]
    show ((Ideal.absNorm (Ideal.span {a}) : ℤ)) • (QuotientAddGroup.mk' S.toAddSubgroup y) = 0
    rw [← map_zsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    have e : ((Ideal.absNorm (Ideal.span {a}) : ℤ)) • y = b • (a • y) := by
      rw [smul_smul, hb, Nat.cast_smul_eq_nsmul (𝓞 K), natCast_zsmul]
    rw [e]
    exact S.smul_mem b ha
  haveI := Module.finite_of_fg_torsion _ htor
  exact AddSubgroup.index_ne_zero_of_finite

private theorem index_ne_zero_and_le_of_smul_mem {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    (F : Submodule (𝓞 K) E.carrier) {n : ℕ} (v : Fin n → E.carrier)
    (hS : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.index ≠ 0)
    (d : ℤ) (hd : d ≠ 0) (hdF : ∀ x : E.carrier, d • x ∈ F) :
    F.toAddSubgroup.index ≠ 0 ∧
      (F.toAddSubgroup.index : ℝ) ≤ (|(d : ℝ)| ^ Module.finrank ℚ K) ^ n := by
  classical
  set S := Submodule.span (𝓞 K) (Set.range v) with hSdef
  have hd' : (d : 𝓞 K) ≠ 0 := by exact_mod_cast hd
  set I : Ideal (𝓞 K) := Ideal.span {(d : 𝓞 K)} with hIdef
  have hIidx : I.toAddSubgroup.index = (d ^ Module.finrank ℚ K).natAbs := by
    rw [← Ideal.absNorm_eq_index, hIdef, Ideal.absNorm_span_singleton,
      show (d : 𝓞 K) = algebraMap ℤ (𝓞 K) d by simp, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank]
  have hIne : I.toAddSubgroup.index ≠ 0 := by
    rw [hIidx]
    exact Int.natAbs_ne_zero.mpr (pow_ne_zero _ hd)
  haveI : I.toAddSubgroup.FiniteIndex := ⟨hIne⟩
  haveI : Finite (𝓞 K ⧸ I) := I.toAddSubgroup.finite_quotient_of_finiteIndex
  haveI : Finite (E.carrier ⧸ (⊤ : Submodule (𝓞 K) E.carrier)) :=
    AddSubgroup.index_ne_zero_iff_finite.mp (by rw [Submodule.top_toAddSubgroup, AddSubgroup.index_top]; exact one_ne_zero)
  have hU : Finite (E.carrier ⧸ I • (⊤ : Submodule (𝓞 K) E.carrier)) :=
    Submodule.finite_quotient_smul I Module.Finite.fg_top
  have hUne : (I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup.index ≠ 0 :=
    AddSubgroup.index_ne_zero_iff_finite.mpr hU
  have hUF : I • (⊤ : Submodule (𝓞 K) E.carrier) ≤ F := by
    rw [Submodule.smul_le]
    intro r hr x _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    rw [mul_smul, Int.cast_smul_eq_zsmul]
    exact F.smul_mem c (hdF x)
  have hTU : I • S ≤ I • (⊤ : Submodule (𝓞 K) E.carrier) := Submodule.smul_mono le_rfl le_top
  set f := DistribMulAction.toLinearMap (𝓞 K) E.carrier (d : 𝓞 K) with hfdef
  have hfinj : Function.Injective f := smul_right_injective E.carrier hd'
  have hmapS : (I • S).toAddSubgroup = S.toAddSubgroup.map f.toAddMonoidHom := by
    rw [hIdef, Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_toAddSubgroup]
    rfl
  have hmapT : (I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup =
      (⊤ : AddSubgroup E.carrier).map f.toAddMonoidHom := by
    rw [hIdef, Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_toAddSubgroup,
      Submodule.top_toAddSubgroup]
    rfl
  have hrel : (I • S).toAddSubgroup.relIndex (I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup =
      S.toAddSubgroup.index := by
    rw [hmapS, hmapT, AddSubgroup.relIndex_map_map_of_injective _ _ hfinj,
      AddSubgroup.relIndex_top_right]
  have hT := Submodule.index_smul_le I (Finset.univ.image v) (N := S)
    (by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ])
  have hcard : (Finset.univ.image v).card ≤ n := Finset.card_image_le.trans (by simp)
  have hmul2 := AddSubgroup.relIndex_mul_index
    (show (I • S).toAddSubgroup ≤ (I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup from hTU)
  rw [hrel] at hmul2
  have hUle : (I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup.index ≤ I.toAddSubgroup.index ^ n := by
    have h1 : S.toAddSubgroup.index * (I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup.index ≤
        S.toAddSubgroup.index * I.toAddSubgroup.index ^ (Finset.univ.image v).card := by
      rw [hmul2, mul_comm]
      exact hT
    have h2 := Nat.le_of_mul_le_mul_left h1 (Nat.pos_of_ne_zero hS)
    exact h2.trans (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hIne) hcard)
  have hFU : F.toAddSubgroup.index ≤ (I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hUne) (AddSubgroup.index_dvd_of_le hUF)
  have hFne : F.toAddSubgroup.index ≠ 0 := by
    intro h
    have hdv := AddSubgroup.index_dvd_of_le
      (show (I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup ≤ F.toAddSubgroup from hUF)
    rw [h] at hdv
    exact hUne (Nat.eq_zero_of_zero_dvd hdv)
  refine ⟨hFne, ?_⟩
  have hIr : (I.toAddSubgroup.index : ℝ) = |(d : ℝ)| ^ Module.finrank ℚ K := by
    rw [hIidx, Nat.cast_natAbs, Int.cast_abs, Int.cast_pow, abs_pow]
  calc (F.toAddSubgroup.index : ℝ) ≤ ((I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup.index : ℝ) := by
        exact_mod_cast hFU
    _ ≤ (I.toAddSubgroup.index : ℝ) ^ n := by exact_mod_cast hUle
    _ = _ := by rw [hIr]

theorem normDegree_full_rank_submodule_bounds : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (F : Submodule (𝓞 K) E.carrier), E.rank F = Module.finrank (𝓞 K) E.carrier → E.normDegree F ≤ E.normDegree ⊤ ∧ ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ F) → E.normDegree ⊤ ≤ E.normDegree F + Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  intro K _ _ E F hF
  classical
  have hrF : Module.finrank (𝓞 K) F = Module.finrank (𝓞 K) E.carrier := hF
  obtain ⟨s, hs⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := F)
    (n := Module.finrank (𝓞 K) E.carrier) hrF.symm.le
  have hv : LinearIndependent (𝓞 K) (fun i => (s i : E.carrier)) := hs.map' F.subtype F.ker_subtype
  let t : Fin (Module.finrank (𝓞 K) E.carrier) → (⊤ : Submodule (𝓞 K) E.carrier) :=
    fun i => ⟨(s i : E.carrier), Submodule.mem_top⟩
  have ht : LinearIndependent (𝓞 K) t :=
    LinearIndependent.of_comp (⊤ : Submodule (𝓞 K) E.carrier).subtype hv
  have hSidx := index_span_ne_zero_of_linearIndependent E rfl _ hv
  have hSF : Submodule.span (𝓞 K) (Set.range fun i => (s i : E.carrier)) ≤ F := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (s j).2
  have hcF := card_quotient_span_eq_relIndex F s
  have hcT : Nat.card ((⊤ : Submodule (𝓞 K) E.carrier) ⧸ Submodule.span (𝓞 K) (Set.range t)) =
      (Submodule.span (𝓞 K) (Set.range fun i => (s i : E.carrier))).toAddSubgroup.index := by
    rw [card_quotient_span_eq_relIndex (⊤ : Submodule (𝓞 K) E.carrier) t, Submodule.top_toAddSubgroup,
      AddSubgroup.relIndex_top_right]
  have hmul := AddSubgroup.relIndex_mul_index
    (show (Submodule.span (𝓞 K) (Set.range fun i => (s i : E.carrier))).toAddSubgroup ≤
      F.toAddSubgroup from hSF)
  have hrelne : (Submodule.span (𝓞 K) (Set.range fun i => (s i : E.carrier))).toAddSubgroup.relIndex
      F.toAddSubgroup ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact hSidx hmul.symm
  have hFne : F.toAddSubgroup.index ≠ 0 := by
    intro h
    rw [h, mul_zero] at hmul
    exact hSidx hmul.symm
  have hdF := E.degree_eq_of_linearIndependent F hs (by rw [Fintype.card_fin]; exact hF.symm)
  have hdT : E.degree ⊤ = Real.log (Nat.card ((⊤ : Submodule (𝓞 K) E.carrier) ⧸
      Submodule.span (𝓞 K) (Set.range t))) -
      1 / 2 * ∑ σ : K →+* ℂ, Real.log (gramDet E.metric σ fun i => ((s i : F) : E.carrier)) :=
    E.degree_eq_of_linearIndependent (⊤ : Submodule (𝓞 K) E.carrier) ht
      (by rw [Fintype.card_fin]; exact (finrank_top (𝓞 K) E.carrier).symm)
  have hdiff : E.degree ⊤ = E.degree F + Real.log (F.toAddSubgroup.index : ℝ) := by
    rw [hdT, hdF, hcT, hcF, ← hmul, Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hrelne) (by exact_mod_cast hFne)]
    ring
  have hq : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hlog0 : 0 ≤ Real.log (F.toAddSubgroup.index : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hFne)
  refine ⟨?_, ?_⟩
  · unfold HermitianBundle.normDegree
    rw [hdiff]
    exact div_le_div_of_nonneg_right (by linarith) hq.le
  · intro d hd hdmem
    obtain ⟨-, hbound⟩ := index_ne_zero_and_le_of_smul_mem E F _ hSidx d hd hdmem
    have hpos : (0 : ℝ) < F.toAddSubgroup.index := by exact_mod_cast Nat.pos_of_ne_zero hFne
    have hlogb : Real.log (F.toAddSubgroup.index : ℝ) ≤
        (Module.finrank (𝓞 K) E.carrier : ℝ) * (Module.finrank ℚ K * Real.log |(d : ℝ)|) := by
      calc Real.log (F.toAddSubgroup.index : ℝ)
          ≤ Real.log ((|(d : ℝ)| ^ Module.finrank ℚ K) ^ Module.finrank (𝓞 K) E.carrier) :=
            Real.log_le_log hpos hbound
        _ = _ := by rw [Real.log_pow, Real.log_pow]
    unfold HermitianBundle.normDegree
    rw [hdiff, add_div, add_le_add_iff_left, div_le_iff₀ hq]
    linarith

end CoverDenseAlt

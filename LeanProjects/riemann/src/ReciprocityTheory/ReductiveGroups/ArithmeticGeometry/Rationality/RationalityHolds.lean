import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FiniteDimensionalBaseSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FinDetPf

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem rationality_holds : RationalityStatement := by
  intro K Ω V _ _ _ _ _ U _ W FF hWle hdef hkill hdet
  classical
  have hEfd : FiniteDimensional Ω (baseSpan Ω U) := finiteDimensional_baseSpan Ω U
  set E := baseSpan Ω U with hEdef

  let FF' : Set (Module.Dual Ω E) := (fun c => c ∘ₗ E.subtype) '' FF
  obtain ⟨s', hs'FF, hs'W⟩ := finiteDetect_holds Ω E (W.comap E.subtype) FF'
    (by rintro _ ⟨c, hc, rfl⟩ x hx; exact hkill c hc hx)
    (by
      intro x hx
      obtain ⟨c, hc, hcx⟩ := hdet x x.2 hx
      exact ⟨_, ⟨c, hc, rfl⟩, hcx⟩)
  have hpre : ∀ c' ∈ s', ∃ c ∈ FF, c ∘ₗ E.subtype = c' := fun c' hc' => hs'FF hc'
  choose! pre hpreFF hpreEq using hpre
  have hR2 : ∀ y (hy : y ∈ E), y ∈ W ↔ ∀ c' ∈ s', pre c' y = 0 := by
    intro y hy
    rw [show y ∈ W ↔ (⟨y, hy⟩ : E) ∈ W.comap E.subtype from Iff.rfl, ← hs'W]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    refine forall₂_congr fun c' hc' => ?_
    conv_lhs => rw [← hpreEq c' hc']
    rfl

  have hfld : ∀ c' ∈ s', ∃ K' : IntermediateField K Ω, FiniteDimensional K K' ∧
      DefinedOver (pre c') K' := fun c' hc' => hdef _ (hpreFF c' hc')
  choose! fld hfldfin hflddef using hfld
  let K₁ : IntermediateField K Ω := ⨆ c' : s', fld c'
  have : ∀ c' : s', FiniteDimensional K (fld c') := fun c' => hfldfin c' c'.2
  have hK₁fin : FiniteDimensional K K₁ := IntermediateField.finiteDimensional_iSup_of_finite
  have hdefK₁ : ∀ c' ∈ s', DefinedOver (pre c') K₁ := fun c' hc' =>
    (hflddef c' hc').mono (le_iSup (fun c'' : s' => fld c'') ⟨c', hc'⟩)
  have hrat : ∀ c' ∈ s', ∃ φ : Module.Dual K₁ (K₁ ⊗[K] V),
      ∀ x, algebraMap K₁ Ω (φ x) = pre c' (inclT K₁ V x) := fun c' hc' =>
    exists_ratFun (hdefK₁ c' hc')
  choose! Φ hΦ using hrat

  have hDfd : FiniteDimensional K₁ (baseSpan K₁ U) := finiteDimensional_baseSpan K₁ U
  set D := baseSpan K₁ U with hDdef
  let φ : s' → Module.Dual K₁ D := fun c' => Φ c' ∘ₗ D.subtype
  obtain ⟨t, htsub, htspan, htli⟩ := exists_linearIndependent K₁ (Set.range φ)
  have htfin : t.Finite := (Set.finite_range φ).subset htsub
  have : Fintype t := htfin.fintype
  set ρ := Fintype.card t with hρ
  let eT := Fintype.equivFin t
  have hsel : ∀ i : Fin ρ, ∃ c' : s', φ c' = (eT.symm i : Module.Dual K₁ D) :=
    fun i => htsub (eT.symm i).2
  choose sel hsel using hsel
  let cc : Fin ρ → Module.Dual Ω (Ω ⊗[K] V) := fun i => pre (sel i)
  let ph : Fin ρ → Module.Dual K₁ D := fun i => (eT.symm i : Module.Dual K₁ D)
  have hph_li : LinearIndependent K₁ ph := htli.comp eT.symm eT.symm.injective
  have hph_span : Submodule.span K₁ (Set.range ph) = Submodule.span K₁ (Set.range φ) := by
    rw [← htspan]
    congr 1
    ext f
    constructor
    · rintro ⟨i, rfl⟩; exact (eT.symm i).2
    · intro hf; exact ⟨eT ⟨f, hf⟩, by simp [ph]⟩
  have hph_cc : ∀ i (x : D), algebraMap K₁ Ω (ph i x) = cc i (inclT K₁ V x) := by
    intro i x
    show algebraMap K₁ Ω ((eT.symm i : Module.Dual K₁ D) x) = _
    rw [← hsel i]
    exact hΦ _ (sel i).2 x
  have hR1 : ∀ x : D, (∀ i, ph i x = 0) → ∀ c' ∈ s', pre c' (inclT K₁ V x) = 0 := by
    intro x hx c' hc'
    have hmem : φ ⟨c', hc'⟩ ∈ Submodule.span K₁ (Set.range ph) :=
      hph_span ▸ Submodule.subset_span ⟨_, rfl⟩
    have hker : Submodule.span K₁ (Set.range ph) ≤ LinearMap.ker (Module.Dual.eval K₁ D x) :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; simp [hx i])
    have h0 : φ ⟨c', hc'⟩ x = 0 := by simpa using hker hmem
    rw [← hΦ c' hc' x]
    simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply] at h0
    simp [h0]

  have hdescmem : ∀ x : K₁ ⊗[K] V, x ∈ descend K₁ W ↔ ∃ hx : x ∈ D, ∀ i, ph i ⟨x, hx⟩ = 0 := by
    intro x
    rw [show x ∈ descend K₁ W ↔ inclT K₁ V x ∈ W from Iff.rfl]
    constructor
    · intro hx
      have hxE : inclT K₁ V x ∈ E := hWle hx
      refine ⟨mem_baseSpan_of_inclT K₁ U x hxE, fun i => ?_⟩
      apply (algebraMap K₁ Ω).injective
      rw [hph_cc, map_zero]
      exact ((hR2 _ hxE).mp hx) _ (sel i).2
    · rintro ⟨hxD, hi⟩
      exact (hR2 _ (inclT_mem_baseSpan K₁ U x hxD)).mpr (hR1 ⟨x, hxD⟩ hi)

  let Φ1 : D →ₗ[K₁] (Fin ρ → K₁) := LinearMap.pi ph
  have hkerΦ1 : LinearMap.ker Φ1 = (Submodule.span K₁ (Set.range ph)).dualCoannihilator := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_dualCoannihilator]
    constructor
    · intro hx f hf
      have hker : Submodule.span K₁ (Set.range ph) ≤ LinearMap.ker (Module.Dual.eval K₁ D x) :=
        Submodule.span_le.mpr (by
          rintro _ ⟨i, rfl⟩
          simpa [Φ1] using congrFun hx i)
      simpa using hker hf
    · intro h
      funext i
      simpa [Φ1] using h (ph i) (Submodule.subset_span ⟨i, rfl⟩)
  have hfinD : Module.finrank K₁ D = Module.finrank K U := finrank_baseSpan K₁ U
  have hfinE : Module.finrank Ω E = Module.finrank K U := finrank_baseSpan Ω U
  have hker_rank : Module.finrank K₁ (LinearMap.ker Φ1) + ρ = Module.finrank K U := by
    have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq
      (Submodule.span K₁ (Set.range ph))
    rw [finrank_span_eq_card hph_li, Fintype.card_fin, ← hkerΦ1, hfinD] at h1
    omega
  have hΦ1surj : LinearMap.range Φ1 = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h2 := LinearMap.finrank_range_add_finrank_ker Φ1
    rw [Module.finrank_fin_fun, hfinD] at *
    omega
  have hd : ∀ j : Fin ρ, ∃ d : D, Φ1 d = Pi.single j 1 := fun j => by
    have : Pi.single j 1 ∈ LinearMap.range Φ1 := hΦ1surj ▸ Submodule.mem_top
    exact this
  choose d hd using hd
  have hphd : ∀ i j, ph i (d j) = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (hd j) i
    simp only [Φ1, LinearMap.pi_apply] at this
    rw [this, Pi.single_apply]

  have hdesc_map : descend K₁ W = (LinearMap.ker Φ1).map D.subtype := by
    ext x
    rw [hdescmem, Submodule.mem_map]
    constructor
    · rintro ⟨hx, hi⟩
      exact ⟨⟨x, hx⟩, LinearMap.mem_ker.mpr (funext fun i => by simpa [Φ1] using hi i), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun i => ?_⟩
      have := congrFun (LinearMap.mem_ker.mp hy) i
      simpa [Φ1] using this
  have hfin_desc : Module.finrank K₁ (descend K₁ W) = Module.finrank K₁ (LinearMap.ker Φ1) := by
    rw [hdesc_map, Submodule.finrank_map_subtype_eq]
  have hdesc_inf : descend K₁ W =
      D ⊓ ⨅ i, LinearMap.ker ((cc i).restrictScalars K₁ ∘ₗ inclT K₁ V) := by
    ext x
    rw [hdescmem]
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply]
    constructor
    · rintro ⟨hx, hi⟩
      refine ⟨hx, fun i => ?_⟩
      have := hph_cc i ⟨x, hx⟩
      rw [hi i, map_zero] at this
      exact this.symm
    · rintro ⟨hx, hi⟩
      refine ⟨hx, fun i => ?_⟩
      apply (algebraMap K₁ Ω).injective
      rw [hph_cc, map_zero]
      exact hi i

  set S := Submodule.span Ω (inclT K₁ V '' (descend K₁ W : Set (K₁ ⊗[K] V))) with hSdef
  have hSW : S ≤ W := Submodule.span_le.mpr (by rintro _ ⟨x, hx, rfl⟩; exact hx)
  let dd : Fin ρ → Ω ⊗[K] V := fun j => inclT K₁ V (d j)
  let Qm : (Ω ⊗[K] V) →ₗ[Ω] (Ω ⊗[K] V) := LinearMap.id - ∑ j, (cc j).smulRight (dd j)
  have hQm_apply : ∀ y, Qm y = y - ∑ j, cc j y • dd j := by
    intro y
    simp only [Qm, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
      LinearMap.smulRight_apply]
  have hQm : ∀ y ∈ E, Qm y ∈ S := by
    intro y hy
    have hle : E ≤ S.comap Qm := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨u, hu, rfl⟩
      have hxD : ((1 : K₁) ⊗ₜ[K] u) ∈ D := Submodule.subset_span ⟨u, hu, rfl⟩
      set x : D := ⟨(1 : K₁) ⊗ₜ[K] u, hxD⟩ with hxdef
      have hx1 : inclT K₁ V (x : K₁ ⊗[K] V) = (1 : Ω) ⊗ₜ[K] u := by
        simp [x, inclT_tmul']
      let m : D := x - ∑ j, ph j x • d j
      have hm : ∀ i, ph i m = 0 := by
        intro i
        simp only [m, map_sub, map_sum, map_smul, smul_eq_mul, hphd, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
      have hmdesc : (m : K₁ ⊗[K] V) ∈ descend K₁ W := (hdescmem _).mpr ⟨m.2, hm⟩
      have hval : inclT K₁ V (m : K₁ ⊗[K] V) = Qm ((1 : Ω) ⊗ₜ[K] u) := by
        rw [hQm_apply]
        simp only [m, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, map_sub, map_sum,
          map_smul]
        rw [hx1]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← hx1, ← hph_cc j x, algebraMap_smul]
      show Qm ((1 : Ω) ⊗ₜ[K] u) ∈ S
      rw [← hval]
      exact Submodule.subset_span ⟨_, hmdesc, rfl⟩
    exact hle hy
  have hWS : W ≤ S := by
    intro y hy
    have h := hQm y (hWle hy)
    have h0 : ∀ j, cc j y = 0 := fun j => LinearMap.mem_ker.mp (hkill _ (hpreFF _ (sel j).2) hy)
    rwa [hQm_apply, Finset.sum_eq_zero (fun j _ => by rw [h0 j, zero_smul]), sub_zero] at h
  have hSeq : S = W := le_antisymm hSW hWS

  have hdfd : FiniteDimensional K₁ (descend K₁ W) := by
    rw [hdesc_map]; infer_instance
  have hle1 : Module.finrank Ω W ≤ Module.finrank K₁ (descend K₁ W) := by
    let bd := Module.finBasis K₁ (descend K₁ W)
    let gen : Fin (Module.finrank K₁ (descend K₁ W)) → Ω ⊗[K] V :=
      fun k => inclT K₁ V (bd k : K₁ ⊗[K] V)
    have hsub : S ≤ Submodule.span Ω (Set.range gen) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      have hrep : x = ∑ k, bd.repr ⟨x, hx⟩ k • (bd k : K₁ ⊗[K] V) := by
        have := congrArg Subtype.val (bd.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      rw [hrep, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [map_smul, ← algebraMap_smul Ω]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    have : FiniteDimensional Ω (Submodule.span Ω (Set.range gen)) :=
      FiniteDimensional.span_of_finite Ω (Set.finite_range _)
    calc Module.finrank Ω W = Module.finrank Ω S := by rw [hSeq]
      _ ≤ Module.finrank Ω (Submodule.span Ω (Set.range gen)) := Submodule.finrank_mono hsub
      _ ≤ Fintype.card (Fin (Module.finrank K₁ (descend K₁ W))) := finrank_range_le_card _
      _ = _ := Fintype.card_fin _
  have hle2 : Module.finrank Ω E ≤ Module.finrank Ω W + ρ := by
    have hsub : E ≤ W ⊔ Submodule.span Ω (Set.range dd) := by
      intro y hy
      have h1 : Qm y ∈ W := hSW (hQm y hy)
      have h2 : ∑ j, cc j y • dd j ∈ Submodule.span Ω (Set.range dd) :=
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      have hy' : y = Qm y + ∑ j, cc j y • dd j := by rw [hQm_apply]; abel
      rw [hy']
      exact Submodule.add_mem_sup h1 h2
    have : FiniteDimensional Ω (Submodule.span Ω (Set.range dd)) :=
      FiniteDimensional.span_of_finite Ω (Set.finite_range _)
    have : FiniteDimensional Ω W := Submodule.finiteDimensional_of_le hWle
    have h3 : Module.finrank Ω (Submodule.span Ω (Set.range dd)) ≤ ρ := by
      exact (finrank_range_le_card dd).trans (Fintype.card_fin ρ).le
    calc Module.finrank Ω E ≤ Module.finrank Ω ↥(W ⊔ Submodule.span Ω (Set.range dd)) :=
          Submodule.finrank_mono hsub
      _ ≤ Module.finrank Ω ↥W + Module.finrank Ω ↥(Submodule.span Ω (Set.range dd)) :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ Module.finrank Ω W + ρ := by omega
  refine ⟨K₁, hK₁fin, ρ, cc, fun i => ⟨hpreFF _ (sel i).2, hdefK₁ _ (sel i).2⟩, hdesc_inf, hSeq,
    ?_, ?_⟩
  · rw [hfinE] at hle2
    omega
  · rw [hfin_desc]; exact hker_rank

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

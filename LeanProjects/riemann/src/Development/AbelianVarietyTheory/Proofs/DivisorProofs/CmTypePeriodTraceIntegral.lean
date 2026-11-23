import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.DetBound

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

theorem ιMulti_eq_det_smul {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {n : ℕ}
    (b : Module.Basis (Fin n) O M) (v : Fin n → M) :
    exteriorPower.ιMulti O n v = b.det v • exteriorPower.ιMulti O n b := by
  have h : exteriorPower.ιMulti O n (M := M) = b.det.smulRight (exteriorPower.ιMulti O n b) := by
    refine Module.Basis.ext_alternating b fun i hi => ?_
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i (Finite.injective_iff_bijective.1 hi)
    change exteriorPower.ιMulti O n (b ∘ σ) = b.det (b ∘ σ) • exteriorPower.ιMulti O n b
    rw [AlternatingMap.map_perm, AlternatingMap.map_perm, Module.Basis.det_self, smul_assoc, one_smul]
  exact DFunLike.congr_fun h v

theorem exists_wedge_generator {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] [Module.Free O M]
    [Module.Finite O M] {n : ℕ} (hn : Module.finrank O M = n) : ∃ ω : ⋀[O]^n M, O ∙ ω = ⊤ := by
  let b := Module.finBasisOfFinrankEq O M hn
  refine ⟨exteriorPower.ιMulti O n b, ?_⟩
  rw [eq_top_iff, ← exteriorPower.ιMulti_span O n M, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  rw [ιMulti_eq_det_smul b v]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem exists_wedge_eq_smul_dvd {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] [Module.Free O M]
    [Module.Finite O M] {n : ℕ} (hn : Module.finrank O M = n) (v : Fin n → M) (D : O)
    (hD : ∀ x : M, D • x ∈ Submodule.span O (Set.range v)) (ω : ⋀[O]^n M) (hω : O ∙ ω = ⊤) :
    ∃ u : O, exteriorPower.ιMulti O n v = u • ω ∧ u ∣ D ^ n := by
  let b := Module.finBasisOfFinrankEq O M hn
  let L := exteriorPower.alternatingMapLinearEquiv b.det
  have hL : ∀ w, L (exteriorPower.ιMulti O n w) = b.det w := fun w =>
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 (hω ▸ Submodule.mem_top : exteriorPower.ιMulti O n v ∈ O ∙ ω)
  obtain ⟨w, hw⟩ := Submodule.mem_span_singleton.1 (hω ▸ Submodule.mem_top : exteriorPower.ιMulti O n b ∈ O ∙ ω)
  have hu' : b.det v = u * L ω := by rw [← hL, ← hu, map_smul, smul_eq_mul]
  let A : M →ₗ[O] M := b.constr O v
  have hA : ∀ j, A (b j) = v j := fun j => b.constr_basis O v j
  have hAv : b.det v = LinearMap.det A := by
    have : (A ∘ b) = v := funext hA
    rw [← this, Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  have hrange : ∀ j, ∃ y, A y = D • b j := by
    intro j
    have h := hD (b j)
    rw [← b.constr_range O (f := v)] at h
    exact h
  choose y hy using hrange
  let B' : M →ₗ[O] M := b.constr O y
  have hAB : A ∘ₗ B' = D • LinearMap.id := by
    refine b.ext fun j => ?_
    simp only [LinearMap.comp_apply, B', b.constr_basis, hy, LinearMap.smul_apply, LinearMap.id_apply]
  have hdet : LinearMap.det A * LinearMap.det B' = D ^ n := by
    rw [← LinearMap.det_comp, hAB, LinearMap.det_smul, LinearMap.det_id, mul_one, hn]
  refine ⟨u, hu.symm, ⟨L ω * LinearMap.det B', ?_⟩⟩
  rw [← hdet, ← hAv, hu', mul_assoc]

theorem val_bounds_of_dvd (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K] (l : ℕ) (hl : (l : O) ≠ 0) (hlm : (l : O) ∈ IsLocalRing.maximalIdeal O) (u D : O) (n : ℕ)
    (hD : D ≠ 0) (hu : u ∣ D ^ n) :
    0 ≤ val_vp O l (algebraMap O K u) ∧ val_vp O l (algebraMap O K u) ≤ n • val_vp O l (algebraMap O K D) := by
  obtain ⟨w, hw⟩ := hu
  have hDn : D ^ n ≠ 0 := pow_ne_zero _ hD
  have hu0 : u ≠ 0 := by rintro rfl; exact hDn (by simp [hw])
  have hw0 : w ≠ 0 := by rintro rfl; exact hDn (by simp [hw])
  have hinj := IsFractionRing.injective O K
  have hne : ∀ a : O, a ≠ 0 → algebraMap O K a ≠ 0 := fun a ha => (map_ne_zero_iff _ hinj).2 ha
  have hVne : ∀ a : O, a ≠ 0 →
      (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K a) ≠ 0 := by
    intro a ha; simpa using hne a ha
  have key : ∀ a : O, a ≠ 0 → 0 ≤ ord_vw O (algebraMap O K a) := by
    intro a ha
    unfold ord_vw
    rw [neg_nonneg, WithZero.log_le_iff_le_exp (hVne a ha), WithZero.exp_zero]
    exact HeightOneSpectrum.valuation_le_one _ a
  have hmul : ord_vw O (algebraMap O K (D ^ n)) = ord_vw O (algebraMap O K u) + ord_vw O (algebraMap O K w) := by
    unfold ord_vw
    rw [hw, map_mul, Valuation.map_mul, WithZero.log_mul (hVne u hu0) (hVne w hw0), neg_add]
  have hpow : ord_vw O (algebraMap O K (D ^ n)) = n * ord_vw O (algebraMap O K D) := by
    unfold ord_vw
    rw [map_pow, Valuation.map_pow, WithZero.log_pow, nsmul_eq_mul, mul_neg]
  have hlK : (l : K) = algebraMap O K (l : O) := (map_natCast _ _).symm
  have hlpos : 0 < ord_vw O (l : K) := by
    rw [hlK]
    refine lt_of_le_of_ne (key _ hl) ?_
    intro h4
    have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K (l : O)) < 1 := by
      rw [HeightOneSpectrum.valuation_lt_one_iff_mem]; exact hlm
    unfold ord_vw at h4
    have := WithZero.exp_log (hVne _ hl)
    rw [neg_eq_zero.1 h4.symm, WithZero.exp_zero] at this
    exact h1.ne this.symm
  have hw' := key w hw0
  have hu' := key u hu0
  rw [val_vp, if_neg (hne u hu0), val_vp, if_neg (hne D hD)]
  have hL : (0 : ℚ) < (ord_vw O (l : K) : ℚ) := by exact_mod_cast hlpos
  refine ⟨WithTop.coe_nonneg.2 (div_nonneg (by exact_mod_cast hu') hL.le), ?_⟩
  rw [← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hL.le
  have : ord_vw O (algebraMap O K u) ≤ n * ord_vw O (algebraMap O K D) := by omega
  exact_mod_cast this

theorem inK_injective {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (H : Type) [AddCommGroup H] [Module O H] [Module.Free O H] : Function.Injective (inK K H (O := O)) := by
  have h : (inK K H (O := O)) = ((Algebra.linearMap O K).rTensor H) ∘ₗ (TensorProduct.lid O H).symm.toLinearMap := by
    ext h; simp [inK]
  rw [h, LinearMap.coe_comp]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective O K)).comp
    (TensorProduct.lid O H).symm.injective

theorem cmType_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K] {I : Type}
    {φ : I → E →+* K} (hφ : IsCMTypeIn φ) : Function.Injective φ := by
  intro i j h
  obtain ⟨k, _, hk⟩ := hφ (φ i)
  exact (hk i (Or.inl rfl)).trans (hk j (Or.inl h)).symm

theorem gens_mem_linearIndependent {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K]
    [IsFractionRing O K] {D : O} {I : Type} [Fintype I] {φ : I → E →+* K} (hφ : IsCMTypeIn φ)
    {H : Type} [AddCommGroup H] [Module O H] {ρ : orderC c →+* Module.End O H} {Fil : Submodule O H}
    {B : LinearMap.BilinForm O H} (hL : IsCMLattice φ ρ Fil B) (hE : EigenClaims φ ρ Fil B D) {e f : I → H}
    (hG : IsGens φ ρ e f) : (∀ i, e i ∈ Fil) ∧ LinearIndependent O e := by
  haveI : Module.Free O H := hL.1
  have hself : ∀ i, e i ∈ eigLat (K := K) ρ (φ i) := fun i => (hG i).1 ▸ Submodule.mem_span_singleton_self _
  refine ⟨fun i => ?_, ?_⟩
  · have h := hE.2.2.2.1 i
    exact (inf_eq_right.1 h) (hself i)
  · have hi : iSupIndep (fun σ : E →+* K => eigLat (K := K) ρ σ) := hE.2.2.1.1
    refine iSupIndep.linearIndependent _ (hi.comp (cmType_injective hφ)) hself ?_
    intro i h0
    obtain ⟨g, hg, hgs⟩ := (hE.2.1 (φ i)).2.1
    have : g ∈ eigLat (K := K) ρ (φ i) := hgs ▸ Submodule.mem_span_singleton_self _
    rw [(hG i).1, h0, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at this
    exact hg this

theorem smul_mem_span_gens {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K]
    [IsFractionRing O K] {D : O} {I : Type} [Fintype I] {φ : I → E →+* K} (hφ : IsCMTypeIn φ)
    {H : Type} [AddCommGroup H] [Module O H] {ρ : orderC c →+* Module.End O H} {Fil : Submodule O H}
    {B : LinearMap.BilinForm O H} (hL : IsCMLattice φ ρ Fil B) (hE : EigenClaims φ ρ Fil B D) {e f : I → H}
    (hG : IsGens φ ρ e f) (e' : I → Fil) (he' : ∀ i, (e' i : H) = e i) (x : Fil) :
    D • x ∈ Submodule.span O (Set.range e') := by
  haveI : Module.Free O H := hL.1
  have hind : iSupIndep (fun σ : E →+* K => eigK ρ σ) := hE.1.submodule_iSupIndep
  have hxK : inK (O := O) K H (D • (x : H)) ∈ ⨆ i, eigK ρ (φ i) := by
    rw [← hL.2.2.2.2.2.1]
    exact Submodule.tmul_mem_baseChange_of_mem 1 (Fil.smul_mem D x.2)
  obtain ⟨F, hF, hFs⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 (hE.2.2.1.2 (x : H))
  have hzero : ∀ σ, σ ∉ Set.range φ → F σ = 0 := by
    intro σ₀ hσ₀
    apply inK_injective (O := O) K H
    rw [map_zero]
    have h1 : inK (O := O) K H (F σ₀) ∈ eigK ρ σ₀ := hF σ₀
    have h2 : inK (O := O) K H (F σ₀) ∈ ⨆ (j : E →+* K) (_ : j ≠ σ₀), eigK ρ j := by
      have hsum : inK (O := O) K H (F σ₀) = inK (O := O) K H (D • (x : H)) - ∑ σ ∈ F.support.erase σ₀, inK (O := O) K H (F σ) := by
        rw [← hFs, Finsupp.sum, map_sum]
        by_cases hm : σ₀ ∈ F.support
        · rw [← Finset.add_sum_erase _ _ hm, add_sub_cancel_right]
        · rw [Finsupp.notMem_support_iff.1 hm, map_zero, Finset.erase_eq_of_notMem hm, sub_self]
      rw [hsum]
      refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun σ hσ => ?_)
      · have hle : (⨆ i, eigK ρ (φ i)) ≤ ⨆ (j : E →+* K) (_ : j ≠ σ₀), eigK ρ j := iSup_le fun i =>
          le_iSup₂_of_le (f := fun (j : E →+* K) (_ : j ≠ σ₀) => eigK ρ j) (φ i) (fun h => hσ₀ ⟨i, h⟩) le_rfl
        exact hle hxK
      · exact (le_iSup₂_of_le (f := fun (j : E →+* K) (_ : j ≠ σ₀) => eigK ρ j) σ
          (Finset.ne_of_mem_erase hσ) le_rfl) (hF σ)
    exact Submodule.disjoint_def.1 (hind σ₀) _ h1 h2
  have hH : D • (x : H) ∈ Submodule.span O (Set.range e) := by
    rw [← hFs, Finsupp.sum]
    refine Submodule.sum_mem _ fun σ _ => ?_
    by_cases hσ : σ ∈ Set.range φ
    · obtain ⟨i, rfl⟩ := hσ
      have h := hF (φ i)
      rw [(hG i).1, Submodule.mem_span_singleton] at h
      obtain ⟨a, ha⟩ := h
      rw [← ha]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [hzero σ hσ]; exact Submodule.zero_mem _
  have hspan : Submodule.span O (Set.range e) = (Submodule.span O (Set.range e')).map Fil.subtype := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    exact (he' i).symm
  rw [hspan] at hH
  obtain ⟨y, hy, hyx⟩ := hH
  have : y = D • x := Subtype.ext hyx
  exact this ▸ hy

theorem detClaims : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → DetClaims K l Fil D e := by
  intro E _ _ _ c _ l hl O _ _ _ _ K _ _ _ hlm _ D hD _ I _ φ hφ H _ _ ρ Fil B hL hE e f hG
  haveI : Module.Free O H := hL.1
  haveI : Module.Finite O H := hL.2.1
  obtain ⟨hmem, hli⟩ := gens_mem_linearIndependent hφ hL hE hG
  let e₀ : I → Fil := fun i => ⟨e i, hmem i⟩
  have he₀ : ∀ i, (e₀ i : H) = e i := fun i => rfl
  have hli₀ : LinearIndependent O e₀ := LinearIndependent.of_comp Fil.subtype hli
  have hrank : Module.finrank O Fil = Fintype.card I := by
    apply le_antisymm
    · let g : Fil →ₗ[O] Submodule.span O (Set.range e₀) :=
        ((LinearMap.lsmul O Fil D).codRestrict _ (fun x => smul_mem_span_gens hφ hL hE hG e₀ he₀ x))
      have hg : Function.Injective g := by
        intro x y hxy
        have : D • x = D • y := congrArg Subtype.val hxy
        exact smul_right_injective _ hD this
      exact (LinearMap.finrank_le_finrank_of_injective hg).trans (finrank_range_le_card e₀)
    · exact hli₀.fintype_card_le_finrank
  refine ⟨inferInstance, hrank, hmem, exists_wedge_generator hrank, ?_⟩
  intro ω hω s e' he'
  obtain ⟨u, hu, hdvd⟩ := exists_wedge_eq_smul_dvd hrank (fun j => e' (s j)) D (by
    intro x
    have h := smul_mem_span_gens hφ hL hE hG e' he' x
    have : Set.range (fun j => e' (s j)) = Set.range e' := s.surjective.range_comp e'
    rw [this]; exact h) ω hω
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  exact ⟨u, hu, val_bounds_of_dvd O K l hl0 hlm u D _ hD hdvd⟩

end GlobalTheory.DetBound

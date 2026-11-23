import Mathlib

namespace DualFramesAlt.SatDVR

noncomputable def toK (O K : Type*) [CommRing O] [Field K] [Algebra O K] (r : ℕ) :
    (Fin r → O) →ₗ[O] (Fin r → K) :=
  LinearMap.pi fun i => (Algebra.linearMap O K).comp (LinearMap.proj i)

section SlopeTestRemainingChoices

variable {O K : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  {r : ℕ}

lemma toK_apply (x : Fin r → O) (i : Fin r) : toK O K r x i = algebraMap O K (x i) := rfl

lemma toK_injective : Function.Injective (toK O K r) := by
  intro x y h
  funext i
  exact IsFractionRing.injective O K (congr_fun h i)

lemma algebraMap_ne_zero {a : O} (ha : a ≠ 0) : algebraMap O K a ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 ha

lemma exists_toK_eq_smul (y : Fin r → K) :
    ∃ d : O, d ≠ 0 ∧ ∃ x : Fin r → O, toK O K r x = algebraMap O K d • y := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) y
  choose x hx using hb
  refine ⟨b, nonZeroDivisors.ne_zero b.2, x, ?_⟩
  funext i
  rw [toK_apply, hx i, Pi.smul_apply, Algebra.smul_def, smul_eq_mul]

lemma le_span_comap (W : Submodule K (Fin r → K)) :
    W ≤ Submodule.span K (toK O K r '' ((W.restrictScalars O).comap (toK O K r) : Set _)) := by
  intro y hy
  obtain ⟨d, hd, x, hx⟩ := exists_toK_eq_smul (O := O) y
  have hxW : x ∈ (W.restrictScalars O).comap (toK O K r) := by
    rw [Submodule.mem_comap, Submodule.restrictScalars_mem, hx]
    exact W.smul_mem _ hy
  have hy' : y = (algebraMap O K d)⁻¹ • toK O K r x := by
    rw [hx, smul_smul, inv_mul_cancel₀ (algebraMap_ne_zero hd), one_smul]
  rw [hy']
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hxW, rfl⟩)

variable [IsPrincipalIdealRing O]

lemma finrank_le_finrank_span (N : Submodule O (Fin r → O)) :
    Module.finrank O N ≤ Module.finrank K (Submodule.span K (toK O K r '' (N : Set _))) := by
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin r)) N
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hker : LinearMap.ker ((toK O K r).comp N.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (toK_injective (K := K)).comp Subtype.val_injective
  have hli : LinearIndependent O (((toK O K r).comp N.subtype) ∘ b) :=
    b.linearIndependent.map' ((toK O K r).comp N.subtype) hker
  have hK : LinearIndependent K (((toK O K r).comp N.subtype) ∘ b) :=
    LinearIndependent.localization K (nonZeroDivisors O) hli
  have h := finrank_span_eq_card hK
  rw [Fintype.card_fin] at h
  rw [← h]
  apply Submodule.finrank_mono
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨_, (b i).2, rfl⟩

lemma finrank_span_le_finrank (N : Submodule O (Fin r → O)) :
    Module.finrank K (Submodule.span K (toK O K r '' (N : Set _))) ≤ Module.finrank O N := by
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin r)) N
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hsp : Submodule.span K (toK O K r '' (N : Set _)) =
      Submodule.span K (Set.range fun i => toK O K r (b i : Fin r → O)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : (⟨x, hx⟩ : N) ∈ Submodule.span O (Set.range b) := by
        rw [b.span_eq]; exact Submodule.mem_top
      have h1 : x ∈ Submodule.span O (Set.range fun i => (b i : Fin r → O)) := by
        have := Submodule.mem_map_of_mem (f := N.subtype) hx'
        rwa [Submodule.map_span, ← Set.range_comp] at this
      have h2 := Submodule.mem_map_of_mem (f := toK O K r) h1
      rw [Submodule.map_span, ← Set.range_comp] at h2
      exact Submodule.span_le_restrictScalars O K _ h2
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨_, (b i).2, rfl⟩
  rw [hsp]
  exact (finrank_range_le_card _).trans (by simp)

end SlopeTestRemainingChoices

lemma exists_isCompl_of_sat {O : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M]
    (N : Submodule O M) (hsat : ∀ (a : O) (x : M), a ≠ 0 → a • x ∈ N → x ∈ N) :
    ∃ N₂ : Submodule O M, IsCompl N N₂ := by
  have : Module.IsTorsionFree O (M ⧸ N) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro a q h
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
        rw [Submodule.Quotient.mk_eq_zero]
        exact hsat a x ha h
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id
    (Submodule.mkQ_surjective N)
  let g : M →ₗ[O] M := LinearMap.id - s ∘ₗ N.mkQ
  have hg : ∀ x, g x ∈ N := by
    intro x
    have h1 : N.mkQ (s (N.mkQ x)) = N.mkQ x := LinearMap.congr_fun hs (N.mkQ x)
    have h2 : N.mkQ (g x) = 0 := by
      simp only [g, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1,
        sub_self]
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  refine ⟨LinearMap.ker (g.codRestrict N hg), LinearMap.isCompl_of_proj fun x => ?_⟩
  apply Subtype.ext
  have hx : N.mkQ (x : M) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact x.2
  simp [g, hx]

lemma exists_isCompl_finrank_add_of_saturated_of_isPrincipalIdealRing {O : Type*} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] {r : ℕ} (L' : Submodule O (Fin r → O))
    (hsat : ∀ (a : O) (x : Fin r → O), a ≠ 0 → a • x ∈ L' → x ∈ L') :
    ∃ L₂ : Submodule O (Fin r → O), IsCompl L' L₂ ∧
      Module.finrank O L₂ + Module.finrank O L' = r := by
  obtain ⟨L₂, h⟩ := exists_isCompl_of_sat L' hsat
  refine ⟨L₂, h, ?_⟩
  have h1 := Submodule.finrank_quotient_add_finrank L'
  rw [Module.finrank_fin_fun] at h1
  rw [← (Submodule.quotientEquivOfIsCompl L' L₂ h).finrank_eq]
  exact h1

lemma saturated_comap_coordinateMap_of_isPrincipalIdealRing {O K : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] {r : ℕ} (W : Submodule K (Fin r → K)) :
    (∀ (a : O) (x : Fin r → O), a ≠ 0 → a • x ∈ (W.restrictScalars O).comap (toK O K r) →
        x ∈ (W.restrictScalars O).comap (toK O K r)) ∧
      Module.finrank O ((W.restrictScalars O).comap (toK O K r)) ≤ Module.finrank K W := by
  refine ⟨fun a x ha h => ?_, ?_⟩
  · rw [Submodule.mem_comap, Submodule.restrictScalars_mem, map_smul,
      ← algebraMap_smul K a] at h
    rw [Submodule.mem_comap, Submodule.restrictScalars_mem]
    have := W.smul_mem (algebraMap O K a)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ (algebraMap_ne_zero ha), one_smul] at this
  · refine (finrank_le_finrank_span (K := K) _).trans (Submodule.finrank_mono ?_)
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx

theorem decomp {O K : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] {r m : ℕ} {ι₁ ι₂ : Type*}
    [Fintype ι₁] [Fintype ι₂]
    (C : ι₁ → Submodule K (Fin r → K)) (hC : ∀ τ, r ≤ Module.finrank K (C τ) + m)
    (F : ι₂ → Submodule K (Fin r → K)) (hF : ∀ τ, Module.finrank K (F τ) ≤ m) :
    ∃ L'' Lrest : Submodule O (Fin r → O), IsCompl L'' Lrest ∧
      Module.finrank O Lrest ≤ (Fintype.card ι₁ + Fintype.card ι₂) * m ∧
      (∀ τ, ∀ x ∈ L'', toK O K r x ∈ C τ) ∧
      (∀ τ, F τ ≤ Submodule.span K (toK O K r '' (Lrest : Set (Fin r → O)))) := by
  classical

  set W : Submodule K (Fin r → K) := ⨅ τ, C τ with hWdef
  set V : Submodule K (Fin r → K) := ⨆ τ, F τ with hVdef
  have hW : r ≤ Module.finrank K W + Fintype.card ι₁ * m := by
    let φ : (Fin r → K) →ₗ[K] ((τ : ι₁) → (Fin r → K) ⧸ C τ) := LinearMap.pi fun τ => (C τ).mkQ
    have hker : LinearMap.ker φ = W := by
      rw [LinearMap.ker_pi]
      simp only [Submodule.ker_mkQ, hWdef]
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    rw [hker, Module.finrank_fin_fun] at h1
    have h2 : Module.finrank K (LinearMap.range φ) ≤ Fintype.card ι₁ * m := by
      refine (Submodule.finrank_le _).trans ?_
      rw [Module.finrank_pi_fintype]
      calc ∑ τ, Module.finrank K ((Fin r → K) ⧸ C τ) ≤ ∑ _τ : ι₁, m := by
            refine Finset.sum_le_sum fun τ _ => ?_
            have h3 := Submodule.finrank_quotient_add_finrank (C τ)
            rw [Module.finrank_fin_fun] at h3
            have h4 := hC τ
            omega
        _ = Fintype.card ι₁ * m := by simp
    omega

  have hV : Module.finrank K V ≤ Fintype.card ι₂ * m := by
    have key : ∀ s : Finset ι₂, Module.finrank K ↥(s.sup F) ≤ s.card * m := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sup_insert, Finset.card_insert_of_notMem ha]
        calc Module.finrank K ↥(F a ⊔ s.sup F)
            ≤ Module.finrank K ↥(F a) + Module.finrank K ↥(s.sup F) :=
              Submodule.finrank_add_le_finrank_add_finrank _ _
          _ ≤ m + s.card * m := add_le_add (hF a) ih
          _ = (s.card + 1) * m := by ring
    have hVs : V = Finset.univ.sup F := by rw [hVdef, Finset.sup_univ_eq_iSup]
    rw [hVs]
    simpa using key Finset.univ

  obtain ⟨hsat', -⟩ := saturated_comap_coordinateMap_of_isPrincipalIdealRing (O := O) W
  have hrkL' : Module.finrank K W ≤ Module.finrank O ((W.restrictScalars O).comap (toK O K r)) :=
    (Submodule.finrank_mono (le_span_comap (O := O) W)).trans (finrank_span_le_finrank _)
  obtain ⟨L₂, hc, hrk2⟩ := exists_isCompl_finrank_add_of_saturated_of_isPrincipalIdealRing _ hsat'
  set L' := (W.restrictScalars O).comap (toK O K r) with hL'

  set Y : Submodule K (Fin r → K) := V ⊔ Submodule.span K (toK O K r '' (L₂ : Set _)) with hYdef
  obtain ⟨hsatS, hrkS⟩ := saturated_comap_coordinateMap_of_isPrincipalIdealRing (O := O) Y
  set S := (Y.restrictScalars O).comap (toK O K r) with hS
  let N : Submodule O L' := S.comap L'.subtype
  have hsatN : ∀ (a : O) (x : L'), a ≠ 0 → a • x ∈ N → x ∈ N :=
    fun a x ha h => hsatS a x ha h
  obtain ⟨N₂, hN⟩ := exists_isCompl_of_sat N hsatN
  refine ⟨N₂.map L'.subtype, S, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hxS
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
    have hyN : y ∈ N := hxS
    have := Submodule.disjoint_def.1 hN.disjoint y hyN hy
    simp [this]
  · rw [codisjoint_iff, eq_top_iff]
    rintro x -
    have hx : x ∈ L' ⊔ L₂ := hc.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    have ha' : (⟨a, ha⟩ : L') ∈ N ⊔ N₂ := hN.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨n, hn, n₂, hn₂, hnn⟩ := Submodule.mem_sup.1 ha'
    have hbS : b ∈ S := by
      rw [hS, Submodule.mem_comap, Submodule.restrictScalars_mem]
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩)
    have hnS : (n : Fin r → O) ∈ S := hn
    have hsum : a + b = (n₂ : Fin r → O) + ((n : Fin r → O) + b) := by
      have h5 := congrArg Subtype.val hnn
      simp only [Submodule.coe_add] at h5
      rw [← h5]
      abel
    rw [hsum]
    exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hn₂) (S.add_mem hnS hbS)
  · have h1 : Module.finrank K Y ≤ Module.finrank K V +
        Module.finrank K (Submodule.span K (toK O K r '' (L₂ : Set _))) :=
      Submodule.finrank_add_le_finrank_add_finrank _ _
    have h2 := finrank_span_le_finrank (K := K) L₂
    rw [add_mul]
    generalize Fintype.card ι₁ * m = A at *
    generalize Fintype.card ι₂ * m = B at *
    omega
  · intro τ x hx
    obtain ⟨y, -, rfl⟩ := Submodule.mem_map.1 hx
    have hy : toK O K r (y : Fin r → O) ∈ W := y.2
    exact (iInf_le C τ) hy
  · intro τ
    calc F τ ≤ V := le_iSup F τ
      _ ≤ Y := le_sup_left
      _ ≤ _ := le_span_comap (O := O) Y

end DualFramesAlt.SatDVR

import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem fin_quot (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] (n : ℕ) (h : Module.rank A B ≤ n) :
    Module.Finite A (B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) := by
  classical
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hnzd : ∀ (c : A) (x : B), c ≠ 0 → c • x = 0 → x = 0 := by
    intro c x hc hx
    rw [Algebra.smul_def] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd ((map_eq_zero_iff _ hinj).mp h) hc
    · exact h
  have hbound : ∀ s : Finset (B ⧸ (maximalIdeal A • ⊤ : Submodule A B)),
      LinearIndependent (A ⧸ maximalIdeal A) (fun i : s => (i : B ⧸ (maximalIdeal A • ⊤ : Submodule A B))) →
      s.card ≤ n := by
    intro s hs
    have hlift : ∀ i : s, ∃ b : B,
        Submodule.Quotient.mk (p := (maximalIdeal A • ⊤ : Submodule A B)) b = (i : B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) :=
      fun i => Submodule.Quotient.mk_surjective _ _
    choose b hb using hlift
    have hli : LinearIndependent A b := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      by_contra hne
      push_neg at hne
      obtain ⟨i0, hi0⟩ := hne
      obtain ⟨j, hj, hjmin⟩ := (Finset.univ.filter (fun i => c i ≠ 0)).exists_min_image
        (fun i => IsDiscreteValuationRing.addVal A (c i)) ⟨i0, by simpa using hi0⟩
      have hcj : c j ≠ 0 := by simpa using hj
      have hdvd : ∀ i, c j ∣ c i := by
        intro i
        by_cases hci : c i = 0
        · rw [hci]; exact dvd_zero _
        · exact IsDiscreteValuationRing.addVal_le_iff_dvd.mp (hjmin i (by simpa using hci))
      choose d hd using hdvd
      have hsum : c j • ∑ i, d i • b i = 0 := by
        rw [Finset.smul_sum]
        simp_rw [smul_smul, ← hd]
        exact hc
      have hsum' : ∑ i, d i • b i = 0 := hnzd _ _ hcj hsum
      have hdj : d j = 1 := by
        have h1 : c j * d j = c j * 1 := by rw [mul_one, ← hd j]
        exact mul_left_cancel₀ hcj h1
      have hk : ∑ i, Ideal.Quotient.mk (maximalIdeal A) (d i) •
          (i : B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) = 0 := by
        have h2 := congrArg (Submodule.mkQ (maximalIdeal A • ⊤ : Submodule A B)) hsum'
        simp only [map_sum, map_zero, map_smul, Submodule.mkQ_apply] at h2
        rw [← h2]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hb i]
        rfl
      have h3 := Fintype.linearIndependent_iff.mp hs _ hk j
      rw [hdj, map_one] at h3
      exact one_ne_zero h3
    have h4 := hli.cardinal_le_rank
    rw [Cardinal.mk_coe_finset] at h4
    exact_mod_cast h4.trans h
  have hrank : Module.rank (A ⧸ maximalIdeal A) (B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) ≤ n :=
    rank_le hbound
  haveI : Module.Finite (A ⧸ maximalIdeal A) (B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) :=
    Module.rank_lt_aleph0_iff.mp (hrank.trans_lt (Cardinal.nat_lt_aleph0 n))
  exact Module.Finite.trans (A ⧸ maximalIdeal A) _

private theorem haus (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)] [Algebra.IsAlgebraic A B] :
    IsHausdorff (maximalIdeal A) B := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  refine ⟨fun x hx => ?_⟩
  by_contra hx0
  have hmem : ∀ n : ℕ, ∃ b : B, algebraMap A B (ϖ ^ n) * b = x := by
    intro n
    have h1 := (SModEq.zero).mp (hx n)
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨b, _, hb⟩ := h1
    exact ⟨b, by rw [← hb, Algebra.smul_def]⟩
  have hne := Ideal.comap_ne_bot_of_algebraic_mem hx0 (Ideal.mem_span_singleton_self x)
    (Algebra.IsAlgebraic.isAlgebraic (R := A) x)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, hc⟩ := ha
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨b, hb⟩ := hmem (k + 1)
  have e : algebraMap A B (ϖ ^ k) * algebraMap A B (u : A)
      = algebraMap A B (ϖ ^ k) * (algebraMap A B ϖ * (b * c)) := by
    rw [← map_mul, mul_comm (ϖ ^ k), ← hu, ← hc, ← hb, pow_succ, map_mul]
    ring
  have hpk : algebraMap A B (ϖ ^ k) ≠ 0 := by
    rw [← map_zero (algebraMap A B)]
    exact fun h => pow_ne_zero k hϖ.ne_zero (hinj h)
  have e2 := mul_left_cancel₀ hpk e
  have hunit : IsUnit (algebraMap A B ϖ) :=
    isUnit_of_mul_isUnit_left (e2 ▸ (u.isUnit.map (algebraMap A B)))
  exact hϖ.not_isUnit ((isUnit_map_iff (algebraMap A B) ϖ).mp hunit)

private theorem key (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [CommRing B] [IsDomain B] [ValuationRing B]
    [Algebra A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)] [Algebra.IsAlgebraic A B]
    (n : ℕ) (h : Module.rank A B ≤ n) (hf : Finite (ResidueField A)) :
    ∃ _ : IsDiscreteValuationRing B, IsAdicComplete (maximalIdeal B) B ∧ Finite (ResidueField B) := by
  haveI : IsHausdorff (maximalIdeal A) B := haus A B
  haveI : Module.Finite A (B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) := fin_quot A B n h
  haveI : Module.Finite A B := GlobalTheory.finite_of_isHausdorff_of_finite_quotient (maximalIdeal A) B
  haveI : IsNoetherianRing B := isNoetherian_of_tower A inferInstance
  have hnf : ¬ IsField B := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
    intro hF
    have h0 : algebraMap A B ϖ ≠ 0 := by
      rw [← map_zero (algebraMap A B)]
      exact fun e => hϖ.ne_zero (FaithfulSMul.algebraMap_injective A B e)
    obtain ⟨y, hy⟩ := hF.mul_inv_cancel h0
    have hu : IsUnit (algebraMap A B ϖ) := ⟨⟨_, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
    exact hϖ.not_isUnit ((isUnit_map_iff (algebraMap A B) ϖ).mp hu)
  haveI hd : IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B hnf).out 1 0).mp (inferInstance : ValuationRing B)
  exact ⟨hd, GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite A B,
    IsLocalRing.ResidueField.finite_of_finite hf⟩

theorem UpperTheory.V.Ws.smallExt :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (f : A →+* 𝔞.V), 𝔞.IsDvr f →
      ∀ s : Finset 𝔞.K, ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A') (f' : A' →+* 𝔞.V) (g : A →+* A'),
        𝔞.IsDvr f' ∧ f'.comp g = f ∧ ∀ x : 𝔞.V, (x : 𝔞.K) ∈ Subfield.closure (Set.range (𝔞.toK.comp f) ∪ s) → x ∈ f'.range := by
  intro l _ 𝔞 A _ _ _ f hf s
  classical
  have hinjK : Function.Injective (𝔞.toK.comp f) := fun a b h => hf.inj (Subtype.val_injective h)
  let E := FractionRing A
  let φ : E →+* 𝔞.K := IsFractionRing.lift hinjK
  letI : Algebra E 𝔞.K := φ.toAlgebra
  letI : Algebra A 𝔞.K := (𝔞.toK.comp f).toAlgebra
  haveI : IsScalarTower A E 𝔞.K :=
    IsScalarTower.of_algebraMap_eq (fun a => (IsFractionRing.lift_algebraMap hinjK a).symm)
  have hint : ∀ x ∈ (s : Set 𝔞.K), IsIntegral E x := by
    intro x _
    obtain ⟨p, hp0, hp⟩ := hf.alg x
    refine IsAlgebraic.isIntegral ⟨p.map (algebraMap A E), ?_, ?_⟩
    · exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective A E)).mpr hp0
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq]
      exact hp
  let L' : IntermediateField E 𝔞.K := IntermediateField.adjoin E (s : Set 𝔞.K)
  haveI : FiniteDimensional E L' := IntermediateField.finiteDimensional_adjoin hint
  have hcl : ∀ y ∈ Subfield.closure (Set.range (𝔞.toK.comp f) ∪ ↑s), y ∈ L' := by
    intro y hy
    have hle : Subfield.closure (Set.range (𝔞.toK.comp f) ∪ ↑s) ≤ L'.toSubfield := by
      rw [Subfield.closure_le]
      rintro z (⟨a, rfl⟩ | hz)
      · show (𝔞.toK.comp f) a ∈ L'
        have e : (𝔞.toK.comp f) a = algebraMap E 𝔞.K (algebraMap A E a) :=
          (IsFractionRing.lift_algebraMap hinjK a).symm
        rw [e]
        exact L'.algebraMap_mem _
      · exact IntermediateField.subset_adjoin E _ hz
    exact hle hy
  let B : Subring 𝔞.V := Subring.comap 𝔞.toK L'.toSubfield.toSubring
  have hBext : ∀ x y : B, ((x : 𝔞.V) : 𝔞.K) = ((y : 𝔞.V) : 𝔞.K) → x = y :=
    fun x y h => Subtype.ext (Subtype.ext h)
  have hBmem : ∀ x : B, ((x : 𝔞.V) : 𝔞.K) ∈ L' := fun x => x.2
  let g : A →+* B := f.codRestrict B (fun a => by
    have := hcl ((𝔞.toK.comp f) a) (Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
    exact this)
  have hgi : Function.Injective g := fun a b h => hf.inj (congrArg Subtype.val h)
  letI : Algebra A B := g.toAlgebra
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hgi
  haveI : IsLocalHom (algebraMap A B) := ⟨fun a ha => by
    haveI := hf.loc
    exact (isUnit_map_iff f a).mp (ha.map B.subtype)⟩
  have hdvd : ∀ a b : B, a ∣ b ∨ b ∣ a := by
    intro a b
    by_cases ha : ((a : 𝔞.V) : 𝔞.K) = 0
    · right
      exact ⟨0, hBext _ _ (by simp [ha])⟩
    by_cases hb : ((b : 𝔞.V) : 𝔞.K) = 0
    · left
      exact ⟨0, hBext _ _ (by simp [hb])⟩
    have hq : ((b : 𝔞.V) : 𝔞.K) / ((a : 𝔞.V) : 𝔞.K) ∈ L' := L'.div_mem (hBmem b) (hBmem a)
    rcases 𝔞.V.mem_or_inv_mem (((b : 𝔞.V) : 𝔞.K) / ((a : 𝔞.V) : 𝔞.K)) with hv | hv
    · left
      refine ⟨⟨⟨_, hv⟩, hq⟩, hBext _ _ ?_⟩
      show ((b : 𝔞.V) : 𝔞.K) = ((a : 𝔞.V) : 𝔞.K) * (((b : 𝔞.V) : 𝔞.K) / ((a : 𝔞.V) : 𝔞.K))
      field_simp
    · right
      refine ⟨⟨⟨_, hv⟩, L'.inv_mem hq⟩, hBext _ _ ?_⟩
      show ((a : 𝔞.V) : 𝔞.K) = ((b : 𝔞.V) : 𝔞.K) * (((b : 𝔞.V) : 𝔞.K) / ((a : 𝔞.V) : 𝔞.K))⁻¹
      field_simp
  haveI : ValuationRing B := ValuationRing.iff_dvd_total.mpr ⟨hdvd⟩
  haveI : Algebra.IsAlgebraic A B := ⟨fun x => by
    obtain ⟨p, hp0, hp⟩ := hf.alg ((x : 𝔞.V) : 𝔞.K)
    refine ⟨p, hp0, ?_⟩
    have e : (𝔞.toK.comp B.subtype) (Polynomial.aeval x p) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
      exact hp
    exact hBext _ _ e⟩
  haveI : IsAdicComplete (maximalIdeal A) A := hf.complete
  let ψ : B →ₗ[A] L' :=
    { toFun := fun x => ⟨((x : 𝔞.V) : 𝔞.K), hBmem x⟩
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }
  have hψ : Function.Injective ψ := fun x y h => hBext x y (by
    have h' := congrArg (fun z : L' => (z : 𝔞.K)) h
    exact h')
  have hrank : Module.rank A B ≤ (Module.finrank E L' : ℕ) := by
    calc Module.rank A B ≤ Module.rank A L' := LinearMap.rank_le_of_injective ψ hψ
      _ = Module.rank E L' := (IsFractionRing.rank_right_eq A E L').symm
      _ = Module.finrank E L' := (Module.finrank_eq_rank E L').symm
  obtain ⟨hd, hc, hfin⟩ := key A B (Module.finrank E L') hrank hf.fin
  refine ⟨B, inferInstance, inferInstance, hd, B.subtype, g, ?_, RingHom.ext fun a => rfl, ?_⟩
  · refine ⟨Subtype.val_injective, ⟨fun x hx => ?_⟩, hc, hfin, fun x => ?_⟩
    · obtain ⟨u, hu⟩ := hx
      have hu' : (u : 𝔞.V) = x := hu
      have hxy : ((x : 𝔞.V) : 𝔞.K) * (((u⁻¹ : 𝔞.Vˣ) : 𝔞.V) : 𝔞.K) = 1 := by
        rw [← hu']
        exact congrArg Subtype.val u.mul_inv
      have hmem : (((u⁻¹ : 𝔞.Vˣ) : 𝔞.V) : 𝔞.K) ∈ L' := by
        rw [eq_inv_of_mul_eq_one_right hxy]
        exact L'.inv_mem (hBmem x)
      exact ⟨⟨x, ⟨_, hmem⟩, hBext _ _ hxy, hBext _ _ (by rw [mul_comm]; exact hxy)⟩, rfl⟩
    · obtain ⟨p, hp0, hp⟩ := hf.alg x
      refine ⟨p.map g, (Polynomial.map_ne_zero_iff hgi).mpr hp0, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hp
  · intro x hx
    exact RingHom.mem_range.mpr ⟨⟨x, hcl _ hx⟩, rfl⟩

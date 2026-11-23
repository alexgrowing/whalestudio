import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.ActU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.PowEqOneOfDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem ofMul_mem_mt_iff_exists_pow_mul_finOrder {F : Type} [Field F] (l : ℕ) (α : Fˣ) :
    Additive.ofMul α ∈ Ct.mt (Additive Fˣ) l ↔ ∃ w t : Fˣ, IsOfFinOrder t ∧ α = w ^ l * t := by
  unfold Ct.mt
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨y, ⟨w, rfl⟩, z, hz, h⟩
    rw [Submodule.mem_torsion_iff] at hz
    obtain ⟨⟨a, ha⟩, haz⟩ := hz
    refine ⟨Additive.toMul w, Additive.toMul z, ?_, ?_⟩
    · rw [isOfFinOrder_iff_zpow_eq_one]
      refine ⟨a, fun h0 => ?_, ?_⟩
      · subst h0
        exact zero_notMem_nonZeroDivisors ha
      · have := congrArg Additive.toMul haz
        simpa using this
    · have := congrArg Additive.toMul h
      simpa using this.symm
  · rintro ⟨w, t, ht, rfl⟩
    refine ⟨Additive.ofMul (w ^ l), ⟨Additive.ofMul w, ?_⟩, Additive.ofMul t, ?_, ?_⟩
    · simp
    · rw [Submodule.mem_torsion_iff]
      obtain ⟨n, hn, hn1⟩ := isOfFinOrder_iff_zpow_eq_one.mp ht
      refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
      show n • Additive.ofMul t = 0
      rw [← ofMul_zpow, hn1]
      rfl
    · rfl

private theorem exists_units_generator_of_finOrder_units (F : Type) [Field F] [NumberField F] : ∃ ρ : Fˣ, ∀ t : Fˣ, IsOfFinOrder t → ∃ k : ℤ, t = ρ ^ k := by
  have hs : (Set.range (fun u : CommGroup.torsion Fˣ => ((u : Fˣ) : F))).Finite := by
    refine (NumberField.Embeddings.finite_of_norm_le F ℂ 1).subset ?_
    rintro _ ⟨u, rfl⟩
    have hu : IsOfFinOrder (u : Fˣ) := (CommGroup.mem_torsion _).mp u.2
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hu
    have hx : ((u : Fˣ) : F) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]
    refine ⟨IsIntegral.of_pow hn (by rw [hx]; exact isIntegral_one), fun φ => ?_⟩
    have hφ : (φ ((u : Fˣ) : F)) ^ n = 1 := by
      rw [← map_pow, hx, map_one]
    exact le_of_eq (Complex.norm_eq_one_of_pow_eq_one hφ hn.ne')
  have hinj : Function.Injective (fun u : CommGroup.torsion Fˣ => ((u : Fˣ) : F)) := by
    intro a b h
    exact Subtype.ext (Units.ext h)
  have hfin : Finite (CommGroup.torsion Fˣ) := (Set.finite_range_iff hinj).mp hs
  obtain ⟨g, hg⟩ := (isCyclic_subgroup_units (CommGroup.torsion Fˣ)).exists_generator
  refine ⟨g, fun t ht => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨t, (CommGroup.mem_torsion _).mpr ht⟩)
  exact ⟨k, by simpa using (congrArg Subtype.val hk).symm⟩

private theorem exists_heightOneSpectrum_liesOver (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (p : HeightOneSpectrum (𝓞 L)) : ∃ P : HeightOneSpectrum (𝓞 F), P.asIdeal.LiesOver p.asIdeal := by
  haveI := p.isMaximal
  obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) p.asIdeal
  refine ⟨⟨Q, hQm.isPrime, ?_⟩, hQ⟩
  intro hQbot
  apply p.ne_bot
  rw [hQ.over, hQbot]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

private theorem exists_rep_of_mem_selInv_ordP_dvd_actU_eq (L F : Type) [Field L] [Field F] [NumberField F] [Algebra L F] (l a : ℕ) (hl0 : 0 < l) (γ : F ≃ₐ[L] F) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)) (hD : IsDat γ a D) (ρ : Fˣ) (hρ : ∀ t : Fˣ, IsOfFinOrder t → ∃ k : ℤ, t = ρ ^ k) (x : Additive Fˣ ⧸ Ct.mt (Additive Fˣ) l) (hx : x ∈ D.SelInv l) :
    ∃ (r : ℕ) (α v : Fˣ), r < l ∧ Submodule.Quotient.mk (Additive.ofMul α) = x ∧ (∀ P, (l : ℤ) ∣ ordP P α) ∧ actU γ α = α * v ^ l * ρ ^ r := by
  obtain ⟨y, rfl, hg, i, hi⟩ := hx
  have hy : y = Additive.ofMul (Additive.toMul y) := rfl
  set α := Additive.toMul y with hα
  have hord : ∀ P, (l : ℤ) ∣ ordP P α := by
    intro P
    rw [← hD.d_eq α P, ← hy, hi, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  rw [hy, hD.g_eq α] at hg
  have hm : Additive.ofMul (actU γ⁻¹ α * α⁻¹) ∈ Ct.mt (Additive Fˣ) l := by
    rw [ofMul_mul, ofMul_inv, ← sub_eq_add_neg]
    exact hg
  obtain ⟨w, t, ht, hwt⟩ := (ofMul_mem_mt_iff_exists_pow_mul_finOrder l _).mp hm
  have hback : actU γ (actU γ⁻¹ α) = α := by
    ext
    simp [actU]
  have hkey : actU γ α = α * ((actU γ w) ^ l * actU γ t)⁻¹ := by
    have h1 : actU γ⁻¹ α = w ^ l * t * α := by
      rw [← hwt]
      group
    have h2 := congrArg (actU γ) h1
    rw [hback, map_mul, map_mul, map_pow] at h2
    rw [eq_mul_inv_iff_mul_eq]
    conv_rhs => rw [h2]
    rw [mul_comm]
  obtain ⟨k, hk⟩ := hρ (actU γ t)⁻¹ ((MonoidHom.isOfFinOrder _ ht).inv)
  have hl' : (0 : ℤ) < l := by exact_mod_cast hl0
  have hr0 : 0 ≤ k % (l : ℤ) := Int.emod_nonneg k hl'.ne'
  have hrl : k % (l : ℤ) < l := Int.emod_lt_of_pos k hl'
  refine ⟨(k % (l : ℤ)).toNat, α, (actU γ w)⁻¹ * ρ ^ (k / (l : ℤ)), by omega, rfl, hord, ?_⟩
  have hkk : k = (l : ℤ) * (k / (l : ℤ)) + ((k % (l : ℤ)).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg hr0]
    exact (Int.mul_ediv_add_emod k l).symm
  rw [hkey, mul_inv, hk]
  conv_lhs => rw [hkk]
  rw [zpow_add, zpow_mul', zpow_natCast, zpow_natCast]
  simp only [mul_pow, inv_pow, mul_assoc]

private theorem selInvLe_lemma_5 (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (l c ν a : ℕ) (ζ : (𝓞 F)ˣ) (γ : F ≃ₐ[L] F) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)) (hl : l.Prime) (hL : Lay l c ν ζ γ) (hD : IsDat γ a D) (α α' v v' ρ : Fˣ) (r : ℕ) (hord : ∀ P, (l : ℤ) ∣ ordP P α) (hord' : ∀ P, (l : ℤ) ∣ ordP P α') (h : actU γ α = α * v ^ l * ρ ^ r) (h' : actU γ α' = α' * v' ^ l * ρ ^ r) (hN : Algebra.norm L (v : F) = Algebra.norm L (v' : F)) :
    ∃ x₀ : Lˣ, (QuotientGroup.mk x₀ : Lˣ ⧸ (powMonoidHom l).range) ∈ SelL l L ∧
      (Submodule.Quotient.mk (Additive.ofMul α) : Additive Fˣ ⧸ Ct.mt (Additive Fˣ) l) =
        Submodule.Quotient.mk (Additive.ofMul α') + Submodule.Quotient.mk (Additive.ofMul (Units.map (algebraMap L F : L →* F) x₀)) := by
  have hβ : actU γ (α * α'⁻¹) = (α * α'⁻¹) * (v * v'⁻¹) ^ l := by
    rw [map_mul, map_inv, h, h']
    ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    have h1 : (α' : F) ≠ 0 := α'.ne_zero
    have h2 : (v' : F) ≠ 0 := v'.ne_zero
    have h3 : (ρ : F) ≠ 0 := ρ.ne_zero
    rw [mul_pow, inv_pow]
    field_simp
  have hN1 : Algebra.norm L ((v * v'⁻¹ : Fˣ) : F) = 1 := by
    rw [Units.val_mul, map_mul, hN, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  obtain ⟨x₀, z, hz⟩ := h90 L F γ l hL.gal hL.gen (α * α'⁻¹) (v * v'⁻¹) hβ hN1
  have hx₀ : Units.map (algebraMap L F : L →* F) x₀ = α * α'⁻¹ * (z ^ l)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, hz]
  refine ⟨x₀, ⟨x₀, rfl, fun p hp => ?_⟩, ?_⟩
  · obtain ⟨P, hP⟩ := exists_heightOneSpectrum_liesOver L F p
    rw [← unram L F l c ν ζ γ hl hL x₀ P p hp hP]
    have hadd : ∀ b b' : Fˣ, ordP P (b * b') = ordP P b + ordP P b' := by
      intro b b'
      rw [← hD.d_eq, ← hD.d_eq, ← hD.d_eq, ofMul_mul, map_add, Finsupp.add_apply]
    have hinv : ∀ b : Fˣ, ordP P b⁻¹ = - ordP P b := by
      intro b
      rw [← hD.d_eq, ← hD.d_eq, ofMul_inv, map_neg, Finsupp.neg_apply]
    have hpow : ∀ b : Fˣ, ordP P (b ^ l) = l * ordP P b := by
      intro b
      rw [← hD.d_eq, ← hD.d_eq, ofMul_pow, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
    rw [hx₀, hadd, hadd, hinv, hinv, hpow]
    exact dvd_add (dvd_add (hord P) (dvd_neg.mpr (hord' P))) (dvd_neg.mpr (dvd_mul_right _ _))
  · rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq, sub_eq_add_neg, ← ofMul_mul, ← ofMul_inv, ← ofMul_mul, hx₀]
    refine (ofMul_mem_mt_iff_exists_pow_mul_finOrder l _).mpr ⟨z, 1, isOfFinOrder_iff_pow_eq_one.mpr ⟨1, one_pos, one_pow 1⟩, ?_⟩
    have h1 : (α' : F) ≠ 0 := α'.ne_zero
    have h2 : (z : F) ≠ 0 := z.ne_zero
    have h3 : (α : F) ≠ 0 := α.ne_zero
    ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_one]
    field_simp

private theorem norm_pow_eq_inv_norm_pow_of_actU_eq_mul_pow (L F : Type) [Field L] [Field F] [Algebra L F] (γ : F ≃ₐ[L] F) (α v ρ : Fˣ) (l r : ℕ) (h : actU γ α = α * v ^ l * ρ ^ r) :
    Algebra.norm L (v : F) ^ l = (Algebra.norm L (ρ : F) ^ r)⁻¹ := by
  have e := congrArg (fun u : Fˣ => Algebra.norm L (u : F)) h
  have hγ : ((actU γ α : Fˣ) : F) = γ (α : F) := by simp [actU]
  simp only [hγ, Algebra.norm_eq_of_algEquiv, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow] at e
  have hu : ∀ b : Fˣ, Algebra.norm L (b : F) * Algebra.norm L ((b⁻¹ : Fˣ) : F) = 1 := by
    intro b
    rw [← map_mul, Units.mul_inv, map_one]
  have hα : Algebra.norm L (α : F) ≠ 0 := left_ne_zero_of_mul_eq_one (hu α)
  have hρ : Algebra.norm L (ρ : F) ^ r ≠ 0 := pow_ne_zero _ (left_ne_zero_of_mul_eq_one (hu ρ))
  have e2 : Algebra.norm L (α : F) * (Algebra.norm L (v : F) ^ l * Algebra.norm L (ρ : F) ^ r) = Algebra.norm L (α : F) * 1 := by
    rw [mul_one, ← mul_assoc]
    exact e.symm
  have e3 := mul_left_cancel₀ hα e2
  exact eq_inv_of_mul_eq_one_left e3

theorem UpperTheory.V.ZK.Ct.selInvLe :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (l c ν a : ℕ) (ζ : (𝓞 F)ˣ) (γ : F ≃ₐ[L] F) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)), l.Prime → Lay l c ν ζ γ → IsDat γ a D → Finite (SelL l L) → Finite (D.SelInv l) ∧ Nat.card (D.SelInv l) ≤ Nat.card (SelL l L) * l ^ 2 := by
  intro L F _ _ _ _ _ l c ν a ζ γ D hl hL hD hfin
  classical
  obtain ⟨ρ, hρ⟩ := exists_units_generator_of_finOrder_units F
  have hl0 : 0 < l := hl.pos
  let T : Finset (ℕ × L) := (Finset.range l).biUnion
    (fun r => ((Polynomial.nthRoots l (Algebra.norm L (ρ : F) ^ r)⁻¹).toFinset).image (fun z => (r, z)))
  have hT : T.card ≤ l * l := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ r ∈ Finset.range l, (((Polynomial.nthRoots l (Algebra.norm L (ρ : F) ^ r)⁻¹).toFinset).image (fun z => (r, z))).card
        ≤ ∑ r ∈ Finset.range l, l := Finset.sum_le_sum (fun r _ =>
          Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)))
      _ = l * l := by simp
  let Ty : (Additive Fˣ ⧸ Ct.mt (Additive Fˣ) l) → ℕ × L → Prop := fun x t =>
    ∃ α v : Fˣ, Submodule.Quotient.mk (Additive.ofMul α) = x ∧ (∀ P, (l : ℤ) ∣ ordP P α) ∧
      actU γ α = α * v ^ l * ρ ^ t.1 ∧ Algebra.norm L (v : F) = t.2
  have hty : ∀ x ∈ D.SelInv l, ∃ t ∈ T, Ty x t := by
    intro x hx
    obtain ⟨r, α, v, hr, hxα, hord, hact⟩ := exists_rep_of_mem_selInv_ordP_dvd_actU_eq L F l a hl0 γ D hD ρ hρ x hx
    refine ⟨(r, Algebra.norm L (v : F)), ?_, α, v, hxα, hord, hact, rfl⟩
    simp only [T, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Multiset.mem_toFinset]
    refine ⟨r, hr, _, ?_, rfl⟩
    rw [Polynomial.mem_nthRoots hl0]
    exact norm_pow_eq_inv_norm_pow_of_actU_eq_mul_pow L F γ α v ρ l r hact
  let rep : ℕ × L → (Additive Fˣ ⧸ Ct.mt (Additive Fˣ) l) := fun t =>
    if h : ∃ x ∈ D.SelInv l, Ty x t then h.choose else 0
  let ψ : (Lˣ ⧸ (powMonoidHom l).range) → (Additive Fˣ ⧸ Ct.mt (Additive Fˣ) l) := fun s =>
    Submodule.Quotient.mk (Additive.ofMul (Units.map (algebraMap L F : L →* F) s.out))
  let f : (ℕ × L) × (Lˣ ⧸ (powMonoidHom l).range) → (Additive Fˣ ⧸ Ct.mt (Additive Fˣ) l) :=
    fun p => rep p.1 + ψ p.2
  have hψ : ∀ x₀ : Lˣ, ψ (QuotientGroup.mk x₀) =
      Submodule.Quotient.mk (Additive.ofMul (Units.map (algebraMap L F : L →* F) x₀)) := by
    intro x₀
    obtain ⟨hh, hhe⟩ := QuotientGroup.mk_out_eq_mul (powMonoidHom l).range x₀
    obtain ⟨b, hb⟩ := hh.2
    show Submodule.Quotient.mk (Additive.ofMul (Units.map (algebraMap L F : L →* F)
      (Quotient.out (QuotientGroup.mk x₀ : Lˣ ⧸ (powMonoidHom l).range)))) = _
    rw [hhe, Submodule.Quotient.eq, sub_eq_add_neg, ← ofMul_inv, ← ofMul_mul]
    refine (ofMul_mem_mt_iff_exists_pow_mul_finOrder l _).mpr ⟨Units.map (algebraMap L F : L →* F) b, 1,
      isOfFinOrder_iff_pow_eq_one.mpr ⟨1, one_pos, one_pow 1⟩, ?_⟩
    rw [map_mul, ← hb, powMonoidHom_apply, map_pow, mul_one, mul_comm, inv_mul_cancel_left]
  have hsub : D.SelInv l ⊆ f '' ((↑T : Set (ℕ × L)) ×ˢ SelL l L) := by
    intro x hx
    obtain ⟨t, htT, hxt⟩ := hty x hx
    have hex : ∃ x ∈ D.SelInv l, Ty x t := ⟨x, hx, hxt⟩
    have hrep : rep t = hex.choose := dif_pos hex
    obtain ⟨_, hx't⟩ := hex.choose_spec
    obtain ⟨α, v, hxα, hord, hact, hN⟩ := hxt
    obtain ⟨α', v', hxα', hord', hact', hN'⟩ := hx't
    obtain ⟨x₀, hx₀S, hx₀⟩ := selInvLe_lemma_5 L F l c ν a ζ γ D hl hL hD α α' v v' ρ t.1 hord hord'
      hact hact' (hN.trans hN'.symm)
    refine ⟨(t, QuotientGroup.mk x₀), ⟨htT, hx₀S⟩, ?_⟩
    show rep t + ψ (QuotientGroup.mk x₀) = x
    rw [hrep, ← hxα', ← hxα, hx₀, hψ]
  have hfinS : (SelL l L).Finite := Set.finite_coe_iff.mp hfin
  have hfinT : ((↑T : Set (ℕ × L)) ×ˢ SelL l L).Finite := T.finite_toSet.prod hfinS
  have hfinI := hfinT.image f
  refine ⟨(hfinI.subset hsub).to_subtype, ?_⟩
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  calc (D.SelInv l).ncard ≤ (f '' ((↑T : Set (ℕ × L)) ×ˢ SelL l L)).ncard := Set.ncard_le_ncard hsub hfinI
    _ ≤ ((↑T : Set (ℕ × L)) ×ˢ SelL l L).ncard := Set.ncard_image_le hfinT
    _ = (↑T : Set (ℕ × L)).ncard * (SelL l L).ncard := Set.ncard_prod
    _ ≤ (l * l) * (SelL l L).ncard := by
      rw [Set.ncard_coe_finset]
      exact Nat.mul_le_mul_right _ hT
    _ = (SelL l L).ncard * l ^ 2 := by ring

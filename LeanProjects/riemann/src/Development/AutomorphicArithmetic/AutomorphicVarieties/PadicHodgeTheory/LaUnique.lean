import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HeckeLAdicParameterAbove
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem finite_emb {F : Type} [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (w : Plc F) :
    Finite (Emb l w) := by
  classical
  let φ : Emb l w → (F →+* Qbar l) := fun j =>
    (j.1).comp (algebraMap F (HeightOneSpectrum.adicCompletion F w))
  refine Finite.of_injective φ ?_
  intro i j hij
  apply Subtype.ext
  have hd := HeightOneSpectrum.denseRange_algebraMap (K := F) w
  have hfun : (i.1 : HeightOneSpectrum.adicCompletion F w → Qbar l) = j.1 :=
    hd.equalizer i.2 j.2 (funext fun x => DFunLike.congr_fun hij x)
  exact DFunLike.coe_injective hfun

private theorem lin_term {ι L : Type} [Fintype ι] [Field L] [CharZero L] (c : ι → L) (p q : ι → ℕ)
    (H : ∀ n : ℕ, ∏ i, (1 + c i * n) ^ p i = ∏ i, (1 + c i * n) ^ q i) :
    ∑ i, (p i : L) * c i = ∑ i, (q i : L) * c i := by
  classical
  open Polynomial in
  have hmul : ∀ f g : L[X], (f * g).coeff 1 = f.coeff 0 * g.coeff 1 + f.coeff 1 * g.coeff 0 := by
    intro f g
    rw [coeff_mul, Finset.Nat.antidiagonal_succ]
    simp [add_comm]
  have hlin : ∀ (a : L) (m : ℕ), ((1 + C a * X) ^ m).coeff 0 = 1 ∧ ((1 + C a * X) ^ m).coeff 1 = (m : L) * a := by
    intro a m
    induction m with
    | zero => simp [coeff_one]
    | succ m ih =>
      refine ⟨?_, ?_⟩
      · rw [pow_succ, mul_coeff_zero, ih.1]
        simp
      · rw [pow_succ, hmul, ih.1, ih.2]
        simp [coeff_one, coeff_C_mul_X]
        push_cast
        ring
  have hprod : ∀ (m : ι → ℕ) (s : Finset ι), (∏ i ∈ s, (1 + C (c i) * X) ^ m i).coeff 0 = 1 ∧
      (∏ i ∈ s, (1 + C (c i) * X) ^ m i).coeff 1 = ∑ i ∈ s, (m i : L) * c i := by
    intro m s
    induction s using Finset.induction_on with
    | empty => simp [coeff_one]
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj]
      refine ⟨?_, ?_⟩
      · rw [mul_coeff_zero, ih.1, (hlin (c j) (m j)).1, one_mul]
      · rw [hmul, ih.1, ih.2, (hlin (c j) (m j)).1, (hlin (c j) (m j)).2]
        ring
  have heq : (∏ i, (1 + C (c i) * X) ^ p i) = ∏ i, (1 + C (c i) * X) ^ q i := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := Set.range (fun n : ℕ => (n : L)))
    · rintro _ ⟨n, rfl⟩
      simp only [Set.mem_setOf_eq, eval_prod, eval_pow, eval_add, eval_one, eval_mul, eval_C, eval_X]
      exact H n
    · exact Set.infinite_range_of_injective Nat.cast_injective
  have h1 := congrArg (fun P : L[X] => P.coeff 1) heq
  rw [(hprod p Finset.univ).2, (hprod q Finset.univ).2] at h1
  exact h1

private theorem indep {ι k L Γ : Type} [Fintype ι] [Field k] [Field L] [CharZero L]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation k Γ) (π : k) (h0 : π ≠ 0) (h1 : v π < 1)
    (τ : ι → k →+* L) (hτ : Function.Injective τ) (e : ι → ℤ)
    (H : ∀ u : k, v u = 1 → ∏ i, τ i u ^ e i = 1) : e = 0 := by
  classical
  have hnat : ∀ n : ℕ, v (n : k) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      exact le_trans (v.map_add _ _) (max_le ih (by simp))
  have hS : ∀ y : k, v y < 1 → ∑ i, (e i : L) * τ i y = 0 := by
    intro y hy
    have key : ∀ n : ℕ, ∏ i, (1 + τ i y * n) ^ (e i).toNat = ∏ i, (1 + τ i y * n) ^ (-e i).toNat := by
      intro n
      have hlt : v ((n : k) * y) < 1 := by
        rw [v.map_mul]
        calc v (n : k) * v y ≤ 1 * v y := by gcongr; exact hnat n
          _ = v y := one_mul _
          _ < 1 := hy
      have hu : v (1 + (n : k) * y) = 1 := v.map_one_add_of_lt hlt
      have hu0 : (1 + (n : k) * y) ≠ 0 := by
        intro h0
        rw [h0, v.map_zero] at hu
        exact zero_ne_one hu
      have hx : ∀ i, τ i (1 + (n : k) * y) = 1 + τ i y * n := by
        intro i
        simp [map_add, map_mul, map_natCast, mul_comm]
      have hne : ∀ i, τ i (1 + (n : k) * y) ≠ 0 := fun i => (map_ne_zero (τ i)).2 hu0
      have h := H _ hu
      have hsplit : ∀ i, τ i (1 + (n : k) * y) ^ e i =
          τ i (1 + (n : k) * y) ^ (e i).toNat / τ i (1 + (n : k) * y) ^ (-e i).toNat := by
        intro i
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (hne i), Int.toNat_sub_toNat_neg]
      simp only [hsplit] at h
      rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hne i))] at h
      simpa only [hx] using h
    have h2 := lin_term (fun i => τ i y) (fun i => (e i).toNat) (fun i => (-e i).toNat) key
    have hcast : ∀ i, (e i : L) = ((e i).toNat : L) - ((-e i).toNat : L) := by
      intro i
      have := congrArg (fun z : ℤ => (z : L)) (Int.toNat_sub_toNat_neg (e i))
      push_cast at this
      exact this.symm
    simp only [hcast, sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 h2
  let R := v.integer
  let ρ : ι → (R →* L) := fun i => (τ i).toMonoidHom.comp R.subtype.toMonoidHom
  have hinj : Function.Injective ρ := by
    intro i j hij
    apply hτ
    ext x
    rcases le_or_gt (v x) 1 with hx | hx
    · have := DFunLike.congr_fun hij ⟨x, hx⟩
      simpa [ρ] using this
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have hxi : v x⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact (inv_lt_one_of_one_lt₀ hx).le
      have := DFunLike.congr_fun hij ⟨x⁻¹, hxi⟩
      simp only [ρ, MonoidHom.coe_comp, Function.comp_apply] at this
      simpa [map_inv₀] using this
  have hli := (linearIndependent_monoidHom R L).comp ρ hinj
  rw [Fintype.linearIndependent_iff] at hli
  have hz := hli (fun i => (e i : L) * τ i π) (by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
    have ha : v (π * (a : k)) < 1 := by
      rw [v.map_mul]
      calc v π * v (a : k) ≤ v π * 1 := by gcongr; exact a.2
        _ = v π := mul_one _
        _ < 1 := h1
    have := hS _ ha
    simp only [map_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [ρ, mul_assoc])
  funext i
  have hi := hz i
  have hπ : τ i π ≠ 0 := (map_ne_zero (τ i)).2 h0
  have : (e i : L) = 0 := by
    rcases mul_eq_zero.1 hi with h | h
    · exact h
    · exact absurd h hπ
  simpa using this

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem UpperTheory.V.Loc.laUnique :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), (∃ a, IsLocalArtin h a) → ∀ (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (wt wt' : Emb l w → ℤ), IsLocAlg h κ wt → IsLocAlg h κ wt' → wt = wt' := by
  intro F Ω _ _ _ _ _ l _ A w h ha0 κ wt wt' hw hw'
  classical
  obtain ⟨a, ha⟩ := ha0
  obtain ⟨ph, hph⟩ := hw
  obtain ⟨ph', hph'⟩ := hw'
  haveI : Finite (Emb l w) := finite_emb l w
  letI : Fintype (Emb l w) := Fintype.ofFinite _
  let K : Subgroup ↥(Ine (F := F) A) := ph.ker ⊓ ph'.ker
  haveI : CompactSpace ↥(Ine (F := F) A) :=
    isCompact_iff_compactSpace.mp (isClosed_Ine (F := F) A).isCompact
  have hKo : IsOpen (K : Set ↥(Ine (F := F) A)) := hph.1.inter hph'.1
  haveI : Finite (↥(Ine (F := F) A) ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKo
  haveI : K.Normal := Subgroup.normal_inf_normal _ _
  have hm0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel : ∀ σ : ↥(Ine (F := F) A), ∏ τ : Emb l w,
      (τ.1 (a (ineIncl h σ) : HeightOneSpectrum.adicCompletion F w)) ^ ((K.index : ℤ) * (wt' τ - wt τ)) = 1 := by
    intro σ
    have hmem := K.pow_index_mem σ
    have hk1 : ph (σ ^ K.index) = 1 := hmem.1
    have hk2 : ph' (σ ^ K.index) = 1 := hmem.2
    have e1 := hph.2 a ha (σ ^ K.index)
    have e2 := hph'.2 a ha (σ ^ K.index)
    rw [hk1, mul_one] at e1
    rw [hk2, mul_one] at e2
    have e := e1.symm.trans e2
    rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype] at e
    simp only [map_pow, Units.val_pow_eq_pow_val] at e
    have hy : ((a (ineIncl h σ)) : HeightOneSpectrum.adicCompletion F w) ≠ 0 := Units.ne_zero _
    have hne : ∀ τ : Emb l w, τ.1 ((a (ineIncl h σ)) : HeightOneSpectrum.adicCompletion F w) ≠ 0 :=
      fun τ => (map_ne_zero τ.1).2 hy
    have hsp : ∀ τ : Emb l w, τ.1 ((a (ineIncl h σ)) : HeightOneSpectrum.adicCompletion F w) ^ ((K.index : ℤ) * (wt' τ - wt τ)) =
        (τ.1 ((a (ineIncl h σ)) : HeightOneSpectrum.adicCompletion F w) ^ K.index) ^ (-wt τ) /
        (τ.1 ((a (ineIncl h σ)) : HeightOneSpectrum.adicCompletion F w) ^ K.index) ^ (-wt' τ) := by
      intro τ
      rw [← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_sub₀ (hne τ)]
      congr 1
      ring
    simp only [hsp]
    rw [Finset.prod_div_distrib, e, div_self (Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (pow_ne_zero _ (hne τ)))]
  obtain ⟨γ, hγ0, hγ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := HeightOneSpectrum.adicCompletion F w)
  obtain ⟨π, hπ⟩ := ValuativeRel.valuation_surjective γ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact hγ0.ne hπ
  have he := indep (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion F w)) π hπ0 (hπ ▸ hγ1)
    (fun τ : Emb l w => τ.1) Subtype.val_injective (fun τ => (K.index : ℤ) * (wt' τ - wt τ)) (by
      intro u hu
      have hu0 : u ≠ 0 := by
        rintro rfl
        rw [map_zero] at hu
        exact zero_ne_one hu
      have hord : GlobalTheory.SmGL.ord _ (Units.mk0 u hu0) = 0 := GlobalTheory.SmGL.ord_eq_zero_iff.2 (by simpa using hu)
      obtain ⟨ρ, hρ⟩ := ha.surj (Units.mk0 u hu0)
      have hdeg : deg ρ = 0 := by
        have := ha.ord_eq ρ
        rw [hρ, hord] at this
        omega
      have hI : (ρ : G F Ω) ∈ Ine (F := F) A :=
        actsAs_zero_iff.1 (actsAs_of_deg (a := 0) (b := 0) (by simp [hdeg]))
      have hr : ineIncl h ⟨(ρ : G F Ω), hI⟩ = ρ := Subtype.ext rfl
      have := hrel ⟨(ρ : G F Ω), hI⟩
      rw [hr, hρ] at this
      simpa using this)
  funext τ
  have hτ := congrFun he τ
  simp only [Pi.zero_apply, mul_eq_zero, Nat.cast_eq_zero] at hτ
  rcases hτ with hτ | hτ
  · exact absurd hτ hm0
  · exact (sub_eq_zero.1 hτ).symm

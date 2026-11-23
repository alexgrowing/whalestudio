import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

noncomputable section
namespace GlobalTheory.PlaceBridge

theorem val_int_lt_one_iff {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {l : ℕ} (hl : l.Prime)
    (h : B.valuation (l : Ω) < 1) (n : ℤ) : B.valuation (n : Ω) < 1 ↔ (l : ℤ) ∣ n := by
  have hint : ∀ m : ℤ, B.valuation (m : Ω) ≤ 1 := fun m =>
    (B.valuation_le_one_iff _).2 (intCast_mem B m)
  constructor
  · intro hn
    by_contra hd
    have hc : IsCoprime (l : ℤ) n :=
      ((Nat.prime_iff_prime_int.mp hl).irreducible.coprime_iff_not_dvd).2 hd
    obtain ⟨a, b, hab⟩ := hc
    have h1 : (a : Ω) * (l : Ω) + (b : Ω) * (n : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
    have h2 : B.valuation ((a : Ω) * (l : Ω) + (b : Ω) * (n : Ω)) < 1 := by
      apply Valuation.map_add_lt
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint a)) h
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint b)) hn
    rw [h1, map_one] at h2
    exact lt_irrefl _ h2
  · rintro ⟨m, rfl⟩
    push_cast
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint m)) h

variable {l : ℕ} [Fact l.Prime]

theorem norm_l_lt_one : ‖(l : PadicAlgCl l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem exists_embedding (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (hw : w ∈ placesOver E l) (hA : IsPlaceOver A w) :
    ∃ j : Ω →+* PadicAlgCl l, ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1 := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  let j0 : Ω →ₐ[ℚ] PadicAlgCl l := IsAlgClosed.lift
  let A0 : ValuationSubring Ω := (Valued.v (R := PadicAlgCl l)).valuationSubring.comap j0.toRingHom
  have hA0 : ∀ x, x ∈ A0 ↔ ‖j0 x‖ ≤ 1 := fun x => by
    change Valued.v (j0 x) ≤ 1 ↔ _
    rw [PadicAlgCl.valuation_def]
    exact Iff.rfl
  have hl : l.Prime := Fact.out
  have hAl : A.valuation (l : Ω) < 1 := by
    have := (hA (l : 𝓞 E)).2 hw
    simpa using this
  have hA0l : A0.valuation (l : Ω) < 1 := by
    rw [valuation_lt_one_iff', hA0, hA0, map_inv₀, map_natCast, norm_inv]
    have h0 : 0 < ‖(l : PadicAlgCl l)‖ := norm_pos_iff.2 (by exact_mod_cast hl.ne_zero)
    refine ⟨norm_l_lt_one.le, Or.inr (not_le.2 ?_)⟩
    exact (one_lt_inv₀ h0).2 norm_l_lt_one
  let v : HeightOneSpectrum (𝓞 ℚ) := w.under (𝓞 ℚ)
  have h1 : IsPlaceOver (F := ℚ) A v := fun x => by
    have := hA (algebraMap (𝓞 ℚ) (𝓞 E) x)
    change _ ↔ algebraMap (𝓞 ℚ) (𝓞 E) x ∈ w.asIdeal
    rw [← this]
    have e : algebraMap E Ω ((algebraMap (𝓞 ℚ) (𝓞 E) x : 𝓞 E) : E) = algebraMap ℚ Ω (x : ℚ) := by
      obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
      simp
    rw [e]
  have h0 : IsPlaceOver (F := ℚ) A0 v := fun x => by
    rw [← h1 x]
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
    have e : algebraMap ℚ Ω ((Rat.ringOfIntegersEquiv.symm n : 𝓞 ℚ) : ℚ) = (n : Ω) := by simp
    rw [e, val_int_lt_one_iff A hl hAl, val_int_lt_one_iff A0 hl hA0l]
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver h0 h1
  refine ⟨j0.toRingHom.comp σ.symm.toRingEquiv.toRingHom, fun x => ?_⟩
  rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hA0]
  rfl

theorem denseRange_embedding {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l) : DenseRange j := by
  have : CharZero Ω := (RingHom.charZero_iff j.injective).2 inferInstance
  rw [Metric.denseRange_iff]
  intro a δ δpos
  have hi : DenseRange (algebraMap ℚ ℚ_[l]) := Padic.denseRange_ratCast l
  have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  set f := minpoly ℚ_[l] a with hf
  have fmon : f.Monic := minpoly.monic hint
  have fa0 : f.aeval a = 0 := minpoly.aeval _ _
  have fnatdeg0 : f.natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have hε : (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hi fmon hε
  obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
  have hab : ‖a - b‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
    · simp [fnatdeg0]
    · positivity
  have e : (g.map (algebraMap ℚ ℚ_[l])).map (algebraMap ℚ_[l] (PadicAlgCl l)) =
      (g.map (algebraMap ℚ Ω)).map j := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact Subsingleton.elim _ _
  rw [Polynomial.aroots_def, e, Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨y, -, rfl⟩ := hb
  exact ⟨y, by rwa [dist_eq_norm]⟩

theorem norm_eq_of_le_one_iff {Ω : Type} [Field Ω] (j j' : Ω →+* PadicAlgCl l)
    (h : ∀ x, ‖j x‖ ≤ 1 ↔ ‖j' x‖ ≤ 1) (x : Ω) : ‖j' x‖ = ‖j x‖ := by
  let v : AbsoluteValue Ω ℝ := (NormedField.toAbsoluteValue (PadicAlgCl l)).comp j.injective
  let v' : AbsoluteValue Ω ℝ := (NormedField.toAbsoluteValue (PadicAlgCl l)).comp j'.injective
  have hv : ∀ y, v y = ‖j y‖ := fun _ => rfl
  have hv' : ∀ y, v' y = ‖j' y‖ := fun _ => rfl
  have he : v.IsEquiv v' := by
    intro a b
    rcases eq_or_ne b 0 with rfl | hb
    · simp
    · have := h (a / b)
      rw [map_div₀, map_div₀, norm_div, norm_div, div_le_one (by simpa using hb),
        div_le_one (by simpa using hb)] at this
      exact this
  obtain ⟨c, hc, hcv⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  have h0 : 0 < ‖(l : PadicAlgCl l)‖ := norm_pos_iff.2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have h1 := congrFun hcv (l : Ω)
  simp only [hv, hv', map_natCast] at h1
  have hc1 : c = 1 := by
    have := (Real.rpow_right_inj h0 norm_l_lt_one.ne).1 (h1.trans (Real.rpow_one _).symm)
    exact this
  have h2 := congrFun hcv x
  simp only [hv, hv', hc1, Real.rpow_one] at h2
  exact h2.symm

theorem exists_algEquiv {Ω : Type} [Field Ω] (j j' : Ω →+* PadicAlgCl l) (hd : DenseRange j)
    (h : ∀ x, ‖j' x‖ = ‖j x‖) :
    ∃ τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, ∀ x, τ (j x) = j' x := by
  have : CharZero Ω := (RingHom.charZero_iff j.injective).2 inferInstance
  let : NormedField Ω := NormedField.induced Ω (PadicAlgCl l) j j.injective
  have hj : Isometry j := AddMonoidHomClass.isometry_of_norm j fun _ => rfl
  let f : Ω →+* ℂ_[l] := (algebraMap (PadicAlgCl l) ℂ_[l]).comp j'
  have hf : Isometry f := AddMonoidHomClass.isometry_of_norm f fun x => by
    change ‖((j' x : PadicAlgCl l) : ℂ_[l])‖ = ‖j x‖
    rw [PadicComplex.norm_extends, h]
  let t : PadicAlgCl l →+* ℂ_[l] :=
    IsDenseInducing.extendRingHom hj.isUniformInducing hd hf.uniformContinuous
  have ht : ∀ x, t (j x) = f x := fun x =>
    uniformly_extend_of_ind hj.isUniformInducing hd hf.uniformContinuous x
  have htc : Continuous t :=
    (uniformContinuous_uniformly_extend hj.isUniformInducing hd hf.uniformContinuous).continuous
  have hq : ∀ x : ℚ_[l], t (algebraMap ℚ_[l] (PadicAlgCl l) x) = algebraMap ℚ_[l] ℂ_[l] x := by
    have := (Padic.denseRange_ratCast l).equalizer
      (htc.comp (continuous_algebraMap ℚ_[l] (PadicAlgCl l))) (continuous_algebraMap ℚ_[l] ℂ_[l])
      (by funext q; simp)
    exact congrFun this
  let ta : PadicAlgCl l →ₐ[ℚ_[l]] ℂ_[l] := ⟨t, hq⟩
  refine ⟨ta.restrictNormal' (PadicAlgCl l), fun x => ?_⟩
  apply (algebraMap (PadicAlgCl l) ℂ_[l]).injective
  exact (ta.restrictNormal_commutes (PadicAlgCl l) (j x)).trans (ht x)

theorem norm_algEquiv (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : PadicAlgCl l) : ‖τ x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv τ x).symm

theorem algEquiv_ext {Ω : Type} [Field Ω] {j : Ω →+* PadicAlgCl l} (hd : DenseRange j)
    {τ τ' : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l} (h : ∀ x, τ (j x) = τ' (j x)) : τ = τ' := by
  have hc : ∀ σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, Continuous σ := fun σ =>
    (AddMonoidHomClass.isometry_of_norm σ (norm_algEquiv σ)).continuous
  exact AlgEquiv.ext (congrFun (hd.equalizer (hc τ) (hc τ') (funext h)))

section Completion

variable {E : Type} [Field E] [NumberField E] (c : E →+* PadicAlgCl l)

theorem finiteDimensional_adjoin_range :
    FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range c)) := by
  let b := Module.finBasis ℚ E
  have h : IntermediateField.adjoin ℚ_[l] (Set.range c) =
      IntermediateField.adjoin ℚ_[l] (Set.range fun i => c (b i)) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      rw [← b.sum_repr x, map_sum]
      refine sum_mem fun i _ => ?_
      rw [Rat.smul_def, map_mul, map_ratCast]
      exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    · apply IntermediateField.adjoin.mono
      rintro _ ⟨i, rfl⟩
      exact ⟨b i, rfl⟩
  rw [h]
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

omit [NumberField E] in
theorem adjoin_range_subset_closure :
    (IntermediateField.adjoin ℚ_[l] (Set.range c) : Set (PadicAlgCl l)) ⊆ closure (Set.range c) := by
  let S : Subfield (PadicAlgCl l) := c.fieldRange.topologicalClosure
  have hS : (S : Set (PadicAlgCl l)) = closure (Set.range c) := rfl
  have hq : ∀ x : ℚ_[l], algebraMap ℚ_[l] (PadicAlgCl l) x ∈ S := fun x => by
    refine (Padic.denseRange_ratCast l).induction_on
      (p := fun x => algebraMap ℚ_[l] (PadicAlgCl l) x ∈ S) x ?_ fun q => ?_
    · exact isClosed_closure.preimage (continuous_algebraMap ℚ_[l] (PadicAlgCl l))
    · rw [map_ratCast]
      exact SubfieldClass.ratCast_mem _ _
  have : IntermediateField.adjoin ℚ_[l] (Set.range c) ≤ S.toIntermediateField hq := by
    rw [IntermediateField.adjoin_le_iff]
    exact subset_closure
  exact this

end Completion

section Group

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {j : Ω →+* PadicAlgCl l}

omit [NumberField E] [IsAlgClosure E Ω] in
theorem mem_GK_iff (K : Loc.FinExt l)
    (hK : K.1 = IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)))
    (τ : Loc.GQ l) : τ ∈ Loc.GK K ↔ ∀ x : E, τ (j (algebraMap E Ω x)) = j (algebraMap E Ω x) := by
  rw [Loc.GK, IntermediateField.mem_fixingSubgroup_iff, hK]
  constructor
  · intro h x
    exact h _ (IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)
  · intro h y hy
    induction hy using IntermediateField.adjoin_induction with
    | mem y hy => obtain ⟨x, rfl⟩ := hy; exact h x
    | algebraMap y => exact τ.commutes y
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | inv a _ ha => rw [map_inv₀, ha]
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]

theorem exists_restrict (hA : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (τ : Loc.GQ l)
    (h : ∀ x : E, τ (j (algebraMap E Ω x)) = j (algebraMap E Ω x)) :
    ∃ g ∈ Dec (F := E) A, ∀ x, τ (j x) = j (g x) := by
  let : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  let : Algebra E (PadicAlgCl l) := (j.comp (algebraMap E Ω)).toAlgebra
  have : IsScalarTower E Ω (PadicAlgCl l) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ta : PadicAlgCl l →ₐ[E] PadicAlgCl l := ⟨τ.toRingEquiv.toRingHom, h⟩
  let g : Ω ≃ₐ[E] Ω := ta.restrictNormal' Ω
  have hg : ∀ x, τ (j x) = j (g x) := fun x => (ta.restrictNormal_commutes Ω x).symm
  refine ⟨g, ?_, hg⟩
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hA, hA, ← norm_algEquiv τ, hg]
  simp

theorem exists_mulEquiv (hA : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (K : Loc.FinExt l)
    (hK : K.1 = IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x))) :
    ∃ e : ↥(Dec (F := E) A) ≃* ↥(Loc.GK K), Continuous e ∧ Continuous e.symm ∧
      ∀ (g : ↥(Dec (F := E) A)) (x : Ω),
        ((e g : ↥(Loc.GK K)) : Loc.GQ l) (j x) = j ((g : Ω ≃ₐ[E] Ω) x) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hd : DenseRange j := denseRange_embedding j
  choose r hr hr' using fun τ : ↥(Loc.GK K) => exists_restrict hA τ.1 ((mem_GK_iff K hK τ.1).1 τ.2)
  let ρ : ↥(Loc.GK K) →* ↥(Dec (F := E) A) := MonoidHom.mk' (fun τ => ⟨r τ, hr τ⟩) fun σ τ => by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    apply j.injective
    change j (r (σ * τ) x) = j (r σ (r τ x))
    rw [← hr', ← hr', ← hr']
    rfl
  have hρ : ∀ (τ : ↥(Loc.GK K)) (x : Ω), (τ : Loc.GQ l) (j x) = j ((ρ τ : Ω ≃ₐ[E] Ω) x) := hr'
  have hinj : Function.Injective ρ := fun σ τ h =>
    Subtype.ext (algEquiv_ext hd fun x => by rw [hρ, hρ, h])
  have hsurj : Function.Surjective ρ := fun g => by
    obtain ⟨τ, hτ⟩ := exists_algEquiv j (j.comp (g : Ω ≃ₐ[E] Ω).toRingEquiv.toRingHom) hd
      (norm_eq_of_le_one_iff _ _ fun x => by
        rw [← hA]
        exact ((hA _).symm.trans (apply_mem_iff_of_mem_Dec g.2 x)).symm)
    have hτ' : ∀ x, τ (j x) = j ((g : Ω ≃ₐ[E] Ω) x) := hτ
    refine ⟨⟨τ, (mem_GK_iff K hK τ).2 fun x => by rw [hτ', AlgEquiv.commutes]⟩, ?_⟩
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    apply j.injective
    rw [← hρ, hτ']
  have hc : Continuous ρ := by
    refine continuous_induced_rng.2 ?_
    refine continuous_of_continuousAt_one ((Dec (F := E) A).subtype.comp ρ) ?_
    intro s hs
    rw [map_one, krullTopology_mem_nhds_one_iff] at hs
    obtain ⟨L, hL, hsub⟩ := hs
    let b := Module.finBasis E L
    have hi : ∀ i, ∀ᶠ τ : ↥(Loc.GK K) in nhds 1, (τ : Loc.GQ l) (j (b i)) = j (b i) := fun i =>
      ((stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) (j (b i))).preimage
        continuous_subtype_val).mem_nhds (show ((1 : ↥(Loc.GK K)) : Loc.GQ l) • j (b i) = j (b i) from rfl)
    rw [Filter.mem_map]
    filter_upwards [Filter.eventually_all.2 hi] with τ hτ
    apply hsub
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have : ((ρ τ : Ω ≃ₐ[E] Ω).toLinearMap.comp L.val.toLinearMap) = L.val.toLinearMap :=
      b.ext fun i => j.injective ((hρ τ _).symm.trans (hτ i))
    exact LinearMap.congr_fun this ⟨x, hx⟩
  have := K.2
  have : CompactSpace ↥(Loc.GK K) :=
    isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K.1).isCompact
  let e := MulEquiv.ofBijective ρ ⟨hinj, hsurj⟩
  refine ⟨e.symm, Continuous.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) hc, hc,
    fun g x => ?_⟩
  rw [hρ]
  exact congrArg (fun g : ↥(Dec (F := E) A) => j ((g : Ω ≃ₐ[E] Ω) x)) (e.apply_symm_apply g)

end Group

theorem exists_locBridge : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), w ∈ placesOver E l → IsPlaceOver A w → ∃ (j : Ω →+* Loc.Om l) (L0 : Loc.FinExt l), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) ∧ ∀ LL : Loc.FinExt l, L0.1 ≤ LL.1 → ∃ Bw : LocBridge l E Ω (Dec (F := E) A) ↥(Loc.OL LL), Bw.j = j ∧ Bw.LL = LL ∧ (Bw.Kw.1 = IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x))) ∧ ∀ x : ↥(Loc.OL LL), ((Bw.toLL x : ↥Bw.LL.1) : Loc.Om l) = ((x : ↥LL.1) : Loc.Om l) := by
  intro l _ E Ω _ _ _ _ _ w A hw hA
  obtain ⟨j, hj⟩ := exists_embedding E Ω w A hw hA
  let K : Loc.FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)),
    finiteDimensional_adjoin_range (j.comp (algebraMap E Ω))⟩
  have := K.2
  obtain ⟨e, he, he', hec⟩ := exists_mulEquiv (E := E) hj K rfl
  refine ⟨j, ⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩, hj, fun LL hLL => ?_⟩
  exact ⟨{
    Kw := K
    j := j
    j_E := fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
    j_dense := adjoin_range_subset_closure (j.comp (algebraMap E Ω))
    e := e
    e_cont := he
    e_symm_cont := he'
    e_comm := hec
    LL := LL
    LL_split := fun τ x => hLL (AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩)
    eO := RingEquiv.refl _
    eO_alg := fun _ => rfl
    eO_cont := continuous_id
    eO_symm_cont := continuous_id }, rfl, rfl, rfl, fun _ => rfl⟩

end GlobalTheory.PlaceBridge

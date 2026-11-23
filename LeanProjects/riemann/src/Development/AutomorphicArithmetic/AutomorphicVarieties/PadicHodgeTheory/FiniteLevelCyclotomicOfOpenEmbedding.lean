import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import ReciprocityTheory.GroupCohomology.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingSubgroupEquivBicontinuous
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContCohomologyTransportMulEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem numField {v : ℕ} [Fact v.Prime] (K : FinExt v) {Ω : Type} [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl v) (A : ValuationSubring Ω) (hA : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) :
    ∃ F : IntermediateField ℚ Ω, FiniteDimensional ℚ F ∧
      K.1 = IntermediateField.adjoin ℚ_[v] (Set.range fun x : F => j (algebraMap F Ω x)) := by
  let K0 : FinExt v := ⟨IntermediateField.adjoin ℚ_[v] (Set.range fun x : ℚ => j (algebraMap ℚ Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap ℚ Ω))⟩
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := ℚ) hA K0 rfl
  have h0 : ∀ τ, τ ∈ GK K0 := fun τ => (GlobalTheory.PlaceBridge.mem_GK_iff K0 rfl τ).2 fun x => by simp
  let r : GQ v →* (Ω ≃ₐ[ℚ] Ω) := (Subgroup.subtype _).comp
    (e.symm.toMonoidHom.comp ((MonoidHom.id _).codRestrict _ h0))
  have hr : ∀ τ x, τ (j x) = j (r τ x) := fun τ x => by
    have := hec (e.symm ⟨τ, h0 τ⟩) x
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  have hrc : Continuous r := continuous_subtype_val.comp (he'.comp (continuous_id.subtype_mk _))
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hK := K.2
  have hle : K.1 ≤ IntermediateField.adjoin ℚ_[v] (j '' {a | j a ∈ K.1}) := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ_[v] _),
      IntermediateField.le_iff_le]
    intro τ hτ
    let H : ClosedSubgroup (Ω ≃ₐ[ℚ] Ω) := ⟨(GK K).map r,
      ((IntermediateField.fixingSubgroup_isClosed K.1).isCompact.image hrc).isClosed⟩
    have h1 : r τ ∈ H.1 := by
      rw [← InfiniteGalois.fixingSubgroup_fixedField H, IntermediateField.mem_fixingSubgroup_iff]
      intro a ha
      apply j.injective
      rw [← hr]
      refine (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ _
        (IntermediateField.subset_adjoin _ _ ⟨a, ?_, rfl⟩)
      change j a ∈ K.1
      rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
      intro σ hσ
      rw [hr, (IntermediateField.mem_fixedField_iff _ _).1 ha _ ⟨σ, hσ, rfl⟩]
    obtain ⟨σ, hσ, hst⟩ := h1
    have : σ = τ := GlobalTheory.PlaceBridge.algEquiv_ext (GlobalTheory.PlaceBridge.denseRange_embedding j)
      fun x => by rw [hr, hr, hst]
    exact this ▸ hσ
  obtain ⟨x, hx⟩ := Field.exists_primitive_element ℚ_[v] K.1
  have hx' : IntermediateField.adjoin ℚ_[v] {(x : PadicAlgCl v)} = K.1 := by
    rw [← IntermediateField.lift_adjoin_simple, hx, IntermediateField.lift_top]
  obtain ⟨T, hT, hxT⟩ := IntermediateField.exists_finset_of_mem_adjoin (hle x.2)
  have hfin : Finite (j ⁻¹' (T : Set (PadicAlgCl v))) :=
    (T.finite_toSet.preimage j.injective.injOn).to_subtype
  refine ⟨IntermediateField.adjoin ℚ (j ⁻¹' (T : Set (PadicAlgCl v))),
    IntermediateField.finiteDimensional_adjoin fun z _ => Algebra.IsIntegral.isIntegral z,
    le_antisymm ?_ ?_⟩
  · rw [← hx', IntermediateField.adjoin_simple_le_iff]
    refine IntermediateField.adjoin.mono _ _ _ (fun t ht => ?_) hxT
    obtain ⟨a, -, rfl⟩ := hT ht
    exact ⟨⟨a, IntermediateField.subset_adjoin _ _ ht⟩, rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    change j y ∈ K.1
    induction hy using IntermediateField.adjoin_induction with
    | mem y hy =>
      obtain ⟨a, ha, h⟩ := hT hy
      exact h ▸ ha
    | algebraMap y => rw [eq_ratCast, map_ratCast]; exact SubfieldClass.ratCast_mem _ _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | inv a _ ha => rw [map_inv₀]; exact inv_mem ha
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

open NumberField IsDedekindDomain in
private theorem placeBelow {v : ℕ} (hv : v.Prime) (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] (A : ValuationSubring Ω) (hA : A.valuation (v : Ω) < 1) :
    ∃ w : HeightOneSpectrum (𝓞 F), Formalism.ConjugateSelfDual.IsPlaceOver A w ∧
      ∀ l : ℕ, l.Prime → v ≠ l → ((l : ℕ) : 𝓞 F) ∉ w.asIdeal := by
  have hm : ∀ x : 𝓞 F, algebraMap F Ω x ∈ A := fun x => by
    have h : IsIntegral ℤ (algebraMap F Ω x) := x.isIntegral_coe.map (algebraMap F Ω).toIntAlgHom
    have := (Valuation.integer.integers A.valuation).mem_of_integral (x := algebraMap F Ω x) h.tower_top
    exact (A.valuation_le_one_iff _).1 this
  let f : 𝓞 F →+* A := ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).codRestrict A hm
  have hf : ∀ x, x ∈ (IsLocalRing.maximalIdeal A).comap f ↔ A.valuation (algebraMap F Ω x) < 1 :=
    fun x => A.valuation_lt_one_iff (f x)
  have hn : ∀ n : ℕ, (n : 𝓞 F) ∈ (IsLocalRing.maximalIdeal A).comap f ↔ v ∣ n := fun n => by
    rw [hf, ← Int.natCast_dvd_natCast, ← GlobalTheory.PlaceBridge.val_int_lt_one_iff A hv hA]
    simp
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, fun h => ?_⟩, fun x => (hf x).symm,
    fun l hl hvl h => hvl ((Nat.prime_dvd_prime_iff_eq hv hl).1 ((hn l).1 h))⟩
  have := (hn v).2 dvd_rfl
  rw [h, Ideal.mem_bot] at this
  exact hv.ne_zero (Nat.cast_eq_zero.1 this)

private theorem hn_transport {R Γ Γ' M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [Group Γ']
    [TopologicalSpace Γ'] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (e : Γ' ≃* Γ) (he : Continuous e) (he' : Continuous e.symm) (ρ : Representation R Γ M)
    (ρ' : Representation R Γ' M) (h : ∀ g m, ρ' g m = ρ (e g) m) (n : ℕ)
    (hs : Subsingleton (Hn ρ (n + 1))) : Subsingleton (Hn ρ' (n + 1)) := by
  have h' : ∀ g m, ρ g m = ρ' (e.symm g) m := fun g m => by rw [h, e.apply_symm_apply]
  rw [GlobalTheory.Published.subsingleton_Hn_succ_iff] at hs ⊢
  intro f hf hd
  obtain ⟨c, hc, hcf⟩ := hs (fun x => f (fun i => e.symm (x i)))
    (hf.comp (continuous_pi fun i => he'.comp (continuous_apply i))) (by
      funext g
      have := GlobalTheory.dn_comp_monoidHom e.symm.toMonoidHom ρ' ρ h' (n + 1) f g
      rw [hd] at this
      exact this)
  refine ⟨fun x => c (fun i => e (x i)),
    hc.comp (continuous_pi fun i => he.comp (continuous_apply i)), ?_⟩
  funext g
  have := GlobalTheory.dn_comp_monoidHom e.toMonoidHom ρ ρ' h n c g
  rw [hcf] at this
  refine this.trans ?_
  exact congrArg f (funext fun i => e.symm_apply_apply _)

private theorem core {n : ℕ} [NeZero n] {G D M : Type} [Group G] [TopologicalSpace G] [Group D]
    [TopologicalSpace D] [AddCommGroup M] [Module (ZMod n) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (e : G ≃* D) (he : Continuous e) (he' : Continuous e.symm)
    (χG : G →* (ZMod n)ˣ) (χ : D →* (ZMod n)ˣ) (hχ : ∀ g, χ (e g) = χG g)
    (ρ : Representation (ZMod n) G M) (σ : Representation (ZMod n) D M) (h : ∀ g m, ρ g m = σ (e g) m)
    (c : ℕ) (f1 : Finite (H1 σ)) (f2 : Finite (H2 σ)) (f3 : ∀ m, 3 ≤ m → Subsingleton (Hn σ m))
    (hj : Nonempty (H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod n] ZMod n))
    (hb : Function.Bijective (cup20 χ σ (MonoidHom.id _)))
    (hE : Nat.card (H1 σ) = Nat.card (H0 σ) * Nat.card (H2 σ) * c) :
    Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ (∀ m, 3 ≤ m → Subsingleton (Hn ρ m)) ∧
      Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) * c ∧
      Nat.card (H2 ρ) = Nat.card (H0dual χG ρ) := by
  obtain ⟨⟨e1⟩, ⟨e2⟩, -⟩ := GlobalTheory.contCohomology_transport_mulEquiv _ _ _ M e he he' σ ρ h
  obtain ⟨j⟩ := hj
  have h0 : H0 ρ = H0 σ := by
    ext m
    rw [mem_riemannRochSpace_iff_regularAt_everywhere, mem_riemannRochSpace_iff_regularAt_everywhere]
    refine ⟨fun hm g => ?_, fun hm g => (h g m).trans (hm _)⟩
    obtain ⟨g, rfl⟩ := e.surjective g
    exact (h g m).symm.trans (hm g)
  refine ⟨Finite.of_equiv _ e1, Finite.of_equiv _ e2, fun m hm => ?_, ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact hn_transport e he he' σ ρ h k (f3 _ hm)
  · rw [← Nat.card_congr e1, ← Nat.card_congr e2, h0, hE]
  · have hfin : Finite (TDual (ZMod n) M) := DFunLike.finite _
    let E : H2 σ ≃ Module.Dual (ZMod n) (H0 ((twDual χ σ).comp (MonoidHom.id _))) :=
      (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight j).toEquiv
    rw [← Nat.card_congr e2, Nat.card_congr E, GlobalTheory.ZModDual.card_dual_eq]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun f : TDual (ZMod n) M => ?_)
    change (∀ g, twDual χ σ g f = f) ↔ ∀ g x, f (ρ g x) = ((χG g : (ZMod n)ˣ) : ZMod n) * f x
    constructor
    · intro hf g x
      have := congrArg (fun ψ : TDual (ZMod n) M => ψ (σ (e g) x)) (hf (e g))
      simp only [twDual_apply] at this
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, hχ] at this
      rw [h, this]
    · intro hf g
      obtain ⟨g, rfl⟩ := e.surjective g
      refine TDual.ext fun x => ?_
      rw [twDual_apply, hχ, ← hf, h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]

theorem UpperTheory.finiteLevel_cyclotomic_of_openEmbedding :
    LocalPublishedTheorems → ∀ {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ v), IsOpenEmbedding φ → FinLevelMod l G ((cyc v l).comp φ) (if v = l then φ.range.index else 0) := by
  intro P v l _ _ G _ _ _ φ hφ r hr M _ _ _ _ _ ρ hρ
  have hl : l.Prime := Fact.out
  have hv : v.Prime := Fact.out
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨K, e, he, he', hc, -, hi, -⟩ := openField φ hφ
  have hc' : ∀ g, ((e g : ↥(GK K)) : GQ v) = φ g := fun g => DFunLike.congr_fun hc g
  have hK := K.2
  by_cases hvl : v = l
  · subst hvl
    rw [if_pos rfl, hi]
    obtain ⟨hf, hf'⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[v] (PadicAlgCl v) K.1
    let ε : G ≃* Formalism.GaloisCohomology.GK v K.1 := e.trans (IntermediateField.fixingSubgroupEquiv K.1)
    have hε : Continuous ε := hf.comp he
    have hε' : Continuous ε.symm := he'.comp hf'
    let σ : Representation (ZMod (v ^ r)) (Formalism.GaloisCohomology.GK v K.1) M := ρ.comp ε.symm.toMonoidHom
    have hσ : ReciprocityTheory.Gal.ContAction σ := hρ.comp' hε'
    obtain ⟨-, f1, f2, f3⟩ := P.lfK v K.1 hK r M σ hr hσ
    obtain ⟨hj, -, -, -, hb⟩ := P.ltK v K.1 hK r M σ hr hσ
    refine core ε hε hε' _ _ (fun g => ?_) ρ σ (fun g m => by simp [σ]) _ f1 f2 f3 hj hb
      (P.leK v K.1 hK r M σ hr hσ)
    simp only [MonoidHom.comp_apply, ← hc']
    rfl
  · rw [if_neg hvl, pow_zero]
    let Ω := AlgebraicClosure ℚ
    have : IsAlgClosure ℚ Ω := AlgebraicClosure.instIsAlgClosure ℚ
    let j : Ω →+* PadicAlgCl v := (IsAlgClosed.lift (R := ℚ) (S := Ω) (M := PadicAlgCl v)).toRingHom
    let A : ValuationSubring Ω := (Valued.v (R := PadicAlgCl v)).valuationSubring.comap j
    have hA : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1 := fun x => by
      change Valued.v (j x) ≤ 1 ↔ _
      rw [PadicAlgCl.valuation_def]
      exact Iff.rfl
    have hAv : A.valuation (v : Ω) < 1 := by
      have h0 : 0 < ‖(v : PadicAlgCl v)‖ := norm_pos_iff.2 (by exact_mod_cast hv.ne_zero)
      have h1 : ((v : Ω))⁻¹ ∉ A := by
        rw [hA, map_inv₀, map_natCast, norm_inv, not_le]
        exact (one_lt_inv₀ h0).2 GlobalTheory.PlaceBridge.norm_l_lt_one
      rw [← A.valuation_le_one_iff, not_le, map_inv₀] at h1
      exact (one_lt_inv₀ (zero_lt_iff.2 (by simpa using hv.ne_zero))).1 h1
    obtain ⟨F, hF, hKF⟩ := numField K j A hA
    have : NumberField F := ⟨⟩
    have : IsAlgClosure F Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) F⟩
    obtain ⟨w, hw, hwl⟩ := placeBelow hv F A hAv
    obtain ⟨d, hd, hd', hdc⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hA K hKF
    let ε := e.trans d.symm
    have hε : Continuous ε := hd'.comp he
    have hε' : Continuous ε.symm := he'.comp hd
    let σ : Representation (ZMod (l ^ r)) _ M := ρ.comp ε.symm.toMonoidHom
    have hσ : ReciprocityTheory.Gal.ContAction σ := hρ.comp' hε'
    obtain ⟨-, f1, f2, f3⟩ := P.lf F Ω l r M A σ w hr hw hσ
    obtain ⟨hj, -, -, -, hb⟩ := P.lt F Ω l r M A σ w hr hw hσ
    refine core ε hε hε' _ ((cycMod F Ω l r).comp (Subgroup.subtype _)) (fun g => Units.ext ?_) ρ σ
      (fun g m => by simp [σ]) _ f1 f2 f3 hj hb
      (((P.le F Ω l r M A σ w hr hw hσ).2 (hwl l hl hvl)).trans (mul_one _).symm)
    have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
    have : NeZero ((l : ℕ) : PadicAlgCl v) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
    have hζ' := hζ.map_of_injective j.injective
    have ha : (ε g : Ω ≃ₐ[F] Ω) ζ = ζ ^ ((cycMod F Ω l r (ε g : Ω ≃ₐ[F] Ω) : ZMod (l ^ r))).val :=
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[F] Ω) Ω (ε g : Ω ≃ₐ[F] Ω)) ζ
        hζ.pow_eq_one
    have hb : φ g (j ζ) = j ζ ^ (PadicInt.toZModPow r ((cyc v l (φ g) : ℤ_[l]ˣ) : ℤ_[l])).val :=
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ v) (PadicAlgCl v) (φ g)) _
        hζ'.pow_eq_one
    have h3 : φ g (j ζ) = j ((ε g : Ω ≃ₐ[F] Ω) ζ) := by
      rw [← hdc, ← hc']
      simp [ε]
    rw [h3, ha, map_pow] at hb
    exact ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)

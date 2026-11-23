import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.FdAdjoinRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsIntBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ToGalDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PoitouTateDualityOfNormalised

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem fd_adjoin_range (l : ℕ) [Fact l.Prime] {ι : Type} [Finite ι] (f : ι → PadicAlgCl l) :
    FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range f)) := by
  haveI : Finite (Set.range f) := (Set.finite_range _).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral

private theorem char_finext (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] (ψ : Γ →* (PadicAlgCl l)ˣ) (hψ : IsOpen (ψ.ker : Set Γ)) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ g, (ψ g : PadicAlgCl l) ∈ K := by
  haveI : Finite (Γ ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hψ
  refine ⟨_, fd_adjoin_range l (fun q : Γ ⧸ ψ.ker => (ψ q.out : PadicAlgCl l)), fun g => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ψ.ker g
  refine IntermediateField.subset_adjoin _ _ ⟨(g : Γ ⧸ ψ.ker), ?_⟩
  have h1 : ψ (h : Γ) = 1 := h.2
  simp only [hh, map_mul, h1, mul_one]

open TensorProduct in

private theorem desc {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] (φ : H →* GQ l)
    (κ : H →* (PadicAlgCl l)ˣ) (E₀ : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E₀]
    (hκ : ∀ g, (κ g : PadicAlgCl l) ∈ E₀) (c : H → PadicAlgCl l) (hc : c ∈ Loc.finiteCocycles φ (Loc.chRep κ)) :
    ∃ (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (_ : FiniteDimensional ℚ_[l] E) (κ' : H →* Eˣ) (c' : H → E),
      (∀ g, ((κ' g : E) : PadicAlgCl l) = κ g) ∧ (∀ g, (c' g : PadicAlgCl l) = c g) ∧ c' ∈ Loc.finiteCocycles φ (Loc.chRep κ') := by
  obtain ⟨⟨hcc, hcoc⟩, x, hx⟩ := hc
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  obtain ⟨T⟩ := Loc.tiedP l
  haveI : IsDomain (Loc.Bcr l) := GlobalTheory.RegularRing.isDomain_of_tied T (Loc.botExt l)
  haveI := fd_adjoin_range l (fun p : S => p.1.1)
  let E : IntermediateField ℚ_[l] (PadicAlgCl l) := E₀ ⊔ IntermediateField.adjoin ℚ_[l] (Set.range fun p : S => p.1.1)
  have hκE : ∀ g, (κ g : PadicAlgCl l) ∈ E := fun g => (le_sup_left : E₀ ≤ E) (hκ g)
  have hS : ∀ p ∈ S, p.1 ∈ E := fun p hp =>
    (le_sup_right : _ ≤ E) (IntermediateField.subset_adjoin _ _ ⟨⟨p, hp⟩, rfl⟩)
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E (PadicAlgCl l))
    (LinearMap.ker_eq_bot.2 (algebraMap E (PadicAlgCl l)).injective)
  have hπ1 : ∀ y : E, π (y : PadicAlgCl l) = y := fun y => LinearMap.congr_fun hπ y
  let κ' : H →* Eˣ := MonoidHom.toHomUnits
    { toFun := fun g => ⟨κ g, hκE g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }
  have hκ' : ∀ g, ((κ' g : E) : PadicAlgCl l) = κ g := fun g => rfl
  have hπ2 : ∀ g y, π (κ g * y) = κ' g * π y := fun g y => map_smul π (κ' g : E) y
  let f : PadicAlgCl l →ₗ[ℚ_[l]] E := π.restrictScalars ℚ_[l]
  let i : E →ₗ[ℚ_[l]] PadicAlgCl l := E.val.toLinearMap
  have key : ∀ g (y : PadicAlgCl l ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) f (Loc.actC φ (Loc.chRep κ) g y) =
      Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Loc.actC, Loc.chRep, f, hπ2]
    | add a b ha hb => simp only [map_add, ha, hb]
  have key' : ∀ g (y : E ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) i (Loc.actC φ (Loc.chRep κ') g y) =
      Loc.actC φ (Loc.chRep κ) g (LinearMap.rTensor (Loc.Bcr l) i y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Loc.actC, Loc.chRep, i, hκ']
    | add a b ha hb => simp only [map_add, ha, hb]
  set x := ∑ p ∈ S, p.1 ⊗ₜ[ℚ_[l]] p.2 with hxd
  have hix : LinearMap.rTensor (Loc.Bcr l) i (LinearMap.rTensor (Loc.Bcr l) f x) = x := by
    rw [hxd, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    congr 1
    exact congrArg Subtype.val (hπ1 ⟨p.1, hS p hp⟩)
  have hx' : ∀ g, f (c g) ⊗ₜ[ℚ_[l]] (1 : Loc.Bcr l) =
      Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f x) - LinearMap.rTensor (Loc.Bcr l) f x := fun g => by
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
  have hcE : ∀ g, ((f (c g) : E) : PadicAlgCl l) = c g := fun g => by
    have h1 := congrArg (LinearMap.rTensor (Loc.Bcr l) i) (hx' g)
    rw [map_sub, key', hix, ← hx g, LinearMap.rTensor_tmul] at h1
    exact Algebra.TensorProduct.includeLeft_injective (R := ℚ_[l]) (S := ℚ_[l]) (B := Loc.Bcr l)
      (algebraMap ℚ_[l] (Loc.Bcr l)).injective h1
  refine ⟨E, inferInstance, κ', fun g => f (c g), hκ', hcE, ⟨?_, fun g h => ?_⟩, _, hx'⟩
  · exact continuous_induced_rng.2 (hcc.congr fun g => (hcE g).symm)
  · have := hcoc g h
    simp only [Loc.chRep] at this ⊢
    simp [this, f, hπ2]

private theorem cob_conj {Γ k : Type} [Group Γ] [Field k] (θ : Γ →* kˣ) (c : Γ → k)
    (hc : ∀ g h, c (g * h) = c g + θ g * c h) (S S' : Subgroup Γ) (g : Γ) (hS : ∀ s ∈ S', g⁻¹ * s * g ∈ S)
    (h : ∃ m, ∀ s ∈ S, c s = θ s * m - m) : ∃ m, ∀ s ∈ S', c s = θ s * m - m := by
  obtain ⟨m, hm⟩ := h
  refine ⟨θ g * m - c g, fun s hs => ?_⟩
  have h1 := hm _ (hS s hs)
  have h2 := hc g (g⁻¹ * s * g)
  have h3 := hc s g
  have h4 : θ (g⁻¹ * s * g) = θ s := by rw [map_mul, map_mul, map_inv, mul_comm _ (θ s), inv_mul_cancel_right]
  rw [show g * (g⁻¹ * s * g) = s * g by group, h3, h1, h4] at h2
  linear_combination h2

open scoped Pointwise in
private theorem conj_place {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) :
    ∃ g : G k Ω, (∀ τ ∈ Ine (F := k) B, g⁻¹ * τ * g ∈ Ine (F := k) A) ∧ ∀ τ ∈ Dec (F := k) B, g⁻¹ * τ * g ∈ Dec (F := k) A := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := k) hA hB
  have h : IsLift (RingEquiv.refl k) g.toRingEquiv := fun x => g.commutes x
  have hm : ∀ x, g.toRingEquiv x ∈ B ↔ x ∈ A := fun x => by
    show g • x ∈ B ↔ _
    rw [← hg]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  exact ⟨g, fun τ hτ => conjGal_mem_Ine h hm hτ, fun τ hτ => conjGal_mem_Dec h hm hτ⟩

private theorem unr_zero (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (l : ℕ) [Fact l.Prime] (f : G K Ω → PadicAlgCl l) (hf : Continuous f) (hm : ∀ g h, f (g * h) = f g + f h)
    (hI : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := K) A, f g = 0) (g : G K Ω) : f g = 0 := by
  let F : G K Ω →* Multiplicative (PadicAlgCl l) := MonoidHom.mk' (fun g => Multiplicative.ofAdd (f g)) hm
  have hpow : ∀ g (n : ℕ), n ≠ 0 → f (g ^ n) = 0 → f g = 0 := fun g n hn h => by
    have h1 : f (g ^ n) = n • f g := congrArg Multiplicative.toAdd (map_pow F g n)
    rw [h, nsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (Nat.cast_ne_zero.2 hn)
  have h1 : f 1 = 0 := congrArg Multiplicative.toAdd (map_one F)
  have key : ∀ g ∈ (Kum.artCl K Ω).ker, f g = 0 := fun g hg => by
    by_contra h0
    have hr : 0 < ‖f g‖ := norm_pos_iff.2 h0
    let B : OpenAddSubgroup (PadicAlgCl l) := IsUltrametricDist.ball_openAddSubgroup (PadicAlgCl l) hr
    let χ : G K Ω →* Multiplicative (PadicAlgCl l ⧸ B.toAddSubgroup) :=
      (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' B.toAddSubgroup)).comp F
    have hχ : ∀ s, χ s = 1 ↔ f s ∈ B := fun s => QuotientAddGroup.eq_zero_iff (f s)
    have := Kum.artKer K Ω _ χ (by
        have : (χ.ker : Set (G K Ω)) = f ⁻¹' B := Set.ext hχ
        rw [this]
        exact B.isOpen.preimage hf)
      (fun A s hs => (hχ s).2 (by rw [hI A s hs]; exact zero_mem _))
      (fun c hc => (hχ c).2 (by
        obtain ⟨j, hj⟩ := hc
        have h2 : c ^ 2 = 1 := AlgEquiv.ext fun x => j.injective (by
          rw [pow_two, AlgEquiv.mul_apply]
          exact (hj _).trans ((congrArg _ (hj x)).trans (Complex.conj_conj _)))
        rw [hpow c 2 two_ne_zero (by rw [h2, h1])]
        exact zero_mem _)) hg
    have h3 : f g ∈ Metric.ball (0 : PadicAlgCl l) ‖f g‖ := (hχ g).1 this
    simp at h3
  refine hpow g (Nat.card (ClassGroup (𝓞 K))) Nat.card_pos.ne' (key _ ?_)
  rw [MonoidHom.mem_ker, map_pow, pow_card_eq_one']

section Char

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

private theorem bk_loc (θ : G ℚ Ω →* (PadicAlgCl l)ˣ) (c : G ℚ Ω → PadicAlgCl l) (hc : c ∈ Z1 (Loc.chRep θ))
    (hb : Af.IsBK l (Loc.chRep θ) c) :
    (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∃ m, ∀ g ∈ Ine (F := ℚ) A, c g = θ g * m - m) ∧
    ∃ j : Ω →+* Om l, (fun σ => c (Loc.iota j σ)) ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) (Loc.chRep (θ.comp (Loc.iota j))) ∧
      (Loc.placeJ j).valuation (l : Ω) < 1 ∧ ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ g : G ℚ Ω,
        (∀ τ ∈ Ine (F := ℚ) A, g⁻¹ * τ * g ∈ Ine (F := ℚ) (Loc.placeJ j)) ∧
        ∀ τ ∈ Dec (F := ℚ) A, g⁻¹ * τ * g ∈ Dec (F := ℚ) (Loc.placeJ j) := by
  have hcoc : ∀ g h, c (g * h) = c g + θ g * c h := hc.2
  refine ⟨fun A hA => ?_, ?_⟩
  · obtain ⟨p1, p2, p3, -⟩ := places ℚ Ω l A
    by_cases hT : A = ⊤
    · refine ⟨0, fun g hg => ?_⟩
      rw [(p2 hT).1, Subgroup.mem_bot] at hg
      have := hcoc 1 1
      simp only [mul_one, map_one, Units.val_one, one_mul] at this
      rw [hg, left_eq_add.1 this]
      simp
    obtain ⟨v, hv⟩ := p1 hT
    obtain ⟨B, hB, hx⟩ := hb.away v fun h => hA ((p3 v hv).2 h)
    obtain ⟨g, hg, -⟩ := conj_place hB hv
    exact cob_conj θ c hcoc _ _ g hg hx
  · obtain ⟨j, -, -, x, hx⟩ := hb.above (algebraMap ℚ (Om l))
    obtain ⟨i1, -, -, -, -, i6, -⟩ := Loc.iotaFacts j
    refine ⟨j, ⟨⟨hc.1.comp i1.continuous, fun g h => ?_⟩, x, fun σ => ?_⟩, ?_, fun A hA => ?_⟩
    · exact (congrArg c (map_mul _ g h)).trans (hc.2 _ _)
    · exact hx ⟨(Loc.iota j σ, σ), fun y => (Loc.iota_spec j σ y).symm⟩
    · rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
      refine Or.inr fun h => ?_
      have h1 : (Valued.v : Valuation (Om l) NNReal) (j (l : Ω)⁻¹) ≤ 1 := h
      rw [map_inv₀, map_natCast, map_inv₀, PadicAlgCl.valuation_p, one_div, inv_inv] at h1
      exact absurd (Nat.cast_le_one.1 h1) (Fact.out : l.Prime).one_lt.not_ge
    · obtain ⟨p1, p2, p3, -⟩ := places ℚ Ω l A
      obtain ⟨v, hv⟩ := p1 fun h => (p2 h).2 hA
      exact conj_place ((i6 v).2 ((p3 v hv).1 hA)) hv

private theorem neg_case (hP : CohInp) (θ χ : G ℚ Ω →* (PadicAlgCl l)ˣ) (hχ : IsOpen (χ.ker : Set (G ℚ Ω))) (e : ℕ)
    (he : 1 ≤ e) (hθc : Continuous fun g => (θ g : PadicAlgCl l))
    (hθ : ∀ g, (θ g : PadicAlgCl l) * χ g * algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ e = 1)
    (c : G ℚ Ω → PadicAlgCl l) (hc : c ∈ Z1 (Loc.chRep θ)) (hb : Af.IsBK l (Loc.chRep θ) c) :
    ∃ m, ∀ g, c g = θ g * m - m := by
  have hcoc : ∀ g h, c (g * h) = c g + θ g * c h := hc.2
  obtain ⟨CK, hK⟩ := hP.lemK
  obtain ⟨h1, j, hj, -, h2⟩ := bk_loc θ c hc hb
  obtain ⟨i1, i2, -, -, i5, -, -⟩ := Loc.iotaFacts j
  obtain ⟨K₀, hK₀, hψK⟩ := char_finext l (G ℚ Ω) χ hχ
  have hθK : ∀ g, (θ g : PadicAlgCl l) ∈ K₀ := fun g => by
    have h := hθ g
    rw [mul_assoc] at h
    rw [eq_inv_of_mul_eq_one_left h]
    refine inv_mem (mul_mem (hψK g) (pow_mem ?_ _))
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact K₀.algebraMap_mem _
  obtain ⟨E, _, κ, c', hκ, hc', hf⟩ := desc _ (θ.comp (Loc.iota j)) K₀ (fun g => hθK _) _ hj
  haveI : IsModuleTopology ℚ_[l] E := isModuleTopologyOfFiniteDimensional
  have hw : Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
    refine ⟨χ.ker.comap (Loc.iota j), hχ.preimage i1.continuous, fun g hg _ => ?_⟩
    rw [_root_.zpow_neg, zpow_natCast]
    refine eq_inv_of_mul_eq_one_left (Units.ext (Subtype.ext ?_))
    have h3 := hθ (Loc.iota j g)
    have h4 : χ (Loc.iota j g) = 1 := hg
    have h5 : cycZ ℚ Ω l (Loc.iota j g) = Loc.cyc l l g := DFunLike.congr_fun (i5 l) g
    rw [h4, h5, Units.val_one, mul_one] at h3
    rw [Units.val_mul, MulMemClass.coe_mul, hκ, Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow]
    exact h3
  have hz := (Loc.z1fChar hP.loc (MonoidHom.id (GQ l)) Topology.IsOpenEmbedding.id κ
    (continuous_induced_rng.2 ((hθc.comp i1.continuous).congr fun g => (hκ g).symm)) _ hw).1 (by omega)
  rw [hz.1, mem_coboundaries1] at hf
  obtain ⟨m, hm⟩ := hf
  have h3 : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ m, ∀ g ∈ Dec (F := ℚ) A, c g = θ g * m - m := by
    intro A hA
    obtain ⟨g, -, hg⟩ := h2 A hA
    refine cob_conj θ c hcoc _ _ g hg ⟨m, fun s hs => ?_⟩
    rw [← i2] at hs
    obtain ⟨σ, rfl⟩ := hs
    have h4 : c' σ = κ σ * m - m := hm σ
    have h5 := hc' σ
    rw [← h5, h4, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hκ]
    rfl
  refine X.soBar CK hK (GlobalTheory.PoitouTateConj.poitouTateDuality_of_normalised hP.pt) hP.loc.lfK hP.loc.ltK ℚ Ω l χ hχ e he
    (fun g => θ g) hθ c hc.1 hcoc (fun A => ?_) h3
  by_cases hA : A.valuation (l : Ω) < 1
  · obtain ⟨m, hm⟩ := h3 A hA
    exact ⟨m, fun g hg => hm g hg.1⟩
  · exact h1 A hA

private theorem zero_case (hP : CohInp) (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    (θ : G ℚ Ω →* (PadicAlgCl l)ˣ) (hθ : galOf ℚ K Ω ≤ θ.ker)
    (hI : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ galOf ℚ K Ω)
    (c : G ℚ Ω → PadicAlgCl l) (hc : c ∈ Z1 (Loc.chRep θ)) (hb : Af.IsBK l (Loc.chRep θ) c) :
    ∀ g ∈ galOf ℚ K Ω, c g = 0 := by
  have hcoc : ∀ g h, c (g * h) = c g + θ g * c h := hc.2
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  obtain ⟨g1, g2, -⟩ := galEmbTop ℚ K Ω
  obtain ⟨-, hIne, -, -⟩ := Kum.toGalDict ℚ Ω K _ le_rfl
  have hχ : IsOpen (θ.ker : Set (G ℚ Ω)) := Subgroup.isOpen_mono hθ g2
  have hθc : Continuous θ := continuous_of_continuousAt_one θ (by
    refine (continuousAt_const (y := (1 : (PadicAlgCl l)ˣ))).congr ?_
    filter_upwards [hχ.mem_nhds θ.ker.one_mem] with g hg using hg.symm)
  obtain ⟨h1, j, hj, hjl, h2⟩ := bk_loc θ c hc hb
  obtain ⟨i1, -, -, i4, -, -, -⟩ := Loc.iotaFacts j
  obtain ⟨K₀, hK₀, hψK⟩ := char_finext l (G ℚ Ω) θ hχ
  obtain ⟨E, _, κ, c', hκ, hc', hf⟩ := desc _ (θ.comp (Loc.iota j)) K₀ (fun g => hψK _) _ hj
  haveI : IsModuleTopology ℚ_[l] E := isModuleTopologyOfFiniteDimensional
  have hκc : Continuous fun g => (κ g : E) :=
    continuous_induced_rng.2 (((Units.continuous_val.comp hθc).comp i1.continuous).congr fun g => (hκ g).symm)
  have hz := (Loc.z1fUnr hP.loc (MonoidHom.id (GQ l)) Topology.IsOpenEmbedding.id (Loc.chRep κ)
    ((hκc.comp continuous_fst).mul continuous_snd) (fun g hg => by
      have h3 : θ (Loc.iota j g) = 1 := hθ (hI _ hjl (i4 ▸ ⟨g, hg, rfl⟩))
      have h4 : (κ g : E) = 1 := Subtype.ext ((hκ g).trans (congrArg Units.val h3))
      refine LinearMap.ext fun y => ?_
      change (κ g : E) * y = y
      rw [h4, one_mul]) c' hf.1).1 hf
  have h3 : ∀ A : ValuationSubring Ω, ∃ m, ∀ g ∈ Ine (F := ℚ) A, c g = θ g * m - m := by
    intro A
    by_cases hA : A.valuation (l : Ω) < 1
    · obtain ⟨g, hg, -⟩ := h2 A hA
      refine cob_conj θ c hcoc _ _ g hg ⟨0, fun s hs => ?_⟩
      rw [← i4] at hs
      obtain ⟨σ, hσ, rfl⟩ := hs
      have h5 := hc' σ
      rw [← h5, hz σ hσ]
      simp
    · exact h1 A hA
  have h4 : ∀ s : G K Ω, θ (galEmb ℚ K Ω s) = 1 := fun s => hθ (galEmb_mem ℚ K Ω s)
  intro g hg
  rw [← range_galEmb] at hg
  obtain ⟨s, rfl⟩ := hg
  refine unr_zero K Ω l (fun s => c (galEmb ℚ K Ω s)) (hc.1.comp g1.continuous) (fun s t => ?_) (fun A s hs => ?_) s
  · rw [map_mul, hcoc, h4, Units.val_one, one_mul]
  · obtain ⟨m, hm⟩ := h3 A
    rw [hm _ ((hIne A ⟨_, galEmb_mem ℚ K Ω s⟩).1 hs), h4, Units.val_one, one_mul, sub_self]

end Char

private theorem wt_rev (a b : Fin 3) : wt b.rev a.rev = wt a b := by
  revert a b
  decide

theorem UpperTheory.V.U3.bloch_kato_nonpositive_weight :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (j : ℤ), j ≤ 0 → ∀ γ ∈ Z1 (adRep (r0 D.η D.ΨQ)), (∀ g, γ g ∈ gw (PadicAlgCl l) j) →
      Af.IsBK l (adRep (r0 D.η D.ΨQ)) γ → γ ∈ ReciprocityTheory.Gal.B1 (adRep (r0 D.η D.ΨQ)) := by
  intro hP Ω _ _ _ K _ _ _ l _ c N _ e ψ D j hj γ hγ hw hb
  obtain ⟨d1, d2, d3, d4, -, -, -, -, d5, -, d6⟩ := dat_facts D
  let η : G ℚ Ω →* (PadicAlgCl l)ˣ := (Units.map (Int.castRingHom (PadicAlgCl l)).toMonoidHom).comp D.η
  have hη1 : ∀ g, D.η g = 1 → η g = 1 := fun g h => by simp [η, h]
  have hη2 : ∀ g, D.η g ≠ 1 → η g = -1 := fun g h => by
    apply Units.ext
    simp [η, (Int.units_eq_one_or _).resolve_left h]
  have hηo : IsOpen (D.η.ker : Set (G ℚ Ω)) := d4.isOpen_fiber 1

  have hch : ∀ (θ : G ℚ Ω →* (PadicAlgCl l)ˣ), θ = 1 ∨ θ = η → ∀ f ∈ Z1 (Loc.chRep (D.ΨQ ^ j * θ)),
      Af.IsBK l (Loc.chRep (D.ΨQ ^ j * θ)) f → ∃ m, ∀ g, f g = (D.ΨQ g ^ j * θ g : (PadicAlgCl l)ˣ) * m - m := by
    intro θ hθ f hf hfb
    have hk : D.η.ker ≤ θ.ker := fun g hg => by
      rcases hθ with rfl | rfl
      · rfl
      · exact hη1 g hg
    rcases hj.eq_or_lt with rfl | hj
    · simp only [zpow_zero, one_mul] at hf hfb ⊢
      have hcoc : ∀ g h, f (g * h) = f g + θ g * f h := hf.2
      have h0 := zero_case hP K θ (D.η_ker ▸ hk) (fun A hA => D.η_ker ▸ (d6 A hA).1) f hf hfb
      rw [← D.η_ker] at h0
      have h1 : ∀ g, D.η g ≠ 1 → f g = f D.cc := fun g hg => by
        have h2 : g * D.cc ∈ D.η.ker := by
          rw [MonoidHom.mem_ker, map_mul, d2, (Int.units_eq_one_or _).resolve_left hg]
          simp
        have h3 := hcoc (g * D.cc) D.cc
        rwa [mul_assoc, d1, mul_one, h0 _ h2, show θ (g * D.cc) = 1 from hk h2, Units.val_one, one_mul, zero_add] at h3
      refine ⟨-f D.cc / 2, fun g => ?_⟩
      by_cases hg : D.η g = 1
      · rw [h0 g hg, show θ g = 1 from hk hg]
        simp
      · rw [h1 g hg]
        rcases hθ with rfl | rfl
        · have h3 := hcoc D.cc D.cc
          rw [d1, h0 1 (one_mem _)] at h3
          simp only [MonoidHom.one_apply, Units.val_one] at h3 ⊢
          linear_combination (-1 / 2 : PadicAlgCl l) * h3
        · rw [hη2 g hg]
          simp only [Units.val_neg, Units.val_one]
          ring
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
      let ψQ : G ℚ Ω →* (PadicAlgCl l)ˣ :=
        (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)
      have hθc : Continuous θ := continuous_of_continuousAt_one θ (by
        refine (continuousAt_const (y := (1 : (PadicAlgCl l)ˣ))).congr ?_
        filter_upwards [hηo.mem_nhds D.η.ker.one_mem] with g hg using (hk hg).symm)
      refine neg_case hP _ (ψQ ^ n * θ⁻¹) ?_ (e * n) (Nat.mul_pos D.gd.e_pos (by omega))
        (Units.continuous_val.comp ((d5.zpow _).mul hθc)) (fun g => ?_) f hf hfb
      · refine Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω N).ker ⊓ D.η.ker) (fun g hg => ?_)
          ((Chr.clsFacts ℚ Ω N).1.inter hηo)
        have h1 : Chr.cls ℚ Ω N g = 1 := hg.1
        have h2 : θ g = 1 := hk hg.2
        simp [ψQ, Chr.dirG, h1, h2]
      · have h1 : (D.ΨQ g : PadicAlgCl l) = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ e * ψQ g := by
          simp [Dat.ΨQ, Dat.Ψ, Chr.Psi, chiO, ψQ]
        simp only [MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul,
          _root_.zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, pow_mul]
        have h2 := (D.ΨQ g).ne_zero
        have h3 := (θ g).ne_zero
        field_simp
        rw [h1, mul_pow, mul_comm]

  have hpr : ∀ (s : PadicAlgCl l) (θ : G ℚ Ω →* (PadicAlgCl l)ˣ), (s = -1 ∧ θ = 1) ∨ (s = 1 ∧ θ = η) → ∀ a b : Fin 3,
      ∃ m, ∀ g, γ g a b + s * γ g b.rev a.rev = (D.ΨQ g ^ wt a b * θ g : (PadicAlgCl l)ˣ) * m - m := by
    intro s θ hs a b
    by_cases hab : wt a b = j
    swap
    · exact ⟨0, fun g => by rw [hw g a b hab, hw g _ _ (by rwa [wt_rev])]; simp⟩
    let f : Matrix (Fin 3) (Fin 3) (PadicAlgCl l) →ₗ[ℚ_[l]] PadicAlgCl l :=
      { toFun := fun X => X a b + s * X b.rev a.rev
        map_add' := fun X Y => by simp only [Matrix.add_apply]; ring
        map_smul' := fun r X => by simp only [Matrix.smul_apply, RingHom.id_apply, smul_add, mul_smul_comm] }
    have hfc : Continuous f := by
      change Continuous fun X : Matrix (Fin 3) (Fin 3) (PadicAlgCl l) => X a b + s * X b.rev a.rev
      fun_prop
    have hfe : ∀ g X, f (adRep (r0 D.η D.ΨQ) g X) = Loc.chRep (D.ΨQ ^ j * θ) g (f X) := fun g X => by
      change adRep (r0 D.η D.ΨQ) g X a b + s * adRep (r0 D.η D.ΨQ) g X b.rev a.rev =
        (D.ΨQ g ^ j * θ g : (PadicAlgCl l)ˣ) * (X a b + s * X b.rev a.rev)
      rw [adRep_baseLift_apply, adRep_baseLift_apply, wt_rev, hab, Fin.rev_rev, Fin.rev_rev, Units.val_mul]
      by_cases hg : D.η g = 1
      · rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [hg, mul_add]
        · simp [hg, hη1 g hg, mul_add]
      · rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [hg, if_false, MonoidHom.one_apply, Units.val_one]
          ring
        · simp only [hg, if_false, hη2 g hg, Units.val_neg, Units.val_one]
          ring
    rw [hab]
    refine hch θ (hs.imp And.right And.right) (fun g => f (γ g)) ⟨hfc.comp hγ.1, fun g h => ?_⟩
      ⟨fun w hw => ?_, fun τ => ?_⟩
    · exact (congrArg f (hγ.2 g h)).trans (by rw [map_add, hfe])
    · obtain ⟨A, hA, x, hx⟩ := hb.away w hw
      exact ⟨A, hA, f x, fun s hs => by rw [hx s hs, map_sub, hfe]⟩
    · obtain ⟨i, hi, hx⟩ := hb.above τ
      refine ⟨i, hi, Loc.z1fCoef _ _ _ f hfc ?_ _ hx⟩
      exact fun g x => hfe g.1.1 x
  choose p hp using hpr 1 η (Or.inr ⟨rfl, rfl⟩)
  choose q hq using hpr (-1) 1 (Or.inl ⟨rfl, rfl⟩)
  refine (mem_coboundaries1 _ _).2 ⟨Matrix.of fun a b => (p a b + p b.rev a.rev + q a b - q b.rev a.rev) / 4, fun g => ?_⟩
  ext a b
  have h1 := hp a b g
  have h2 := hp b.rev a.rev g
  have h3 := hq a b g
  have h4 := hq b.rev a.rev g
  rw [Matrix.sub_apply, adRep_baseLift_apply]
  simp only [wt_rev, Fin.rev_rev, Units.val_mul, MonoidHom.one_apply, Units.val_one, Matrix.of_apply] at h1 h2 h3 h4 ⊢
  by_cases hg : D.η g = 1
  · rw [hη1 g hg, Units.val_one] at h1 h2
    rw [if_pos hg]
    linear_combination (h1 + h2 + h3 - h4) / 4
  · rw [hη2 g hg, Units.val_neg, Units.val_one] at h1 h2
    rw [if_neg hg]
    linear_combination (h1 + h2 + h3 - h4) / 4

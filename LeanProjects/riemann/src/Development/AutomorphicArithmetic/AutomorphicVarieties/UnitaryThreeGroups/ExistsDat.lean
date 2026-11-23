import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.UnramIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem dx_cc (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] :
    ∃ σ : G ℚ Ω, ∃ φ : Ω →+* ℂ, ∀ x, φ (σ x) = starRingEnd ℂ (φ x) := by
  obtain ⟨σ, h⟩ := exists_isConjOm (E := ℚ) (Ω := Ω)
  exact ⟨AlgEquiv.ofRingEquiv (f := σ) fun x => by rw [eq_ratCast (algebraMap ℚ Ω), map_ratCast], h⟩

private theorem dx_ker (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    [IsGalois ℚ K] (σ : G ℚ Ω) : AlgEquiv.restrictNormalHom (F := ℚ) K σ = 1 ↔ σ ∈ galOf ℚ K Ω := by
  have h : ∀ x : K, algebraMap K Ω (AlgEquiv.restrictNormalHom (F := ℚ) K σ x) = σ (algebraMap K Ω x) :=
    fun x => AlgEquiv.restrictNormal_commutes σ K x
  refine ⟨fun h1 x => ?_, fun h1 => AlgEquiv.ext fun x => (algebraMap K Ω).injective ?_⟩
  · rw [← h, h1]; rfl
  · rw [h, h1]; rfl

private theorem dx_eta (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    [IsGalois ℚ K] (h2 : Module.finrank ℚ K = 2) : ∃ η : G ℚ Ω →* ℤˣ, η.ker = galOf ℚ K Ω := by
  have hc : Nat.card Gal(K/ℚ) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  have hz : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  let e : Gal(K/ℚ) ≃* ℤˣ := mulEquivOfPrimeCardEq hc hz
  refine ⟨e.toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := ℚ) K), Subgroup.ext fun σ => ?_⟩
  rw [← dx_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
  exact map_eq_one_iff e e.injective

private theorem dx_unr (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] [IsGalois ℚ K] (l : ℕ) [hl : Fact l.Prime] (h : ¬ (l : ℤ) ∣ discr K) (A : ValuationSubring Ω)
    (hA : A.valuation (l : Ω) < 1) : Ine (F := ℚ) A ≤ galOf ℚ K Ω := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨p1, p2, p3, -⟩ := places K Ω l A
  obtain ⟨w, hw⟩ := p1 fun ht => (p2 ht).2 hA
  have hm : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal := (p3 w hw).1 hA
  have hb := (CF.unramIff.1 K l hl.out).1 ((CF.unramIff.2.1 K l hl.out).2 h) w hm
  intro σ hσ
  have h1 := Subgroup.mem_map_of_mem (CF.resTo ℚ K Ω) hσ
  rw [CF.ineAbs ℚ K Ω A w hw, hb, Subgroup.mem_bot] at h1
  exact (dx_ker Ω K σ).1 h1

private theorem dx_lc {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group M] (f : Γ →* M)
    (h : IsOpen (f.ker : Set Γ)) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : Γ => x⁻¹ * y := by fun_prop
  have h1 : (fun y : Γ => x⁻¹ * y) ⁻¹' (f.ker : Set Γ) ∈ nhds x :=
    (h.preimage hc).mem_nhds (by simp)
  filter_upwards [h1] with y hy
  have h2 : f (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2.symm

private theorem dx_zpow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R)
    (Ψ : Γ → Rˣ) (h : AdicCont I fun g => (Ψ g : R)) (j : ℤ) : AdicCont I fun g => ((Ψ g ^ j : Rˣ) : R) := by
  classical
  intro N
  have key : (fun g => Ideal.Quotient.mk (I ^ N) ((Ψ g ^ j : Rˣ) : R)) =
      (fun x : R ⧸ I ^ N => if hx : IsUnit x then ((hx.unit ^ j : (R ⧸ I ^ N)ˣ) : R ⧸ I ^ N) else 0) ∘
        fun g => Ideal.Quotient.mk (I ^ N) (Ψ g : R) := by
    funext g
    have hx : IsUnit (Ideal.Quotient.mk (I ^ N) (Ψ g : R)) := (Ψ g).isUnit.map _
    have e : hx.unit = Units.map (Ideal.Quotient.mk (I ^ N)).toMonoidHom (Ψ g) := Units.ext rfl
    simp only [Function.comp_apply, dif_pos hx]
    rw [e, ← map_zpow]
    rfl
  rw [key]
  exact (h N).comp _

private theorem dx_alg {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] R]
    (I : Ideal R) (hI : (l : R) ∈ I) (f : Γ → ℤ_[l]) (hf : Continuous f) :
    AdicCont I fun g => algebraMap ℤ_[l] R (f g) := by
  intro n
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [hf.continuousAt.eventually (Metric.closedBall_mem_nhds (f x) hpos)] with y hy
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton'] at hy
  obtain ⟨a, ha⟩ := hy
  rw [Ideal.Quotient.eq, ← map_sub, ← ha, map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hI n)

private theorem dx_lmem (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] : (l : O) ∈ IsLocalRing.maximalIdeal O := by
  have h : (IsLocalRing.maximalIdeal O).comap (algebraMap ℤ_[l] O) = IsLocalRing.maximalIdeal ℤ_[l] :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
  have h1 : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  rw [← h, Ideal.mem_comap, map_natCast] at h1
  exact h1

private theorem dx_dir (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter O N) : IsLocallyConstant (Chr.dirG ℚ Ω ψ) :=
  (dx_lc _ (Chr.clsFacts ℚ Ω N).1).comp ψ.toUnitHom

private theorem dx_cont (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter O N) : CharCont (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) := by
  refine dx_zpow _ _ fun n => ?_
  have h1 : AdicCont (IsLocalRing.maximalIdeal O) fun g => (chiO ℚ Ω l O g : O) :=
    dx_alg _ (dx_lmem l O) (fun g => (cycZ ℚ Ω l g : ℤ_[l])) (Units.continuous_val.comp (contTw ℚ Ω l).1)
  have h2 := dx_zpow _ _ h1 (e : ℤ) n
  have h3 := (dx_dir Ω ψ).comp fun u : Oˣ => Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n) (u : O)
  have h4 := h2.mul h3
  convert h4 using 1
  funext g
  simp only [Chr.Psi, MonoidHom.mul_apply, Units.val_mul, map_mul, Pi.mul_apply, Function.comp_apply]
  rfl

private theorem dx_place {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [hl : Fact l.Prime] (j : Ω →+* Om l) :
    (Loc.placeJ j).valuation (l : Ω) < 1 := by
  have h0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have h1 : (l : Ω)⁻¹ ∉ Loc.placeJ j := by
    intro h
    have h2 : ‖j (l : Ω)⁻¹‖ ≤ 1 := h
    have h3 : j (l : Ω)⁻¹ = algebraMap ℚ_[l] (Om l) (l : ℚ_[l])⁻¹ := by simp
    rw [h3, PadicAlgCl.norm_extends, norm_inv, Padic.norm_p, inv_inv] at h2
    exact absurd hl.out.one_lt (by exact_mod_cast h2.not_gt)
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, not_le,
    one_lt_inv₀ ((Valuation.pos_iff _).2 h0)] at h1
  exact h1

theorem UpperTheory.V.U3.exists_dat :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}, GD Ω K l e ψ → Nonempty (Dat Ω K c e ψ) := by
  intro Ω _ _ _ K _ _ _ l hl c N _ e ψ h
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h.quad⟩
  haveI : IsGalois ℚ K := inferInstance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨η, hη⟩ := dx_eta Ω K h.quad
  obtain ⟨cc, hcc⟩ := dx_cc Ω
  obtain ⟨j⟩ := Loc.exists_emb (Ω := Ω) (v := l)
  obtain ⟨i1, -, i3, -, i5, -⟩ := Loc.iotaFacts j
  have hA : (Loc.placeJ j).valuation (l : Ω) < 1 := dx_place j
  have hI : ∀ g ∈ Loc.Iq l, Loc.iota j g ∈ Ine (F := ℚ) (Loc.placeJ j) := fun g hg => by
    rw [← i3] at hg; exact hg
  have hopen : IsOpen (((η.comp (Loc.iota j)).ker : Subgroup (GQ l)) : Set (GQ l)) := by
    have h1 := (galEmbTop ℚ K Ω).2.1
    rw [← hη] at h1
    exact h1.preimage i1.continuous
  obtain ⟨Kv, -, -, -, -, hKv, -⟩ := Loc.openField (η.comp (Loc.iota j)).ker.subtype hopen.isOpenEmbedding_subtypeVal
  rw [Subgroup.range_subtype] at hKv
  have hd : ¬ (l : ℤ) ∣ discr K := fun hd => h.l_cop (Dvd.dvd.mul_right (Int.natCast_dvd.1 hd) _)
  exact ⟨{
    gd := h
    η := η
    η_ker := hη
    cc := cc
    conj := hcc
    j := j
    ι := Loc.iota j
    ι_cont := i1.continuous
    ι_spec := fun σ x => (Loc.iota_spec j σ x).symm
    Kv := Kv
    Kv_spec := fun g => by rw [← hKv]; rfl
    η_unr := fun g hg => by
      have h1 := dx_unr Ω K l hd _ hA (hI g hg)
      rw [← hη] at h1
      exact h1
    τ_open := ((dx_dir Ω (comp l ψ)).comp_continuous i1.continuous).isOpen_fiber 1
    Ψ_cont := dx_cont Ω e ψ
    Ψ_I := fun g hg => by
      rw [← ((compIne Ω N l hl.out _ hA).2 c.O ψ).1 _ (hI g hg), Chr.Psi, MonoidHom.mul_apply, zpow_natCast,
        MonoidHom.pow_apply, Loc.cycA, ← i5 l]
      rfl }⟩

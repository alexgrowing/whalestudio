import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneRankOneLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneCharacterTwistPeriod
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CrystallinePeriodRingProperties

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Wd

private theorem cw_cyc {l : ℕ} [Fact l.Prime] (L : FinExt l) (n : ℤ) :
    Continuous fun g : GQ l => (((cycL L g ^ n : (↥L.1)ˣ) : ↥L.1) : Om l) := by
  have h0 := UpperTheory.V.Loc.cycFacts l l
  have h1 : Continuous fun g : GQ l => (((cycL L g : (↥L.1)ˣ) : ↥L.1) : Om l) := by
    have : (fun g : GQ l => (((cycL L g : (↥L.1)ˣ) : ↥L.1) : Om l)) =
        fun g => algebraMap ℚ_[l] (Om l) (((Loc.cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
      funext g
      rw [← h0.2.2 g]
      rfl
    rw [this]
    have h2 : Continuous fun z : ℤ_[l] => (z : ℚ_[l]) := continuous_subtype_val
    exact (continuous_algebraMap ℚ_[l] (Om l)).comp (h2.comp (Units.continuous_val.comp h0.1))
  have : (fun g : GQ l => (((cycL L g ^ n : (↥L.1)ˣ) : ↥L.1) : Om l)) =
      fun g => (((cycL L g : (↥L.1)ˣ) : ↥L.1) : Om l) ^ n := by
    funext g
    rw [Units.val_zpow_eq_zpow_val]
    exact map_zpow₀ L.1.val _ _
  rw [this]
  exact h1.zpow₀ n fun g => Or.inl (by simp)

private theorem cw_lc {l : ℕ} [Fact l.Prime] (K K' : FinExt l) {C : Type} [Group C] (χ : ↥(GK K) →* C)
    (hχ : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → χ g = 1) : IsLocallyConstant χ := by
  have := K'.2
  have ho : IsOpen ((GK K' : Subgroup (GQ l)) : Set (GQ l)) := IntermediateField.fixingSubgroup_isOpen K'.1
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  refine ⟨{y | ((x⁻¹ * y : ↥(GK K)) : GQ l) ∈ GK K'}, ?_, ?_, fun y hy => ?_⟩
  · exact ho.preimage (continuous_subtype_val.comp (continuous_const.mul continuous_id))
  · simp
  · have := hχ _ hy
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm

private theorem cw_eta {l : ℕ} [Fact l.Prime] (K K' L : FinExt l) (κ χ : ↥(GK K) →* (↥L.1)ˣ) (m : ℤ)
    (hκc : Continuous (fun g => ((κ g : ↥L.1) : Om l)))
    (hK' : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → χ g = 1) :
    ∃ η : ↥(GK K) →* (↥L.1)ˣ, (∀ g, κ g = cycL L (g : GQ l) ^ m * χ g * η g) ∧
      Continuous (fun g => ((η g : ↥L.1) : Om l)) := by
  let ε : ↥(GK K) →* (↥L.1)ˣ := (cycL L).comp (GK K).subtype
  refine ⟨κ * ε ^ (-m) * χ⁻¹, fun g => ?_, ?_⟩
  · change κ g = _ * (κ g * cycL L (g : GQ l) ^ (-m) * (χ g)⁻¹)
    rw [zpow_neg]
    generalize cycL L (g : GQ l) ^ m = a
    rw [mul_mul_mul_comm, mul_inv_cancel, mul_one, mul_comm (κ g), mul_inv_cancel_left]
  · have h3 : Continuous fun g => ((((χ g)⁻¹ : (↥L.1)ˣ) : ↥L.1) : Om l) :=
      ((cw_lc K K' χ hK').comp fun u => (((u⁻¹ : (↥L.1)ˣ) : ↥L.1) : Om l)).continuous
    exact (hκc.mul ((cw_cyc L (-m)).comp continuous_subtype_val)).mul h3

private theorem cw_line {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw)
    (L : FinExt l) (V : Type) [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) (h1 : finrank ↥L.1 V = 1) (hV : IsPst P ρ)
    (u : V ⊗[ℚ_[l]] Bst P) (hmem : u ∈ Dpst P ρ) (hu0 : u ≠ 0) (e : ↥L.1) (he0 : e ≠ 0)
    (hu : e • (phiV P ↥L.1 V ^ resDeg l w) u = u) (σ : ↥(Weil h)) (s : ↥L.1)
    (hs : stRep P ρ (weilToGK Bw h σ) u = s • u) (y : WDSpace P ι ρ) :
    haveI := hV.finite; wdRho P ι Bw h hj ρ σ y = ι ((e⁻¹ ^ (-deg σ) * s : ↥L.1) : Om l) • y := by
  refine UpperTheory.weil_deligne_rank_one_line F Ω l P ι w A h O Bw hj L V ρ h1 hV ⟨u, hmem⟩ (fun h0 => hu0 (congrArg Subtype.val h0)) e⁻¹
    (inv_ne_zero he0) (Subtype.ext ?_) σ s (Subtype.ext hs) y
  have h1 : ((phiD P ρ ^ resDeg l w) ⟨u, hmem⟩).1 = (phiV P ↥L.1 V ^ resDeg l w) u := by
    rw [phiD, Module.End.pow_restrict]
    rfl
  rw [h1, Submodule.coe_smul, eq_inv_smul_iff₀ he0]
  exact hu

private theorem cw_calc {k : Type} [Field k] (a κ c χ η : kˣ) (l : k) (m d : ℤ) (f : ℕ) (h1 : κ = c ^ m * χ * η)
    (h2 : η = a ^ d) :
    ((a : k) * l ^ (m * (f : ℕ)))⁻¹ ^ (-d) * (χ : k) = (l ^ f) ^ (m * d) * ((κ * c ^ (-m) : kˣ) : k) := by
  have h3 : κ * c ^ (-m) = a ^ d * χ := by
    rw [h1, h2, zpow_neg, mul_comm, mul_assoc (c ^ m), inv_mul_cancel_left, mul_comm]
  rw [h3, inv_zpow', neg_neg, mul_zpow, ← zpow_natCast, ← zpow_mul, ← zpow_mul, Units.val_mul,
    Units.val_zpow_eq_zpow_val, show m * (f : ℕ) * d = (f : ℕ) * (m * d) by ring]
  ring

private theorem cw_fin {l : ℕ} [Fact l.Prime] (ι : Om l ≃+* ℂ) (L : FinExt l) (f : ℕ) (n : ℤ) (x : ↥L.1) :
    ι (((((l : ↥L.1) ^ f) ^ n * x : ↥L.1)) : Om l) = ((l ^ f : ℕ) : ℂ) ^ n * ι (x : Om l) := by
  have h1 : L.1.val (((l : ↥L.1) ^ f) ^ n * x) = ((l : Om l) ^ f) ^ n * L.1.val x := by
    rw [map_mul, map_zpow₀, map_pow, map_natCast]
  refine (congrArg ι h1).trans ?_
  rw [map_mul, map_zpow₀, map_pow, map_natCast, Nat.cast_pow]
  rfl

private theorem cw_unr {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : Induces Bw) {C : Type} [Group C] (η : ↥(GK Bw.Kw) →* C)
    (hηI : ∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ Loc.Iq l → η g = 1) (σ : ↥(Weil h)) :
    η (weilToGK Bw h σ) = η (weilToGK Bw h (frob h)) ^ deg σ := by
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
  have hτI : (weilToGK Bw h (ineIncl h τ) : GQ l) ∈ Loc.Iq l := by
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
    have := weilToGK_frobUr hj (ineIncl h τ) (a := 0) (b := 0) (actsAs_zero_iff.mpr τ.2) ⟨x, hx⟩
    simpa using this
  conv_lhs => rw [hτ]
  rw [map_mul, map_mul, hηI _ hτI, mul_one, map_zpow, map_zpow]

theorem UpperTheory.cyclotomicWeilChar_properties :
    UpperTheory.V.Af.Wd.CharWD := by
  intro F Ω _ _ _ _ _ l _ ι w A h O _ _ _ Bw hj L κ χ m hκc hχ hI hκ σ y
  obtain ⟨K', hK'⟩ := hχ
  obtain ⟨η, hκη, hηc⟩ := cw_eta Bw.Kw K' L κ χ m hκc hK'
  have hηI : ∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ Loc.Iq l → η g = 1 := fun g hg =>
    mul_left_cancel ((hκη g).symm.trans ((hI g hg).trans (mul_one _).symm))
  obtain ⟨u, hu0, hu1, hu2⟩ := UpperTheory.weilDeligne_character_twist_period l Bw.Kw L κ χ η m hκη hηc hηI
  have hF := (UpperTheory.crystalline_period_ring_properties F Ω l w A h O Bw hj).1
  have hmem : u ∈ Dpst (Loc.PP l) (Loc.chRep κ) :=
    (mem_Dpst _ _).2 ⟨K', fun g hg => by rw [hu1, hK' g hg, Units.val_one, one_smul]⟩
  have hl : (l : ↥L.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have he0 : (η (weilToGK Bw h (frob h)) : ↥L.1) * (l : ↥L.1) ^ (m * (resDeg l w : ℕ)) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (zpow_ne_zero _ hl)
  have key := cw_line (Loc.PP l) ι h Bw hj L ↥L.1 (Loc.chRep κ) (Module.finrank_self _) hκ u hmem hu0 _ he0
    (hu2 _ _ hF) σ _ (hu1 _) y
  have h3 := cw_calc _ _ _ _ _ (l : ↥L.1) m (deg σ) (resDeg l w) (hκη (weilToGK Bw h σ)) (cw_unr h Bw hj η hηI σ)
  have h4 := (congrArg (fun x : ↥L.1 => ι (x : Om l)) h3).trans (cw_fin ι L _ _ _)
  rw [← normV_eq_pow (hj.mem_placesOver h)] at h4
  exact key.trans (congrArg (fun z : ℂ => z • y) h4)

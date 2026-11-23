import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CardH2GaussianField

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise

namespace GlobalTheory.PoitouTateConj

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def conjBack (σ : Ω ≃+* Ω) (τ : F ≃+* F) (hστ : ∀ x, σ (algebraMap F Ω x) = algebraMap F Ω (τ x)) :
    G F Ω →* G F Ω where
  toFun g := AlgEquiv.ofRingEquiv (f := (σ.trans g.toRingEquiv).trans σ.symm) (fun x => by
    simp only [RingEquiv.trans_apply, hστ, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    rw [← hστ, RingEquiv.symm_apply_apply])
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

theorem conjBack_apply (σ : Ω ≃+* Ω) (τ : F ≃+* F) (hστ : ∀ x, σ (algebraMap F Ω x) = algebraMap F Ω (τ x))
    (g : G F Ω) (x : Ω) : conjBack σ τ hστ g x = σ.symm (g (σ x)) := rfl

theorem apply_conjBack (σ : Ω ≃+* Ω) (τ : F ≃+* F) (hστ : ∀ x, σ (algebraMap F Ω x) = algebraMap F Ω (τ x))
    (g : G F Ω) (x : Ω) : σ (conjBack σ τ hστ g x) = g (σ x) := by
  rw [conjBack_apply, RingEquiv.apply_symm_apply]

theorem mem_Dec_of_forall {A : ValuationSubring Ω} {g : G F Ω} (h : ∀ x, g x ∈ A ↔ x ∈ A) :
    g ∈ Dec (F := F) A := by
  show g • A = A
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← h, mul_inv_apply]

variable (σ : Ω ≃+* Ω) (τ : F ≃+* F) (hστ : ∀ x, σ (algebraMap F Ω x) = algebraMap F Ω (τ x))
  {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A)
include hA

theorem valuation_le_one_iff_of_map (x : Ω) :
    A'.valuation (σ x) ≤ 1 ↔ A.valuation x ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff, hA]

theorem valuation_lt_one_iff_of_map (x : Ω) :
    A'.valuation (σ x) < 1 ↔ A.valuation x < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', hA, ← map_inv₀, hA, map_eq_zero_iff _ σ.injective]

omit hA in
include hA in
theorem conjBack_mem_Dec {g : G F Ω} (hg : g ∈ Dec (F := F) A') :
    conjBack σ τ hστ g ∈ Dec (F := F) A :=
  mem_Dec_of_forall fun x => by
    rw [← hA, apply_conjBack, apply_mem_iff_of_mem_Dec hg, hA]

omit hA in
include hA in
theorem conjBack_mem_Ine {g : G F Ω} (hg : g ∈ Ine (F := F) A') :
    conjBack σ τ hστ g ∈ Ine (F := F) A := by
  refine ⟨conjBack_mem_Dec σ τ hστ hA hg.1, fun x hx => ?_⟩
  rw [← valuation_lt_one_iff_of_map σ hA, map_sub, apply_conjBack]
  exact hg.2 _ ((valuation_le_one_iff_of_map σ hA x).2 hx)

omit hA in
include hA in
theorem conjBack_isFrob {q : ℕ} {g : G F Ω} (hg : IsFrob A' q g) :
    IsFrob A q (conjBack σ τ hστ g) := by
  refine ⟨conjBack_mem_Dec σ τ hστ hA hg.1, fun x hx => ?_⟩
  rw [← valuation_lt_one_iff_of_map σ hA, map_sub, apply_conjBack, map_pow]
  exact hg.2 _ ((valuation_le_one_iff_of_map σ hA x).2 hx)

omit hA in
theorem cycMod_conjBack (l : ℕ) [Fact l.Prime] (r : ℕ) (g : G F Ω) :
    cycMod F Ω l r (conjBack σ τ hστ g) = cycMod F Ω l r g := by
  have e : MulSemiringAction.toRingAut (G F Ω) Ω (conjBack σ τ hστ g) =
      σ⁻¹ * MulSemiringAction.toRingAut (G F Ω) Ω g * σ := by
    ext x; rfl
  simp only [cycMod, cycZ, MonoidHom.comp_apply, e, map_mul, map_inv]
  rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]

omit hA in

theorem continuous_conjBack [Algebra.IsAlgebraic F Ω] : Continuous (conjBack σ τ hστ) := by
  haveI : Algebra.IsIntegral F Ω := inferInstance
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  rw [Filter.mem_map]
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff F Ω s).1 hs
  let b := Module.finBasis F E
  have hU : IsOpen (⋂ i, (MulAction.stabilizer (G F Ω) (σ (b i : Ω)) : Set (G F Ω))) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral _
  refine Filter.mem_of_superset (hU.mem_nhds (Set.mem_iInter.2 fun i => (MulAction.stabilizer (G F Ω) _).one_mem)) fun g hg => hEs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hb : ∀ i, conjBack σ τ hστ g (b i) = b i := fun i => by
    have := Set.mem_iInter.1 hg i
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
    rw [conjBack_apply, this, RingEquiv.symm_apply_apply]
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : Ω) := by
    have := congrArg E.val (b.sum_repr ⟨x, hx⟩)
    rw [map_sum] at this
    simp only [map_smul] at this
    exact this.symm
  rw [hx', map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hb]

omit hA in
include hA hστ in

theorem exists_place_map {v : HeightOneSpectrum (𝓞 F)} (hAv : IsPlaceOver A v) :
    ∃ v' : HeightOneSpectrum (𝓞 F), IsPlaceOver A' v' ∧ normV v' = normV v ∧
      ∀ ϖ : 𝓞 F, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∃ ϖ' : 𝓞 F, ϖ' ∈ v'.asIdeal ∧
        ϖ' ∉ v'.asIdeal ^ 2 ∧ algebraMap F Ω (ϖ' : F) = σ (algebraMap F Ω (ϖ : F)) := by
  let e : 𝓞 F ≃+* 𝓞 F := RingOfIntegers.mapRingEquiv τ
  have he : ∀ x : 𝓞 F, ((e x : 𝓞 F) : F) = τ (x : F) := fun x => rfl
  let v' : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := v.asIdeal.map (e : 𝓞 F →+* 𝓞 F)
      isPrime := Ideal.map_isPrime_of_equiv e
      ne_bot := by
        rw [Ne, Ideal.map_eq_bot_iff_of_injective (f := (e : 𝓞 F →+* 𝓞 F)) e.injective]
        exact v.ne_bot }
  have hmem : ∀ x : 𝓞 F, x ∈ v'.asIdeal ↔ e.symm x ∈ v.asIdeal := fun x => by
    show x ∈ v.asIdeal.map (e : 𝓞 F →+* 𝓞 F) ↔ _
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap]
  refine ⟨v', fun x => ?_, ?_, fun ϖ h1 h2 => ⟨e ϖ, ?_, ?_, ?_⟩⟩
  · rw [hmem, ← hAv, ← valuation_lt_one_iff_of_map σ hA, hστ]
    congr 3
    rw [← he, RingEquiv.apply_symm_apply]
  · unfold normV
    exact Nat.card_congr (Ideal.quotientEquiv v.asIdeal v'.asIdeal e rfl).toEquiv.symm
  · rw [hmem, RingEquiv.symm_apply_apply]; exact h1
  · show e ϖ ∉ (v.asIdeal.map (e : 𝓞 F →+* 𝓞 F)) ^ 2
    rw [← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_apply_apply]
    exact h2
  · rw [he, hστ]

end GlobalTheory.PoitouTateConj

namespace GlobalTheory.PoitouTateConj
open GlobalTheory.Published GlobalTheory.Published.PoitouTate

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [hl : Fact l.Prime] {r : ℕ}

theorem conjCompatible (hr : 0 < r) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (l ^ r)) {inv : InvFam F Ω l r}
    (h : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
      Function.Bijective (inv A) ∧ IsNormalised ζ A v (inv A)) :
    ConjCompatible ζ inv := by
  intro σ τ hστ c hc A A' v hAv hA z z' hz
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  let ψ : Dec (F := F) A' →* Dec (F := F) A :=
    ((conjBack σ τ hστ).comp (Dec (F := F) A').subtype).codRestrict (Dec (F := F) A)
      (fun g => conjBack_mem_Dec σ τ hστ hA g.2)
  have hψv : ∀ g : Dec (F := F) A', ((ψ g : Dec (F := F) A) : G F Ω) = conjBack σ τ hστ g := fun _ => rfl
  have hψc : Continuous ψ :=
    (((continuous_conjBack σ τ hστ).comp continuous_subtype_val)).subtype_mk _
  have hψ : ∀ (g' : Dec (F := F) A') x, (g' : G F Ω) (σ x) = σ (((ψ g' : Dec (F := F) A) : G F Ω) x) :=
    fun g' x => (apply_conjBack σ τ hστ g' x).symm
  have hcyc : ∀ g' : Dec (F := F) A',
      ((cycMod F Ω l r ((ψ g' : Dec (F := F) A) : G F Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) =
        ((cycMod F Ω l r (g' : G F Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) := fun g' => by
    rw [hψv, cycMod_conjBack]
  have hz' : ∀ p, z'.1 p = c * z.1 (ψ p.1, ψ p.2) := fun p => hz _ _ p.1 p.2 (hψ p.1) (hψ p.2)

  have hTZ : ∀ w : Z2 (muLoc F l r A),
      (fun p : Dec (F := F) A' × Dec (F := F) A' => c * w.1 (ψ p.1, ψ p.2)) ∈ Z2 (muLoc F l r A') := by
    intro w
    refine ⟨continuous_const.mul (w.2.1.comp ((hψc.comp continuous_fst).prodMk (hψc.comp continuous_snd))),
      fun g h k => ?_⟩
    have e := w.2.2 (ψ g) (ψ h) (ψ k)
    simp only [charRep_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul] at e ⊢
    rw [← hcyc g]
    linear_combination c * e
  have hTB : ∀ f : Dec (F := F) A → ZMod (l ^ r), Continuous f →
      ∃ f' : Dec (F := F) A' → ZMod (l ^ r), Continuous f' ∧
        ∀ p, d1 (muLoc F l r A') f' p = c * d1 (muLoc F l r A) f (ψ p.1, ψ p.2) := by
    intro f hf
    refine ⟨fun g => c * f (ψ g), continuous_const.mul (hf.comp hψc), fun p => ?_⟩
    simp only [d1, LinearMap.coe_mk, AddHom.coe_mk, charRep_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype, map_mul]
    rw [← hcyc p.1]
    ring

  obtain ⟨χ, h1, h2, h3, h4⟩ := GlobalTheory.Published.PoitouTate.Model.exists_unramified hAv (n := l ^ r)
    (Nat.one_lt_pow hr.ne' hl.out.one_lt)
  obtain ⟨ϖ, y, κ, z0, ha, hb, hy, hκ, hz0e⟩ :=
    GlobalTheory.Published.PoitouTate.Model.exists_kummer hζ A v χ h1 h2
  have hz0 : inv A (Submodule.Quotient.mk z0) = 1 := (h A v hAv).2 ϖ y κ χ z0 ha hb hy hκ h1 h3 h4 hz0e
  set a := inv A (Submodule.Quotient.mk z) with ha_def
  have hzz : (Submodule.Quotient.mk z : H2 (muLoc F l r A)) = Submodule.Quotient.mk (a • z0) := by
    rw [Submodule.Quotient.mk_smul]
    exact (h A v hAv).1.1 (by rw [map_smul, hz0, smul_eq_mul, mul_one])
  rw [Submodule.Quotient.eq] at hzz
  obtain ⟨f, hf, hfe⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 hzz)
  obtain ⟨f', hf', hf'e⟩ := hTB f hf

  obtain ⟨v', hA'v', hN, hϖ⟩ := exists_place_map σ τ hστ hA hAv
  obtain ⟨ϖ', ha', hb', hϖe⟩ := hϖ ϖ ha hb
  let z0' : Z2 (muLoc F l r A') := ⟨_, hTZ z0⟩
  have hpow : ∀ s t : ZMod (l ^ r), ζ ^ (s * t).val = ζ ^ (s.val * t.val) := fun s t => by
    rw [ZMod.val_mul]
    conv_rhs => rw [← Nat.mod_add_div (s.val * t.val) (l ^ r), pow_add, pow_mul, hζ.pow_eq_one,
      one_pow, mul_one]
  have hz0' : inv A' (Submodule.Quotient.mk z0') = 1 := by
    refine (h A' v' hA'v').2 ϖ' (σ y) (fun g => c * κ (ψ g)) (fun g => χ (ψ g)) z0' ha' hb' ?_ ?_
      ?_ ?_ ?_ ?_
    · rw [← map_pow, hy, hϖe]
    · intro g
      rw [hψ, hκ, map_mul, map_pow, hc, ← pow_mul, hpow]
    · intro g h; rw [map_mul, h1]
    · intro g hg; exact h3 _ (by rw [hψv]; exact conjBack_mem_Ine σ τ hστ hA hg)
    · intro g hg; exact h4 _ (by rw [hψv]; rw [hN] at hg; exact conjBack_isFrob σ τ hστ hA hg)
    · intro g h; show c * z0.1 (ψ g, ψ h) = _; rw [hz0e]; ring
  have hzz' : (Submodule.Quotient.mk z' : H2 (muLoc F l r A')) = Submodule.Quotient.mk (a • z0') := by
    rw [Submodule.Quotient.eq]
    refine Submodule.mem_comap.2 (Submodule.mem_map.2 ⟨f', hf', ?_⟩)
    funext p
    rw [hf'e, hfe]
    show _ = z'.1 p - a * (c * z0.1 (ψ p.1, ψ p.2))
    rw [hz']
    show c * (z.1 _ - a * z0.1 _) = _
    ring
  rw [hzz', Submodule.Quotient.mk_smul, map_smul, hz0', smul_eq_mul, mul_one]

theorem poitouTateDuality_of_normalised (h : PoitouTateNormalised) : PoitouTateDuality := by
  intro F Ω _ _ _ _ _ l _ r hl hr ζ hζ
  obtain ⟨inv, h1, h2⟩ := h F Ω l r hl hr ζ hζ
  exact ⟨inv, ⟨h1, conjCompatible hr hζ h1⟩, h2⟩

end GlobalTheory.PoitouTateConj

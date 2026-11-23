import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TauOneCharacter

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published.DepthZeroTypeModel
open GlobalTheory.SerSys.TameGen GlobalTheory.Published.DepthZeroModel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem v_lt_one (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) {k : ℚ_[g]} (hk : ‖k‖ < 1) :
    Valued.v (i k) < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => (i k) ^ n) Filter.atTop (nhds 0) := by
    have := (hi.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hk)
    simpa [Function.comp_def] using this
  have h2 : {y : w.adicCompletion E | Valued.v y < 1} ∈ nhds (0 : w.adicCompletion E) := by
    have : IsOpen {y : w.adicCompletion E | Valued.v y < 1} := by
      simpa using Valued.isOpen_ball (w.adicCompletion E) 1
    exact this.mem_nhds (by simp)
  obtain ⟨n, hn⟩ := (h1.eventually h2).exists
  simp only [map_pow] at hn
  by_contra hc
  exact absurd hn (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))

theorem rank_one {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {ε : EpsFamily A} {rc : IrrGL (w.adicCompletion E) → WD h} (hl : Laws a ha ε rc)
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
    (red : 𝓞 E →+* ZMod g) (hker : RingHom.ker red = w.asIdeal) (θ : (ZMod g)ˣ →* ℂˣ)
    (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : GlobalTheory.SmGL.IsSmoothChar χ)
    (hI : Inflates ((GlobalTheory.SmGL.IrrRep.det (Fin 1) χ hχ).ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) (tauOne θ)) :
    (rc (cls (GlobalTheory.SmGL.IrrRep.det (Fin 1) χ hχ))).mono0 ∧
      ∀ (t : Ine (F := E) A) (x : 𝓞 E) (z : (ZMod g)ˣ), red x = z →
        Valued.v ((a (ineIncl h t) : w.adicCompletion E) - algebraMap E (w.adicCompletion E) (x : E)) < 1 →
        (rc (cls (GlobalTheory.SmGL.IrrRep.det (Fin 1) χ hχ))).inePol (AlgEquiv.restrictScalars E (t : G E Ω)) =
          ∏ j ∈ Finset.range 1, (X - C ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) := by
  have h2 : rc (cls (GlobalTheory.SmGL.IrrRep.det (Fin 1) χ hχ)) = _ := hl.one χ hχ
  rw [h2]
  refine ⟨by rw [WD.lpOfChar, WD.monodromyZero_ofWeilDeligneRepClass_iff]; rfl, fun t x z hz hv => ?_⟩
  have e0 : AlgEquiv.restrictScalars E (t : G E Ω) = (t : G E Ω) := rfl
  rw [e0, WD.inePol_of_mem_Ine _ t.2, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  suffices H : χ (a (ineIncl h t)) = θ z by simp [← H]
  set u := a (ineIncl h t)
  have hval : ∀ y : 𝓞 E, Valued.v (algebraMap E (w.adicCompletion E) (y : E)) < 1 ↔ red y = 0 := fun y => by
    rw [← RingHom.mem_ker, hker, ← w.valuation_lt_one_iff_mem (K := E) y]
    rw [show Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _]

  set m : ℕ := (z : ZMod g).val with hm
  have hmz : ((m : ℕ) : ZMod g) = z := by simp [hm]
  have h3 : Valued.v ((u : w.adicCompletion E) - (m : w.adicCompletion E)) < 1 := by
    have h4 := (hval (x - m)).2 (by simp [hz, hmz])
    have : (u : w.adicCompletion E) - (m : w.adicCompletion E) =
        ((u : w.adicCompletion E) - algebraMap E (w.adicCompletion E) (x : E)) +
          algebraMap E (w.adicCompletion E) ((x - m : 𝓞 E) : E) := by simp
    rw [this]; exact Valuation.map_add_lt _ hv h4
  have h5 : ‖i.symm u - (m : ℚ_[g])‖ < 1 := by
    by_contra hc
    rcases (not_lt.1 hc).eq_or_lt with e | e
    ·
      let k : ℤ_[g] := ⟨_, e.ge⟩
      obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ZMod g) = PadicInt.toZMod k := ⟨_, ZMod.natCast_zmod_val _⟩
      have hk : ‖((k - r : ℤ_[g]) : ℚ_[g])‖ < 1 := by
        have : k - r ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by simp [RingHom.mem_ker, hr]
        rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at this
        exact this
      have h6 := v_lt_one i hi hk
      have h7 : i ((k - r : ℤ_[g]) : ℚ_[g]) = ((u : w.adicCompletion E) - m) - r := by
        rw [PadicInt.coe_sub]; simp [k]
      rw [h7] at h6
      have h8 : Valued.v (r : w.adicCompletion E) < 1 := by
        have := Valuation.map_sub_lt _ h3 h6
        simpa using this
      have h9 := (hval r).1 (by simpa using h8)
      have h10 : k ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by simpa [RingHom.mem_ker, hr] using h9
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at h10
      exact absurd e.symm (ne_of_lt h10)
    · have h0 : i.symm u - (m : ℚ_[g]) ≠ 0 := by intro e0; rw [e0] at e; norm_num at e
      have h6 := v_lt_one i hi (k := (i.symm u - (m : ℚ_[g]))⁻¹) (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ e)
      have h7 : Valued.v (i (i.symm u - (m : ℚ_[g]))) < 1 := by simpa using h3
      have h8 := mul_lt_one_of_nonneg_of_lt_one_left zero_le' h7 h6.le
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ h0] at h8
      simp at h8
  have hle : ‖i.symm u‖ ≤ 1 := by
    have := Padic.nonarchimedean (i.symm u - (m : ℚ_[g])) (m : ℚ_[g])
    rw [sub_add_cancel] at this
    exact this.trans (max_le h5.le (by exact_mod_cast Padic.norm_int_le_one (p := g) (m : ℤ)))
  let k : ℤ_[g] := ⟨_, hle⟩
  have hk : PadicInt.toZMod k = z := by
    have : k - m ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]; exact h5
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    simpa [hmz] using this
  have hku : IsUnit k := by
    by_contra hc
    have : k ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by rw [PadicInt.ker_toZMod]; exact hc
    exact z.ne_zero (hk ▸ this)
  obtain ⟨φ, hφ, hφ'⟩ := hI
  let κ : GL (Fin 1) ℤ_[g] := Matrix.GeneralLinearGroup.scalar (Fin 1) hku.unit
  have e1 : Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.red g 1 κ) = z := by
    ext; simp [GlobalTheory.GLp.red, κ, Matrix.GeneralLinearGroup.scalar, hk]
  have e2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 κ)) = u := by
    ext; simp [GlobalTheory.GLp.inc, κ, Matrix.GeneralLinearGroup.scalar]; exact congrArg _ (i.apply_symm_apply _)
  obtain ⟨v, hv0⟩ : ∃ v, φ v ≠ 0 := by
    by_contra hc; push_neg at hc; exact hφ (LinearMap.ext hc)
  have e3 := hφ' κ v
  change φ (((θ (Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.red g 1 κ)) : ℂˣ) : ℂ) • v) =
    ((χ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 κ))) : ℂˣ) : ℂ) • φ v at e3
  rw [e1, e2, map_smul] at e3
  exact Units.ext (smul_left_injective ℂ hv0 e3).symm

theorem tauOne_hyp (θ : (ZMod g)ˣ →* ℂˣ) : IsRegularChar g 1 θ ∧ IsCusp (tauOne θ).character ∧
    ∀ y : Gn g 1, Irreducible (y : Mt g 1).charpoly → ∀ z : (ZMod g)ˣ, aeval (z : ZMod g) (y : Mt g 1).charpoly = 0 →
      (tauOne θ).character y = (-1) ^ (1 - 1) * ∑ j ∈ Finset.range 1, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) := by
  refine ⟨fun i j hi hj _ => by omega, ⟨one_pos, ?_, fun a h1 h2 => by omega⟩, fun y _ z hz => ?_⟩
  · have := GlobalTheory.Published.GreenModel.isIrr_hom
      ((Units.coeHom ℂ).comp (θ.comp (Matrix.GeneralLinearGroup.det (n := Fin 1) (R := ZMod g))))
    convert this using 1
    funext y
    exact tauOne_character θ y
  · have hcp : (y : Mt g 1).charpoly = X - C ((y : Mt g 1) 0 0) := by
      simp [Matrix.charpoly, Matrix.det_fin_one]
    rw [hcp] at hz
    have : Matrix.GeneralLinearGroup.det y = z := Units.ext (by
      simp only [map_sub, aeval_X, aeval_C] at hz
      simpa using (sub_eq_zero.1 hz).symm)
    rw [tauOne_character, this]; simp

theorem hyp_exist (hL : LocalLanglandsGL) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : Nat.Primes) : haveI : Fact p.1.Prime := ⟨p.2⟩
    ∃ (w : HeightOneSpectrum (𝓞 ℚ)) (A : ValuationSubring Ω) (h : IsPlaceOver (F := ℚ) A w)
      (rc : IrrGL (w.adicCompletion ℚ) → WD h) (i : ℚ_[p.1] ≃+* w.adicCompletion ℚ)
      (a : Weil h →* (w.adicCompletion ℚ)ˣ) (red : 𝓞 ℚ →+* ZMod p.1),
      IsRec h rc ∧ Continuous i ∧ ((p.1 : ℕ) : 𝓞 ℚ) ∉ w.asIdeal ^ 2 ∧ normV w = p.1 ^ 1 ∧ IsLocalArtin h a ∧
      Function.Surjective red ∧ RingHom.ker red = w.asIdeal ∧ ∀ θ : (ZMod p.1)ˣ →* ℂˣ,
      ∃ σ : GlobalTheory.SmGL.IrrRep (GL (Fin 1) (w.adicCompletion ℚ)),
        Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) (tauOne θ) := by
  obtain ⟨w, rfl⟩ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).surjective p
  have : Fact (Rat.HeightOneSpectrum.primesEquiv w).1.Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv w).2⟩
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv w
  obtain ⟨rc, ⟨a, ha, ε, hε, hl⟩, -⟩ := hL.1 ℚ Ω A w hA
  let f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have hs := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) w
  have hmem : ∀ x : 𝓞 ℚ, x ∈ w.asIdeal ↔ ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℤ) ∣ f x := fun x => by
    rw [← Ideal.mem_span_singleton, hs, Ideal.apply_mem_of_equiv_iff]
  let red : 𝓞 ℚ →+* ZMod (Rat.HeightOneSpectrum.natGenerator w) := (Int.castRingHom _).comp f.toRingHom
  have hsur : Function.Surjective red := (ZMod.ringHom_surjective _)
  have hker : RingHom.ker red = w.asIdeal := by
    ext x; rw [hmem, RingHom.mem_ker, ← ZMod.intCast_zmod_eq_zero_iff_dvd]; rfl
  refine ⟨w, A, hA, rc, e.symm.toAlgEquiv.toRingEquiv, a, red, ⟨a, ha, ε, hε, hl⟩, e.symm.continuous, ?_, ?_, ha,
    hsur, hker, fun θ => ?_⟩
  · intro hc
    have h1 := Ideal.mem_map_of_mem f hc
    rw [Ideal.map_pow, ← hs, Ideal.span_singleton_pow, Ideal.mem_span_singleton, map_natCast] at h1
    have hp := Rat.HeightOneSpectrum.prime_natGenerator w
    change ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℤ) ^ 2 ∣ ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℤ) at h1
    have h2 : (Rat.HeightOneSpectrum.natGenerator w) ^ 2 ∣ Rat.HeightOneSpectrum.natGenerator w := by exact_mod_cast h1
    have := Nat.le_of_dvd hp.pos h2
    nlinarith [hp.two_le]
  · have := Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsur).toEquiv
    rw [hker, Nat.card_zmod] at this
    rw [pow_one]; exact this
  · obtain ⟨χ, hχ, hθ⟩ := exists_char e.symm.toAlgEquiv.toRingEquiv e.continuous θ
    exact ⟨_, inflates_one _ θ χ hχ hθ⟩

theorem apply_one (H : DepthZeroTypeInertia) {rc : IrrGL (w.adicCompletion E) → WD h} (hr : IsRec h rc)
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (h1 : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2) (h2 : normV w = g ^ 1)
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    (red : 𝓞 E →+* ZMod g) (hs : Function.Surjective red) (hker : RingHom.ker red = w.asIdeal) (θ : (ZMod g)ˣ →* ℂˣ)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin 1) (w.adicCompletion E)))
    (hI : Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) (tauOne θ)) :
    (rc (cls σ)).mono0 ∧
      ∀ (t : Ine (F := E) A) (x : 𝓞 E) (z : (ZMod g)ˣ), red x = z →
        Valued.v ((a (ineIncl h t) : w.adicCompletion E) - algebraMap E (w.adicCompletion E) (x : E)) < 1 →
        (rc (cls σ)).inePol (AlgEquiv.restrictScalars E (t : G E Ω)) =
          ∏ j ∈ Finset.range 1, (X - C ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) :=
  H E E Ω g A w h w h rc hr i hi 1 one_pos h1 h2 a ha (ZMod g) red hs hker θ (tauOne_hyp θ).1 _ (tauOne_hyp θ).2.1
    (tauOne_hyp θ).2.2 σ hI

theorem restrict_mem {E' : Type} [Field E'] [NumberField E'] [Algebra E E'] [Algebra E' Ω] [IsScalarTower E E' Ω]
    (t : Ine (F := E') A) : AlgEquiv.restrictScalars E (t : G E' Ω) ∈ Ine (F := E) A := ⟨t.2.1, t.2.2⟩

end GlobalTheory.Published.DepthZeroTypeModel

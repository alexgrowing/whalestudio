import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharFiniteOrderOfTrivialAtInfinityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AutomorphicArithmetic.WeightCongruences.ProdResidueCharNormOneUnitEqOne

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.DeltaZero

theorem exists_char_of_dvd {G : Type} [Group G] [IsCyclic G] {m : ℕ} (hm : m ≠ 0) (h : m ∣ Nat.card G) :
    ∃ θ : G →* ℂˣ, ∀ n : ℕ, θ ^ n = 1 ↔ m ∣ n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hζ := Complex.isPrimitiveRoot_exp m hm
  have hζ' := hζ.isUnit_unit hm
  set ζ : ℂˣ := (hζ.isUnit hm).unit
  have ho : orderOf ζ ∣ orderOf g := by
    rw [← hζ'.eq_orderOf, orderOf_eq_card_of_forall_mem_zpowers hg]
    exact h
  refine ⟨monoidHomOfForallMemZpowers hg ho, fun n => ?_⟩
  rw [MonoidHom.eq_iff_eq_on_generator hg, MonoidHom.pow_apply, monoidHomOfForallMemZpowers_apply_gen,
    MonoidHom.one_apply]
  exact hζ'.pow_eq_one_iff_dvd n

theorem exists_place_over (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ Q : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ Q.asIdeal := by
  have hne : Ideal.span {((p : ℕ) : 𝓞 K)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 : IsUnit (algebraMap ℤ (𝓞 K) (p : ℤ)) := by simpa using hu
    have h2 : IsUnit (p : ℤ) := isUnit_of_map_unit _ _ h1
    exact (Nat.prime_iff_prime_int.1 hp).not_isUnit h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : ((p : ℕ) : 𝓞 K) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hmem))

private theorem exists_residue_read {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {p : ℕ} (hp : p.Prime)
    (hw : Ideal.absNorm w.asIdeal = p) (ω : (ZMod p)ˣ →* ℂˣ) :
    ∃ θ : (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ, (∀ (a : ℕ) (ha : a.Coprime p) (b : (𝓞 L ⧸ w.asIdeal)ˣ),
        (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 L) → θ b = ω (ZMod.unitOfCoprime a ha)) ∧
      ∀ n : ℕ, θ ^ n = 1 ↔ ω ^ n = 1 := by
  have hc : Nat.card (𝓞 L ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 L ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  let _ : Fintype (𝓞 L ⧸ w.asIdeal) := Fintype.ofFinite _
  let ρ : ZMod p ≃+* (𝓞 L ⧸ w.asIdeal) := ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, hc])
  refine ⟨ω.comp (Units.map (ρ.symm : (𝓞 L ⧸ w.asIdeal) →* ZMod p)), fun a ha b hb => ?_, fun n => ?_⟩
  · rw [MonoidHom.comp_apply]
    congr 1
    ext
    simp [hb]
  · constructor
    · intro h
      ext u
      have := congrArg (fun f => f (Units.map (ρ : ZMod p →* (𝓞 L ⧸ w.asIdeal)) u)) h
      simp only [MonoidHom.pow_apply, MonoidHom.comp_apply, MonoidHom.one_apply] at this
      have e : Units.map (ρ.symm : (𝓞 L ⧸ w.asIdeal) →* ZMod p) (Units.map (ρ : ZMod p →* (𝓞 L ⧸ w.asIdeal)) u) = u := by
        ext; simp
      rw [e] at this
      simp [MonoidHom.pow_apply, this]
    · intro h
      refine MonoidHom.ext fun u => ?_
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, h, MonoidHom.one_apply,
        MonoidHom.one_apply]

open Classical in

theorem delta_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime → p % 15 = 1 → SplitsC H.E p → DeltaExists (H := H) p := by
  intro R H p hp h15 hs
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hce : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
  have hsp := GlobalTheory.Mem.Chr.splitsC_main R H p hp hs
  obtain ⟨Q, hQ⟩ := exists_place_over H.K hp
  have : Fact p.Prime := ⟨hp⟩
  have := H.galois
  have : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  obtain ⟨ω, hω⟩ := exists_char_of_dvd (G := (ZMod p)ˣ) (m := 15) (by norm_num)
    (by rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]; omega)
  have hθ : ∀ w : HeightOneSpectrum (𝓞 H.E), ∃ θ : (𝓞 H.E ⧸ w.asIdeal)ˣ →* ℂˣ,
      (OverP H p w → ∀ (a : ℕ) (ha : a.Coprime p) (b : (𝓞 H.E ⧸ w.asIdeal)ˣ),
        (b : 𝓞 H.E ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 H.E) → θ b = ω (ZMod.unitOfCoprime a ha)) ∧
      (OverP H p w → ∀ n : ℕ, θ ^ n = 1 ↔ 15 ∣ n) := by
    intro w
    by_cases h : OverP H p w
    · obtain ⟨θ, h1, h2⟩ := exists_residue_read w hp (hsp w h).1 ω
      exact ⟨θ, fun _ => h1, fun _ n => (h2 n).trans (hω n)⟩
    · exact ⟨1, fun h' => absurd h' h, fun h' => absurd h' h⟩
  choose θ hθ1 hθ2 using hθ
  let S : Finset (HeightOneSpectrum (𝓞 H.E)) := aboveF (L := H.E) H.K Q
  have hS : ∀ w, w ∈ S ↔ w.under (𝓞 H.K) = Q := fun w => by
    simp only [S, aboveF, Set.Finite.mem_toFinset]
    rfl
  have hov : ∀ w ∈ S, OverP H p w := fun w hw => by
    have h1 := hQ
    rw [← (hS w).1 hw] at h1
    have h2 : algebraMap (𝓞 H.K) (𝓞 H.E) ((p : ℕ) : 𝓞 H.K) ∈ w.asIdeal := h1
    rwa [map_natCast] at h2
  have hres := UpperTheory.prod_residue_char_norm_one_unit_eq_one H.K H.E p hp Q S hS (fun w hw => ⟨(hsp w (hov w hw)).1, (hsp w (hov w hw)).2.1⟩) ω θ
    (by
      intro w hw a ha
      have hu : IsUnit (Ideal.Quotient.mk w.asIdeal (a : 𝓞 H.E)) := by
        obtain ⟨s, t, hst⟩ : IsCoprime ((a : ℕ) : 𝓞 H.E) ((p : ℕ) : 𝓞 H.E) := Nat.Coprime.cast ha
        have h0 : Ideal.Quotient.mk w.asIdeal ((p : ℕ) : 𝓞 H.E) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hov w hw)
        have h1 := congrArg (Ideal.Quotient.mk w.asIdeal) hst
        rw [map_add, map_mul, map_mul, h0, mul_zero, add_zero, map_one] at h1
        exact IsUnit.of_mul_eq_one_right _ h1
      exact ⟨hu.unit, hu.unit_spec, hθ1 w (hov w hw) a ha _ hu.unit_spec⟩)
  obtain ⟨χ, -, ht, hi, htame, hunr, -, hord⟩ :=
    GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn H.F H.E c (R.Psi) (embPsi H) hcm (fun _ => 0) S θ
    (by
      intro w hw w' hcj hw'
      rw [hce] at hcj
      exact ((hsp w (hov w hw)).2.2.2 Q hQ w' hcj).2.1 ((hS w).1 hw) ((hS w').1 hw'))
    (by
      intro ζ hζ
      have h1 := hres ζ (H.der.norm_mu _ hζ)
      have h2 : ∏ w ∈ S, ((θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) : ℂˣ) : ℂ) = 1 := by
        rw [← Units.coe_prod]
        exact congrArg Units.val h1 |>.trans Units.val_one
      rw [h2]
      simp)
  refine ⟨χ, GlobalTheory.T.heckeChar_finiteOrder_of_trivial_at_infinity H.E χ fun k => ?_, ht, htame, fun v hv => hunr v (fun h => hv (hov v h)) ?_,
    fun v hv n => ?_⟩
  · apply Units.ext
    rw [hi k]
    simp
  · intro w hw hcj
    rw [hce] at hcj
    exact hv ((hsp w (hov w hw)).2.2.2 Q hQ v hcj).1
  · by_cases h : v ∈ S
    · exact (hord v h n).1.trans (hθ2 v hv n)
    · obtain ⟨w, hw, -⟩ := existsUnique_conjPl c.toRingEquiv.symm v
      have hcj : ConjPl c.toRingEquiv w v := fun x => by
        have := hw (c.toRingEquiv x)
        rw [RingEquiv.symm_apply_apply] at this
        exact this.symm
      have hwo : OverP H p w := by
        refine ((conjPl_iff_mem _ w v).1 hcj _ _ ?_).2 hv
        simp
      have hwS : w ∈ S := (hS w).2
        (((hsp w hwo).2.2.2 Q hQ v (hce ▸ hcj)).2.2 fun e => h ((hS v).2 e))
      exact ((hord w hwS n).2 v hcj).trans (hθ2 w hwo n)

end GlobalTheory.Mem.DeltaZero

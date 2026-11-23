import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EvLawsGenFrNonemptyComp
import Formalism.LocalToGlobal.ProjectiveLattices.LocFld
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrReadingInCpOfFiniteResidueStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoTie.NumPt

section Val

variable {V : Type} {K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
  [Algebra V K] [IsFractionRing V K]

lemma vV_nonneg_of_mem (b : V) : 0 ≤ vV V (algebraMap V K b) := by
  by_cases hb : b = 0
  · subst hb; simp [vV]
  have h1 : valV V (algebraMap V K b) ≤ 1 := by
    simpa [valV] using (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one (K := K) b
  have h0 : valV V (algebraMap V K b) ≠ 0 := valV_ne_zero (by simpa using hb)
  have := (WithZero.log_le_log h0 one_ne_zero).2 h1
  simp only [vV]
  simp at this
  omega

lemma vV_one : vV V (1 : K) = 0 := by simp [vV]

lemma vV_inv {x : K} (hx : x ≠ 0) : vV V x⁻¹ = - vV V x := by
  have := vV_mul (V := V) hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, vV_one] at this
  omega

lemma vV_eq_zero_of_mul {x y : K} (hx : x ∈ Set.range (algebraMap V K)) (hy : y ∈ Set.range (algebraMap V K))
    (h : x * y = 1) : vV V x = 0 := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have ha : algebraMap V K a ≠ 0 := left_ne_zero_of_mul_eq_one h
  have hb : algebraMap V K b ≠ 0 := right_ne_zero_of_mul_eq_one h
  have := vV_mul (V := V) ha hb
  rw [h, vV_one] at this
  have h1 := vV_nonneg_of_mem (K := K) a
  have h2 := vV_nonneg_of_mem (K := K) b
  omega

lemma vV_irreducible {ϖ : V} (hϖ : Irreducible ϖ) : vV V (algebraMap V K ϖ) = 1 := by
  have hne : ϖ ≠ 0 := hϖ.ne_zero
  simp only [vV, valV]
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_singleton _ hne ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)]
  simp

end Val

section Cmp

variable {V : Type} {K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
  [Algebra V K] [IsFractionRing V K]
  {V' : Type} {K' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K']
  [Algebra V' K'] [IsFractionRing V' K']

lemma exists_vV_map (ψ : K →+* K') (hψ : ∀ a : V, ψ (algebraMap V K a) ∈ Set.range (algebraMap V' K')) :
    ∃ r : ℕ, ∀ x, vV V' (ψ x) = (r : ℤ) * vV V x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨b, hb⟩ := hψ ϖ
  have hr0 : 0 ≤ vV V' (ψ (algebraMap V K ϖ)) := hb ▸ vV_nonneg_of_mem b
  refine ⟨(vV V' (ψ (algebraMap V K ϖ))).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hr0]
  have hint : ∀ a : V, a ≠ 0 → vV V' (ψ (algebraMap V K a)) = vV V' (ψ (algebraMap V K ϖ)) * vV V (algebraMap V K a) := by
    intro a ha
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    have hu0 : algebraMap V K (u : V) ≠ 0 := by
      simpa using u.ne_zero
    have hϖ0 : algebraMap V K ϖ ≠ 0 := by simpa using hϖ.ne_zero
    have huK : vV V (algebraMap V K (u : V)) = 0 :=
      vV_eq_zero_of_mul ⟨_, rfl⟩ ⟨((u⁻¹ : Vˣ) : V), rfl⟩ (by rw [← map_mul]; simp)
    have huK' : vV V' (ψ (algebraMap V K (u : V))) = 0 :=
      vV_eq_zero_of_mul (hψ _) (hψ ((u⁻¹ : Vˣ) : V)) (by rw [← map_mul, ← map_mul]; simp)
    have hpow : ∀ (F : Type) [Field F] (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
        [Algebra W F] [IsFractionRing W F] (y : F), y ≠ 0 → ∀ m : ℕ, vV W (y ^ m) = m * vV W y := by
      intro F _ W _ _ _ _ _ y hy m
      induction m with
      | zero => simp [vV]
      | succ m ih => rw [pow_succ, vV_mul (pow_ne_zero _ hy) hy, ih]; push_cast; ring
    rw [map_mul, map_pow, map_mul, map_pow, vV_mul hu0 (pow_ne_zero _ hϖ0),
      vV_mul ((map_ne_zero ψ).2 hu0) (pow_ne_zero _ ((map_ne_zero ψ).2 hϖ0)), huK, huK',
      hpow K V _ hϖ0, hpow K' V' _ ((map_ne_zero ψ).2 hϖ0), vV_irreducible hϖ]
    ring
  intro x
  by_cases hx : x = 0
  · subst hx; simp [vV]
  obtain ⟨a, b, hb0, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  have hb' : b ≠ 0 := nonZeroDivisors.ne_zero hb0
  have ha' : a ≠ 0 := by rintro rfl; simp at hx
  have haK : algebraMap V K a ≠ 0 := by simpa using ha'
  have hbK : algebraMap V K b ≠ 0 := by simpa using hb'
  rw [div_eq_mul_inv, map_mul, map_inv₀, vV_mul ((map_ne_zero ψ).2 haK) (inv_ne_zero ((map_ne_zero ψ).2 hbK)),
    vV_inv ((map_ne_zero ψ).2 hbK), vV_mul haK (inv_ne_zero hbK), vV_inv hbK, hint a ha', hint b hb']
  ring

end Cmp

section Main

open LocFldPf HeightOneSpectrum

theorem exists_ptC_of_finExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (φ : c.F →+* ℂ_[p]), IntAll Xo c →
    ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →+* ℂ_[p]),
      (∀ a, σ (algebraMap c.F L a) = φ a) → ∀ (y : FrPt Xo c L) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
      ∃ (z : PtC Xo c φ) (u : ℂ_[p]), u ≠ 0 ∧ ∀ f ∈ sec Xo c a n, valC z.1 f = u * σ (evR Xo c f y) := by
  intro E _ _ _ H Dw l Xo c p _ φ hIA L _ _ _ σ hσ y a n
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  haveI : NumberField L := NumberField.of_module_finite c.F L
  have hL : GlobalTheory.Reg.EvLaws Xo c := (GlobalTheory.Reg.evLaws_genFr_nonempty_comp E H Dw l Xo c).1

  let w : HeightOneSpectrum (𝓞 L) := placeAt σ
  haveI : Finite (𝓞 L ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  haveI : CharZero (adicCompletionIntegers L w) :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (𝓞 L) (adicCompletionIntegers L w))
  obtain ⟨e1, he1, h1⟩ := exists_e (L := L) w
  let T : CDVR := { V := adicCompletionIntegers L w, cpl := isAdicComplete w }
  let ι : L →+* T.Fr := kMap w
  have hOσ : OverLa (placeAt σ) T.V ι e1 := by
    refine ⟨he1, fun x => ?_⟩
    show vV (adicCompletionIntegers L w) (kMap w x) = _
    simp only [vV, vLa]
    rw [h1, WithZero.log_pow]
    push_cast
    ring
  have hFin : T.FinRes := finite_res w

  have hlies : w.asIdeal.LiesOver (placeAt φ).asIdeal := ⟨by
    ext b
    rw [Ideal.mem_comap, mem_placeAt, mem_placeAt]
    show _ ↔ ‖σ ((algebraMap (𝓞 c.F) (𝓞 L) b : 𝓞 L) : L)‖ < 1
    rw [show ((algebraMap (𝓞 c.F) (𝓞 L) b : 𝓞 L) : L) = algebraMap c.F L (b : c.F) from rfl, hσ]⟩
  let io : c.F →+* T.Fr := ι.comp (algebraMap c.F L)
  have he2 : (placeAt φ).asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (placeAt φ).ne_bot
  have hO : OverLa (placeAt φ) T.V io ((placeAt φ).asIdeal.ramificationIdx' w.asIdeal * e1) := by
    refine ⟨Nat.mul_pos (Nat.pos_of_ne_zero he2) he1, fun b => ?_⟩
    show vV (adicCompletionIntegers L w) (kMap w (algebraMap c.F L b)) = _
    simp only [vV, vLa]
    rw [h1, ← valuation_liesOver L (placeAt φ) w b, ← pow_mul, WithZero.log_pow]
    push_cast
    simp

  letI : Algebra c.F T.Fr := io.toAlgebra
  let ιA : L →ₐ[c.F] T.Fr := { ι with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := hL.bc L T.Fr ιA y

  obtain ⟨T', io', e', y', hO', hy'alg, φ', zz, t, hint, hmap, hbor⟩ := hIA (placeAt φ) T io _ hO hFin yT
  letI : Algebra c.F T'.Fr := io'.toAlgebra

  let ψ : T.Fr →+* T'.Fr := (φ' : T.Fr →+* T'.Fr)
  obtain ⟨r, hr⟩ := exists_vV_map (V := T.V) (V' := T'.V) ψ hint
  have hψio : ∀ b : c.F, ψ (io b) = io' b := fun b => φ'.commutes b
  have hp0 : vLa (placeAt φ) (p : c.F) ≠ 0 := by
    have hlt : (placeAt φ).valuation c.F (p : c.F) < 1 := by
      rw [show (p : c.F) = algebraMap (𝓞 c.F) c.F ((p : ℕ) : 𝓞 c.F) by simp,
        HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact natCast_mem_placeAt φ
    have hne : (placeAt φ).valuation c.F (p : c.F) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    intro h0
    have : WithZero.log ((placeAt φ).valuation c.F (p : c.F)) = 0 := by
      simp only [vLa] at h0; omega
    have h2 := WithZero.exp_log hne
    rw [this, WithZero.exp_zero] at h2
    exact hlt.ne h2.symm
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      have h3 := hO'.2 (p : c.F)
      rw [← hψio, hr, h0] at h3
      simp only [Nat.cast_zero, zero_mul] at h3
      have : (e' : ℤ) ≠ 0 := by exact_mod_cast hO'.1.ne'
      exact (mul_ne_zero this hp0) h3.symm
    · exact h0
  have hOσ' : OverLa (placeAt σ) T'.V (ψ.comp ι) (r * e1) := hOσ.bc ψ hrpos hr

  obtain ⟨k', hk'⟩ := GlobalTheory.T.exists_cdvrReadingInCp_of_finiteResidue p L σ T' (ψ.comp ι) (r * e1) hOσ' hy'alg
  have hk : IsReading φ T' io' k' := by
    refine ⟨fun b => ?_, hk'.int⟩
    rw [← hψio, ← hσ b]
    exact hk'.comp (algebraMap c.F L b)

  obtain ⟨z₀, hz₀⟩ := PtC.exists_of_reading hk y' hy'alg
  refine ⟨z₀, k' (wchar (ex Dw a n) t), ?_, fun f hf => ?_⟩
  · rw [map_ne_zero]
    simp [wchar, Finset.prod_ne_zero_iff]
  · rw [hz₀ a n f hf]
    obtain ⟨q, χ, y₀, hy₀⟩ := hL.test L y
    have e1' : evR Xo c f y = χ (f q y₀) := GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q χ y₀ y hy₀
    have e2 : evR Xo c f zz = (φ'.comp (ιA.comp χ)) (f q y₀) :=
      GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q _ y₀ zz
        (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ φ' (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans χ ιA hy₀ hyT) hmap)
    have e3 : evI y' f = wchar (ex Dw a n) t * evR Xo c f zz :=
      hL.wt a n f hf T'.Fr t zz y'.1 (hL.test _ _) (hL.test _ _) hbor
    rw [e3, map_mul, e2, e1']
    congr 1
    exact hk'.comp (χ (f q y₀))

end Main

end GlobalTheory.GeoTie.NumPt

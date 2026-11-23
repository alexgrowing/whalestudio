import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi
import ReciprocityTheory.GaloisValuations.ArithOfA
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicCharacterFrobV
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical Pointwise

namespace UpperTheory.V.Z.Kato.Nb

private theorem normV_eq_natGenerator (v : Pl) : normV v = Rat.HeightOneSpectrum.natGenerator v := by
  show Nat.card (𝓞 ℚ ⧸ v.asIdeal) = _
  rw [Nat.card_congr (Ideal.quotientEquiv v.asIdeal _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))
    (Rat.HeightOneSpectrum.span_natGenerator v)).toEquiv,
    Nat.card_congr (Int.quotientSpanNatEquivZMod _).toEquiv, Nat.card_zmod]

theorem mem_place_iff (v : Pl) (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ normV v ∣ n := by
  rw [normV_eq_natGenerator, Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem normV_prime (v : Pl) : (normV v).Prime := by
  rw [normV_eq_natGenerator]
  exact Rat.HeightOneSpectrum.prime_natGenerator v

private theorem normV_injective' : Function.Injective (fun w : Pl => normV w) := by
  intro a b h
  apply Rat.HeightOneSpectrum.primesEquiv.injective
  apply Subtype.ext
  change Rat.HeightOneSpectrum.natGenerator a = Rat.HeightOneSpectrum.natGenerator b
  rw [← normV_eq_natGenerator, ← normV_eq_natGenerator]
  exact h

theorem finite_dvd {n : ℕ} (hn : n ≠ 0) : {w : Pl | normV w ∣ n}.Finite := by
  refine ((Nat.divisors n).finite_toSet.preimage normV_injective'.injOn).subset ?_
  intro w hw
  simp only [Set.mem_preimage, Finset.mem_coe, Nat.mem_divisors]
  exact ⟨hw, hn⟩

theorem finite_normV (T : Finset ℕ) : {w : Pl | normV w ∈ T}.Finite := by
  exact T.finite_toSet.preimage normV_injective'.injOn

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem exists_frobAt (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (w : Pl) :
    ∃ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w ∧ IsFrob B (normV w) σ := by
  obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := exists_isFrob hB
  exact ⟨B, σ, hB, hσ⟩

theorem eps_frobAt (l : ℕ) [Fact l.Prime] {w : Pl} (hl : ¬ normV w ∣ l) {B : ValuationSubring Ω} {σ : G ℚ Ω}
    (hB : IsPlaceOver B w) (hσ : IsFrob B (normV w) σ) : eps l σ = (normV w : Qbar l) := by
  have e : eps l σ = algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) := rfl
  rw [e, cycZ_of_isFrob (fun h => hl ((mem_place_iff w l).1 h)) hB hσ]
  simp

omit [IsAlgClosure ℚ Ω] in
theorem frob_root {w : Pl} {M : ℕ} (hM0 : M ≠ 0) (hM : Nat.Coprime M (normV w)) {B : ValuationSubring Ω} {σ : G ℚ Ω}
    (hB : IsPlaceOver B w) (hσ : IsFrob B (normV w) σ) {ζ : Ω} (hζ : ζ ^ M = 1) : σ ζ = ζ ^ normV w := by
  have hq : ((normV w : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := (mem_place_iff w _).mpr dvd_rfl
  have hs : σ • B = B := hσ.1
  have hs' : σ⁻¹ • B = B := by
    conv_lhs => rw [← hs]
    rw [inv_smul_smul]
  have hF : GlobalTheory.KZ.ES.FrobV B (normV w) σ := by
    refine ⟨?_, fun x hx => ⟨?_, ?_, ?_⟩⟩
    · rw [ValuationSubring.mem_nonunits_iff]
      have := (hB (normV w : 𝓞 ℚ)).mpr hq
      simpa using this
    · have := ValuationSubring.smul_mem_pointwise_smul σ x B hx
      rw [hs] at this
      exact this
    · have := ValuationSubring.smul_mem_pointwise_smul σ⁻¹ x B hx
      rw [hs'] at this
      exact this
    · exact hσ.2 x ((B.valuation_le_one_iff x).mpr hx)
  exact hF.apply_rootOfUnity hM0 hM hζ

theorem cls_frobAt {w : Pl} (M : ℕ) [NeZero M] (hM : Nat.Coprime M (normV w)) {B : ValuationSubring Ω} {σ : G ℚ Ω}
    (hB : IsPlaceOver B w) (hσ : IsFrob B (normV w) σ) :
    ((Chr.cls ℚ Ω M σ : (ZMod M)ˣ) : ZMod M) = normV w := by
  have hc : Nat.Coprime (normV w) M := hM.symm
  have key := (Chr.clsFacts ℚ Ω M).2.2.1 σ (ZMod.unitOfCoprime (normV w) hc) (fun ζ hζ => by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, frob_root (NeZero.ne M) hM hB hσ hζ]
    conv_lhs => rw [← Nat.div_add_mod (normV w) M, pow_add, pow_mul, hζ, one_pow, one_mul])
  rw [key, ZMod.coe_unitOfCoprime]

private theorem isFrob_smul_conj {q : ℕ} {B : ValuationSubring Ω} {σ : G ℚ Ω} (hσ : IsFrob B q σ)
    (g : G ℚ Ω) : IsFrob (g • B) q (g * σ * g⁻¹) := by
  have hs : σ • B = B := hσ.1
  refine ⟨?_, fun x hx => ?_⟩
  · show (g * σ * g⁻¹) • (g • B) = g • B
    rw [mul_smul, mul_smul, inv_smul_smul, hs]
  · rw [smul_valuation_lt_one_iff]
    rw [smul_valuation_le_one_iff] at hx
    have := hσ.2 _ hx
    simpa [AlgEquiv.mul_apply, AlgEquiv.aut_inv, map_sub, map_pow] using this

theorem frob_conj_ine {w : Pl} {B B' : ValuationSubring Ω} {σ σ' : G ℚ Ω} (hB : IsPlaceOver B w) (hσ : IsFrob B (normV w) σ)
    (hB' : IsPlaceOver B' w) (hσ' : IsFrob B' (normV w) σ') :
    ∃ g : G ℚ Ω, ∃ a ∈ Ine (F := ℚ) B', σ' = g * σ * g⁻¹ * a := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver hB hB'
  have hF := isFrob_smul_conj hσ g
  rw [hg] at hF
  exact ⟨g, (g * σ * g⁻¹)⁻¹ * σ', inv_mul_mem_Ine_of_isFrob hF hσ', (mul_inv_cancel_left _ _).symm⟩

theorem frobInv {l : ℕ} [Fact l.Prime] {e : ℕ} {S : Finset Pl} {A : ValuationSubring Ω} {W : R2 Ω l} (h : Nf e S A W) {w : Pl}
    (hw : w ∉ S) {B B' : ValuationSubring Ω} {σ σ' : G ℚ Ω} (hB : IsPlaceOver B w) (hσ : IsFrob B (normV w) σ)
    (hB' : IsPlaceOver B' w) (hσ' : IsFrob B' (normV w) σ') :
    (mat W σ).trace = (mat W σ').trace ∧ (mat W σ).det = (mat W σ').det := by
  obtain ⟨g, a, ha, rfl⟩ := frob_conj_ine hB hσ hB' hσ'
  have hWa : W a = 1 := h.unr w hw B' hB' ha
  unfold GlobalTheory.Ord2.mat
  rw [map_mul, hWa, mul_one, map_mul, map_mul, map_inv]
  constructor
  · rw [Units.val_mul, Units.val_mul, Matrix.trace_units_conj]
  · rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj]

end UpperTheory.V.Z.Kato.Nb

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsValuedHeckeCharRamified

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (betaBound_vp c_vp cE_vp a0 n_vp)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt upIdele IsInvIdealOf IsLatOf)
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.LatVal.Model

variable {K : Type} [Field K] [NumberField K]

def princId (α : Kˣ) : (Af K)ˣ := Units.map (algebraMap K (Af K)).toMonoidHom α

theorem int_iff (x : K) : (∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((algebraMap K (Af K) x) v) ≤ 1) ↔
    x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  have e : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((algebraMap K (Af K) x) v) = v.valuation K x := fun v =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  simp only [e, FractionalIdeal.mem_one_iff]
  constructor
  · intro h
    exact HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K x h
  · rintro ⟨r, rfl⟩ v
    exact v.valuation_le_one r

theorem exists_isLatOf (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) :
    ∃ Λ : PeriodPair, IsLatOf ι 1 Λ := by
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = Fintype.card (Fin 2) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, h2]; simp
  let e := Fintype.equivOfCardEq hc
  let b := (RingOfIntegers.basis K).reindex e
  let B := (integralBasis K).reindex e
  have hB : ∀ i, B i = algebraMap (𝓞 K) K (b i) := fun i => by simp [B, b]
  have hrep : ∀ x : K, ∃ p q : ℚ, ι x = p * ι (B 0) + q * ι (B 1) := fun x => by
    refine ⟨B.repr x 0, B.repr x 1, ?_⟩
    conv_lhs => rw [← B.sum_repr x]
    simp [Fin.sum_univ_two, Rat.smul_def]
  have hδ' : ι δ ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
  have hind : LinearIndependent ℝ ![ι (B 0), ι (B 1)] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    simp only [Complex.real_smul] at h
    obtain ⟨p, q, h1⟩ := hrep 1
    obtain ⟨p', q', h3⟩ := hrep δ
    rw [map_one] at h1
    have key : ∀ u w : ℝ, (u : ℂ) * ι δ = w → u = 0 := fun u w huw => by
      have : ((u : ℂ) * ι δ) ^ 2 = (w : ℂ) ^ 2 := by rw [huw]
      rw [mul_pow, hδ'] at this
      have h' : u ^ 2 * (-(d : ℝ)) = w ^ 2 := by exact_mod_cast this
      have hd' : (0 : ℝ) < d := by exact_mod_cast hd
      have : u ^ 2 ≤ 0 := by nlinarith [sq_nonneg w, sq_nonneg u]
      exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm this (sq_nonneg u))
    have k1 := key (s * q - t * p) (s * q' - t * p') (by
      push_cast
      have : ((s : ℂ) * q' - t * p') = ((s : ℂ) * q' - t * p') * 1 := by ring
      rw [this, h1, h3]
      linear_combination (q * p' - p * q' : ℂ) * h)
    have k1' : (s : ℂ) * q - t * p = 0 := by exact_mod_cast k1
    have hb0 : ι (B 0) ≠ 0 := by simpa using B.ne_zero 0
    have hb1 : ι (B 1) ≠ 0 := by simpa using B.ne_zero 1
    have hs : (s : ℂ) = 0 := by linear_combination (s : ℂ) * h1 + (p : ℂ) * h + ι (B 1) * k1'
    have ht : (t : ℂ) = 0 := by linear_combination (t : ℂ) * h1 + (q : ℂ) * h - ι (B 0) * k1'
    exact ⟨by exact_mod_cast hs, by exact_mod_cast ht⟩
  refine ⟨⟨ι (B 0), ι (B 1), hind⟩, ?_⟩
  ext z
  simp only [SetLike.mem_coe, PeriodPair.mem_lattice, Set.mem_image, FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, ⟨m * b 0 + n * b 1, rfl⟩, by simp [hB]⟩
  · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
    refine ⟨b.repr r 0, b.repr r 1, ?_⟩
    conv_rhs => rw [← b.sum_repr r]
    simp [Fin.sum_univ_two, hB]

theorem torsTransport_princ (ι : K →+* ℂ) (α : Kˣ) (Λ₀ : PeriodPair) (Ω₀ : ℂ) (hΩ : Ω₀ ≠ 0) (hΛ : IsLatOf ι 1 Λ₀) :
    ∃ Λ₁, TorsTransport ι (RingEquiv.refl ℂ) (princId α) Λ₀ Λ₁ Ω₀ (ι α * Ω₀) := by
  have ha : ι α ≠ 0 := by simp
  have hc : (ι α)⁻¹ ≠ 0 := inv_ne_zero ha
  have H := isHomothetic_scalePeriods Λ₀ _ hc
  have hmem : ∀ z, z ∈ Λ₀.lattice ↔ ∃ x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K), ι x = z := fun z => by
    have := Set.ext_iff.1 hΛ z
    simpa using this
  have hid : ∀ x : K, ((princId α : (Af K)ˣ) : Af K) * algebraMap K (Af K) x = algebraMap K (Af K) (α * x) := fun x => by
    rw [map_mul]; rfl
  refine ⟨scalePeriods Λ₀ _ hc, hΩ, mul_ne_zero ha hΩ, fun _ => rfl, hΛ,
    ⟨FractionalIdeal.spanSingleton _ (α : K)⁻¹, fun x => ?_, ?_⟩, ?_, ?_, fun x x' hx hv => ?_⟩
  · rw [hid, int_iff, FractionalIdeal.mem_spanSingleton, FractionalIdeal.mem_one_iff]
    refine exists_congr fun r => ?_
    rw [Algebra.smul_def]
    constructor
    · rintro rfl; field_simp
    · intro h; rw [h]; field_simp
  · ext z
    have := H (ι α * z)
    rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul] at this
    simp only [SetLike.mem_coe, Set.mem_image, FractionalIdeal.mem_coe, this, hmem, FractionalIdeal.mem_spanSingleton,
      FractionalIdeal.mem_one_iff]
    constructor
    · rintro ⟨_, ⟨r, rfl⟩, h⟩
      refine ⟨_, ⟨r, rfl⟩, ?_⟩
      rw [Algebra.smul_def, map_mul, h, map_inv₀]; field_simp
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      refine ⟨_, ⟨r, rfl⟩, ?_⟩
      rw [Algebra.smul_def, map_mul, map_inv₀]; field_simp
  · simp only [RingEquiv.refl_apply, PeriodPair.g₂, H.G_eq]; field_simp
  · simp only [RingEquiv.refl_apply, PeriodPair.g₃, H.G_eq]; field_simp
  · rw [hid, ← map_sub, int_iff] at hv
    have hl : ι (α * x' - x) ∈ Λ₀.lattice := (hmem _).2 ⟨_, hv, rfl⟩
    have e : ι x' = (ι α)⁻¹ * (ι x + ((⟨_, hl⟩ : Λ₀.lattice) : ℂ)) := by
      simp only [map_sub, map_mul]; field_simp; ring
    rw [e, H.weierstrassP_mul, H.derivWeierstrassP_mul, Λ₀.weierstrassP_add_coe, Λ₀.derivWeierstrassP_add_coe]
    simp only [RingEquiv.refl_apply]
    constructor <;> field_simp

theorem conj_scalars (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ) (a a' Ω S : ℂ)
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hΩ : Ω ≠ 0) :
    coordIn E d s κ Ω S = coordIn E d s κ (a * Ω)
      ((((a * a')⁻¹) ^ (∑ i, κ i))⁻¹ * (a ^ (2 * s * Fintype.card I + ∑ i, κ i) * a'⁻¹ ^ (∑ i, κ i) * S)) := by
  simp only [coordIn]
  generalize ∑ i, κ i = n
  generalize 2 * s * Fintype.card I = m
  simp only [inv_pow, inv_inv, mul_pow]
  field_simp
  ring

theorem exponents_add {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d s l : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E))
    (z : ClassGroup (OF E) → ℚ) (hc : c_vp 𝔣 l ≠ 0) :
    betaBound_vp d s κ 𝔣 z l = 12 * (((cE_vp l z : ℝ) + ((2 * s * Fintype.card I : ℕ) : ℝ) * c_vp 𝔣 l +
          ((∑ i, κ i : ℕ) : ℝ) * (c_vp 𝔣 l + 1 + if l = 2 then 1 else 0)) +
      ((∑ i, κ i : ℕ) : ℝ) * (c_vp 𝔣 l + if l = d then 1 / 2 else 0) +
      ((2 * s * Fintype.card I + 2 * ∑ i, κ i : ℕ) : ℝ) * (a0 𝔣 l : ℝ)) := by
  simp only [betaBound_vp, n_vp, if_neg hc, Formalism.PairingDivisionLocalBalance.nl, Formalism.PairingDivisionLocalBalance.absK, Formalism.PairingDivisionLocalBalance.wtM]
  ring

theorem sz_inv (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (r : ℝ) :
    Sz l lam r ((l : ℂ)⁻¹) ↔ 1 ≤ r := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hm : ((l : ℂ)⁻¹) ∈ algebraicClosure ℚ ℂ := inv_mem (natCast_mem _ l)
  have e : (⟨(l : ℂ)⁻¹, hm⟩ : algebraicClosure ℚ ℂ) = (l : algebraicClosure ℚ ℂ)⁻¹ := by ext; simp
  have n : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]), norm_algebraMap']
    simp
  constructor
  · rintro ⟨h, hh⟩
    rw [e, map_inv₀, map_natCast, norm_inv, n, inv_inv] at hh
    nth_rw 1 [← Real.rpow_one l] at hh
    exact (Real.rpow_le_rpow_left_iff hl).1 hh
  · intro h
    refine ⟨hm, ?_⟩
    rw [e, map_inv₀, map_natCast, norm_inv, n, inv_inv]
    nth_rw 1 [← Real.rpow_one l]
    exact (Real.rpow_le_rpow_left_iff hl).2 h

theorem oneOver_one (l : ℕ) : OneOver (E := K) l 1 := fun _ _ => rfl

theorem isCMType_ext {E : Type} [Field E] [NumberField E] [Algebra K E] (d : ℕ) (δ : K) (ι : K →+* ℂ)
    (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) :
    IsCMType (fun i : {ψ : E →+* ℂ // ψ.comp (algebraMap K E) = ι} => i.1) := by
  classical
  have hδ' : ι δ ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
  have hne : ComplexEmbedding.conjugate ι ≠ ι := fun h => by
    have h1 : starRingEnd ℂ (ι δ) = ι δ := DFunLike.congr_fun h δ
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h1
    rw [hr] at hδ'
    have : r ^ 2 = -(d : ℝ) := by exact_mod_cast hδ'
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg r]
  have hall : ∀ τ : K →+* ℂ, τ = ι ∨ τ = ComplexEmbedding.conjugate ι := fun τ => by
    have hc : ({ι, ComplexEmbedding.conjugate ι} : Finset (K →+* ℂ)) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [Finset.card_pair hne.symm, Embeddings.card, h2])
    simpa using (hc ▸ Finset.mem_univ τ : τ ∈ ({ι, ComplexEmbedding.conjugate ι} : Finset (K →+* ℂ)))
  have hcc : ∀ ψ : E →+* ℂ, (ComplexEmbedding.conjugate ψ).comp (algebraMap K E) =
      ComplexEmbedding.conjugate (ψ.comp (algebraMap K E)) := fun _ => rfl
  have hinv : ∀ {F : Type} [Field F] (ψ : F →+* ℂ), ComplexEmbedding.conjugate (ComplexEmbedding.conjugate ψ) = ψ :=
    fun ψ => by ext; simp
  intro σ
  rcases hall (σ.comp (algebraMap K E)) with h | h
  · refine ⟨⟨σ, h⟩, Or.inl rfl, ?_⟩
    rintro ⟨ψ, hψ⟩ (e | e)
    · exact Subtype.ext e.symm
    · exact absurd (by rw [← h, e, hcc, hψ, hinv]; rw [e, hcc, hψ] at h; exact h.symm) hne
  · refine ⟨⟨ComplexEmbedding.conjugate σ, by rw [hcc, h, hinv]⟩, Or.inr (hinv σ).symm, ?_⟩
    rintro ⟨ψ, hψ⟩ (e | e)
    · exact absurd (by rw [← h, e]; exact hψ) hne
    · exact Subtype.ext (show ψ = ComplexEmbedding.conjugate σ from (hinv ψ).symm.trans (congrArg _ e.symm))

theorem latDatum_inhabited : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (d : ℕ) (δ : K) (ι : K →+* ℂ),
    Module.finrank ℚ K = 2 ∧ 0 < d ∧ δ ^ 2 = -(d : K) ∧
    ∃ (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ ∧ Ω₁ ≠ Ω₀ ∧
      TorsTransport ι (RingEquiv.refl ℂ) t Λ₀ Λ₁ Ω₀ Ω₁ ∧
      ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (_ : Algebra K E) (I : Type) (_ : Fintype I)
        (φ : I → E →+* ℂ) (𝔣 : Ideal (OF E)), ∀ s, 1 ≤ s → IsLatDatum ι φ s 𝔣 ∅ := by
  classical
  let E := GlobalTheory.CMVal.Model.K
  have hz : IsPrimitiveRoot (IsCyclotomicExtension.zeta 21 ℚ E ^ 7) 3 :=
    (IsCyclotomicExtension.zeta_spec 21 ℚ E).pow (by norm_num) (by norm_num : 21 = 7 * 3)
  set w := IsCyclotomicExtension.zeta 21 ℚ E ^ 7
  have hcyc : IsCyclotomicExtension {3} ℚ (IntermediateField.adjoin ℚ {w}) :=
    hz.intermediateField_adjoin_isCyclotomicExtension ℚ
  let K' := IntermediateField.adjoin ℚ {w}
  have h2 : Module.finrank ℚ K' = 2 := by
    rw [IsCyclotomicExtension.finrank (n := 3) K' (Polynomial.cyclotomic.irreducible_rat (by norm_num))]; decide
  let w' : K' := ⟨w, IntermediateField.mem_adjoin_simple_self ℚ w⟩
  have hw : w ^ 2 + w + 1 = 0 := by
    have := hz.geom_sum_eq_zero (by norm_num)
    simp [Finset.sum_range_succ] at this
    linear_combination this
  have hδ : (2 * w' + 1) ^ 2 = -((3 : ℕ) : K') := by
    apply Subtype.ext
    show (2 * w + 1) ^ 2 = -((3 : ℕ) : E)
    push_cast
    linear_combination 4 * hw
  obtain ⟨ι⟩ : Nonempty (K' →+* ℂ) := inferInstance
  obtain ⟨Λ₀, hΛ⟩ := exists_isLatOf 3 _ ι h2 (by norm_num) hδ
  obtain ⟨Ω₀, hΩ⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc Λ₀) (n := 12) (by norm_num)
  have h0 : Ω₀ ≠ 0 := by
    rintro rfl
    exact latDisc_ne_zero Λ₀ (by rw [← hΩ]; simp)
  obtain ⟨Λ₁, hT⟩ := torsTransport_princ ι (Units.mk0 (2 : K') two_ne_zero) Λ₀ Ω₀ h0 hΛ
  obtain ⟨hU, -, v, -, hv, -⟩ := GlobalTheory.CMVal.Model.inhabited_K
  refine ⟨K', inferInstance, inferInstance, 3, _, ι, h2, by norm_num, hδ, _, Λ₀, Λ₁, Ω₀, _, hΩ, fun e => h0 ?_, hT,
    E, inferInstance, inferInstance, inferInstance, inferInstance, _, inferInstance, _, v.asIdeal, fun s hs =>
      ⟨hU, isCMType_ext 3 _ ι h2 (by norm_num) hδ, fun i => i.2, hs, hv, fun q hq => by simp at hq⟩⟩
  simp only [Units.val_mk0, map_ofNat] at e
  linear_combination e

end GlobalTheory.LatVal.Model

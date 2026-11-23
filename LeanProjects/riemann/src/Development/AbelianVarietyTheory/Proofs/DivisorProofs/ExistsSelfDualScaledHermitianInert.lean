import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKLeLocU
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfIsSkew
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgebraMapEqOfInertPlace

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

noncomputable section

namespace GlobalTheory.InertSkewRescale

open scoped nonZeroDivisors

theorem exists_notMem_mul_mem {R : Type} [CommRing R] [IsDedekindDomain R] {P : Ideal R} [P.IsPrime]
    {I J : Ideal R} {k : ℕ} (hJ : J ≤ P ^ k) (hJ' : ¬ J ≤ P ^ (k + 1)) (hI : I ≤ P ^ k) :
    ∃ c ∉ P, ∀ i ∈ I, c * i ∈ J := by
  obtain ⟨A, rfl⟩ := Ideal.dvd_iff_le.2 hJ
  have hA : ¬ A ≤ P := fun h => hJ' (by rw [pow_succ]; exact Ideal.mul_mono_right h)
  obtain ⟨c, hcA, hcP⟩ := Set.not_subset.1 hA
  exact ⟨c, hcP, fun i hi => by rw [mul_comm c i]; exact Ideal.mul_mem_mul (hI hi) hcA⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem traceDual_iff (e : E) :
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) ↔
      ∀ d ∈ differentIdeal ℤ (𝓞 E), (d : E) * e ∈ (algebraMap (𝓞 E) E).range := by
  have h1 : (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) ↔
      e ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
      rw [← FractionalIdeal.coeIdeal_top]; exact FractionalIdeal.coeIdeal_ne_zero.2 top_ne_bot
    rw [FractionalIdeal.mem_dual h10]
    constructor
    · rintro h a ⟨o, -, rfl⟩
      rw [Algebra.traceForm_apply, mul_comm]
      exact IsIntegrallyClosed.isIntegral_iff.1 (h o)
    · intro h o
      have := h _ ⟨o, Submodule.mem_top, rfl⟩
      rw [Algebra.traceForm_apply, mul_comm] at this
      exact IsIntegrallyClosed.isIntegral_iff.2 this
  have h2 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) =
      ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
    rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
  rw [h1, h2, FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot)]
  simp only [FractionalIdeal.mem_coeIdeal, FractionalIdeal.mem_one_iff, RingHom.mem_range]
  constructor
  · intro h d hd
    obtain ⟨b, hb⟩ := h _ ⟨d, hd, rfl⟩
    exact ⟨b, hb.trans (mul_comm _ _)⟩
  · rintro h _ ⟨d, hd, rfl⟩
    obtain ⟨b, hb⟩ := h d hd
    exact ⟨b, hb.trans (mul_comm _ _)⟩

theorem inclR_inv_mem_intLoc {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {c : E} (hc : w.valuation E c = 1) :
    inclR (Fv F v) c⁻¹ ∈ intLoc F E v := by
  rw [InertChart.mem_intLoc_iff hw h]
  change toCompl h ((1 : Fv F v) ⊗ₜ[F] c⁻¹) ∈ _
  rw [toCompl_tmul, map_one, one_mul]
  change _ ∈ w.adicCompletionIntegers E
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀]
  rw [show Valued.v ((algebraMap E (w.adicCompletion E)) c) = w.valuation E c from
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w c, hc, inv_one]

theorem latLoc_le_of_smul {n : ℕ} {L L' : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)} {c : E}
    (hc0 : c ≠ 0) (hc : inclR (Fv F v) c⁻¹ ∈ intLoc F E v) (hL : ∀ y ∈ L, c • y ∈ L') :
    latLoc F L v ≤ latLoc F L' v := by
  intro y hy
  refine latLoc_induction (p := (· ∈ latLoc F L' v)) (fun a ha x hx => ?_) (zero_mem _)
    (fun _ _ => add_mem) (fun _ => neg_mem) hy
  have := (latLoc F L' v).smul_mem ⟨_, hc⟩ (tmul_mem_latLoc ha (hL x hx))
  convert this using 1
  funext i
  change _ = inclR (Fv F v) c⁻¹ * (a ⊗ₜ[F] (c • x) i)
  simp [inclR, Algebra.TensorProduct.tmul_mul_tmul, hc0]

end GlobalTheory.InertSkewRescale

namespace GlobalTheory.InertSkewRescale

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_exact_pow (w : HeightOneSpectrum (𝓞 E)) :
    ∃ k : ℕ, differentIdeal ℤ (𝓞 E) ≤ w.asIdeal ^ k ∧ ¬ differentIdeal ℤ (𝓞 E) ≤ w.asIdeal ^ (k + 1) := by
  classical
  obtain ⟨d0, hd0, hd0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E))
  have hex : ∃ j, ¬ differentIdeal ℤ (𝓞 E) ≤ w.asIdeal ^ j := by
    by_contra hall
    push_neg at hall
    apply hd0ne
    have : d0 ∈ ⨅ i, w.asIdeal ^ i := Submodule.mem_iInf _ |>.2 fun i => hall i hd0
    rwa [Ideal.iInf_pow_eq_bot_of_isDomain w.asIdeal w.isPrime.ne_top, Submodule.mem_bot] at this
  have h0 : Nat.find hex ≠ 0 := fun h => Nat.find_spec hex (by rw [h, pow_zero, Ideal.one_eq_top]; exact le_top)
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · exact not_not.1 (Nat.find_min hex (by omega))
  · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)]; exact Nat.find_spec hex

theorem hE_smul_map (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = -J i j)
    (δ : E) (x y : Fin n → E) : hE σ (δ • J.map σ) x y = -δ * form σ J y x := by
  simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  simp only [AlgHom.coe_toRingHom]
  ring

theorem form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    form σ J (c • y) x = c * form σ J y x := by
  unfold form; rw [smul_dotProduct, smul_eq_mul]

end GlobalTheory.InertSkewRescale

namespace GlobalTheory.InertSkewRescale

theorem exists_herm_selfDualAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (d r s : ℕ) (W : Spc F E d), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
    W.IsSkew σ B r s → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), w.under (𝓞 F) = v → Formalism.UG.IsInertAt F E v w →
    ∃ δ : E, δ ≠ 0 ∧ IsHermND σ (δ • W.J.map σ) ∧ IsSelfDualAt σ (δ • W.J.map σ) W.L v := by
  intro F E _ _ _ _ _ σ B d r s W hσ _ hW v w hwv hw

  obtain ⟨x0, hx0⟩ := InertChart.exists_conj_sub_unit hσ hw
  set δ0 : E := σ (x0 : E) - x0 with hδ0def
  have hδ0σ : σ δ0 = -δ0 := by rw [hδ0def, map_sub, InertChart.conj_conj hσ]; ring
  have hδ0int : δ0 ∈ (algebraMap (𝓞 E) E).range :=
    sub_mem (SelfDual.sig_mem_range σ ⟨x0, rfl⟩) ⟨x0, rfl⟩
  have hδ0v : w.valuation E δ0 = 1 := hx0

  obtain ⟨k, hk1, hk2⟩ := exists_exact_pow w
  obtain ⟨ϖ, hϖ⟩ := v.intValuation_exists_uniformizer
  set T : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) (ϖ ^ k) with hTdef
  have hTE : ((T : 𝓞 E) : E) = algebraMap F E ((ϖ ^ k : 𝓞 F) : F) := by
    exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E _).symm.trans (IsScalarTower.algebraMap_apply (𝓞 F) F E _)
  have hTval : w.intValuation T = WithZero.exp (-(k : ℤ)) := by
    have h1 := GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt F E v w hw ((ϖ ^ k : 𝓞 F) : F)
    rw [HeightOneSpectrum.valuation_of_algebraMap, map_pow, hϖ, ← WithZero.exp_nsmul, ← hTE,
      HeightOneSpectrum.valuation_of_algebraMap] at h1
    rw [h1]
    congr 1
    simp
  have hT1 : Ideal.span {T} ≤ w.asIdeal ^ k := by
    rw [Ideal.span_singleton_le_iff_mem, ← HeightOneSpectrum.intValuation_le_pow_iff_mem, hTval]
  have hT2 : ¬ Ideal.span {T} ≤ w.asIdeal ^ (k + 1) := by
    rw [Ideal.span_singleton_le_iff_mem, ← HeightOneSpectrum.intValuation_le_pow_iff_mem, hTval,
      WithZero.exp_le_exp]
    omega
  have hT0 : (T : E) ≠ 0 := by
    intro h0
    have : w.valuation E (T : E) = 0 := by rw [h0, map_zero]
    rw [HeightOneSpectrum.valuation_of_algebraMap, hTval] at this
    exact WithZero.exp_ne_zero this
  have hTσ : σ (T : E) = T := by rw [hTE]; exact σ.commutes _

  obtain ⟨c1, hc1w, hc1⟩ := exists_notMem_mul_mem hT1 hT2 hk1
  obtain ⟨c2, hc2w, hc2⟩ := exists_notMem_mul_mem hk1 hk2 hT1
  have hc1v : w.valuation E (c1 : E) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hc1w
  have hc2v : w.valuation E (c2 : E) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hc2w

  set δ : E := (T : E) * δ0 with hδdef
  have hδ0ne : δ0 ≠ 0 := fun h0 => by rw [h0, map_zero] at hδ0v; exact zero_ne_one hδ0v
  have hδne : δ ≠ 0 := mul_ne_zero hT0 hδ0ne
  have hδσ : σ δ = -δ := by rw [hδdef, map_mul, hTσ, hδ0σ]; ring
  have hJ := GlobalTheory.ThK.TorusCentre.det_ne_zero_of_isSkew hW
  have hH : (δ • W.J.map σ).det ≠ 0 := by
    rw [Matrix.det_smul]
    refine mul_ne_zero (pow_ne_zero _ hδne) ?_
    change ((σ : E →+* E).mapMatrix W.J).det ≠ 0
    rw [← RingHom.map_det]
    exact (map_ne_zero _).2 hJ
  refine ⟨δ, hδne, ⟨fun i j => ?_, hH⟩, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hδσ, InertChart.conj_conj hσ, hW.skew j i]
    ring
  rw [IsSelfDualAt, ← SelfDual.latLoc_dualGlob hH hW.lat v]
  have key := hE_smul_map σ W.J hW.skew δ
  apply le_antisymm
  ·
    refine latLoc_le_of_smul (c := (c2 : E)) (fun h0 => by rw [h0, map_zero] at hc2v; exact zero_ne_one hc2v)
      (inclR_inv_mem_intLoc hw hwv hc2v) fun y hy x hx => ?_
    rw [key, form_smul_left]
    obtain ⟨b, hb⟩ := (traceDual_iff _).1 ((hW.dual y).1 hy x hx) _ (hc2 T (Ideal.mem_span_singleton_self T))
    have e1 : -δ * ((c2 : E) * form σ W.J y x) = -(δ0 * (((c2 * T : 𝓞 E) : E) * form σ W.J y x)) := by
      push_cast; rw [hδdef]; ring
    rw [e1, ← hb]
    obtain ⟨a, ha⟩ := hδ0int
    exact ⟨-(a * b), by rw [map_neg, map_mul, ha]⟩
  · refine latLoc_le_of_smul (c := δ0 * (c1 : E)) (mul_ne_zero hδ0ne
      (fun h0 => by rw [h0, map_zero] at hc1v; exact zero_ne_one hc1v))
      (inclR_inv_mem_intLoc hw hwv (by rw [map_mul, hδ0v, hc1v, one_mul])) fun y hy => ?_
    rw [hW.dual]
    intro x hx
    refine (traceDual_iff _).2 fun e he => ?_
    rw [form_smul_left]
    obtain ⟨a, ha⟩ := (SelfDual.mem_dualGlob σ _).1 hy x hx
    rw [key] at ha
    obtain ⟨b', hb'⟩ := Ideal.mem_span_singleton'.1 (hc1 e he)
    have hb'E : (b' : E) * (T : E) = (c1 : E) * (e : E) := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hb'
    refine ⟨-(b' * a), ?_⟩
    have e2 : algebraMap (𝓞 E) E (-(b' * a)) = -((b' : E) * algebraMap (𝓞 E) E a) := by
      rw [map_neg, map_mul]
    rw [e2, ha, hδdef]
    linear_combination (δ0 * form σ W.J y x) * hb'E

end GlobalTheory.InertSkewRescale

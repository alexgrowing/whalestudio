import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValAtOfUnder

noncomputable section

open scoped TensorProduct NNReal nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.UnrTate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem count_spanSingleton_of_ne (w : HeightOneSpectrum (𝓞 E)) {a : E} (ha : a ≠ 0) :
    FractionalIdeal.count E w (FractionalIdeal.spanSingleton (𝓞 E)⁰ a) = -WithZero.log (w.valuation E a) := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at ha
  have hI : FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E n / algebraMap (𝓞 E) E d) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E d)⁻¹ * ↑(Ideal.span {n} : Ideal (𝓞 E)) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton, div_eq_mul_inv,
      mul_comm]
  rw [FractionalIdeal.count_well_defined E w ((FractionalIdeal.spanSingleton_ne_zero_iff).2 ha) hI, map_div₀,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg _ hn0, HeightOneSpectrum.intValuation_if_neg _ hd0, ← WithZero.exp_sub,
    WithZero.log_exp]
  ring

theorem le_one_of_count_nonneg {K : FractionalIdeal (𝓞 E)⁰ E} (hK : K ≠ 0)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), 0 ≤ FractionalIdeal.count E P K) : K ≤ 1 := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' E hK]
  refine finprod_induction (fun I => I ≤ 1) le_rfl (fun a b ha hb => ?_) (fun P => ?_)
  · calc a * b ≤ 1 * 1 := mul_le_mul' ha hb
      _ = 1 := one_mul 1
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h P)
    show (P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ FractionalIdeal.count E P K ≤ 1
    rw [hn, zpow_natCast]
    exact pow_le_one' FractionalIdeal.coeIdeal_le_one n

theorem exists_mul_mem_of_count {v : HeightOneSpectrum (𝓞 F)} {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0)
    {z : E} (hz : z ≠ 0)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
      FractionalIdeal.count E w 𝔞 ≤ -WithZero.log (w.valuation E z)) :
    ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ algebraMap F E (s : F) * z ∈ 𝔞 := by
  classical
  set M := FractionalIdeal.spanSingleton (𝓞 E)⁰ z * 𝔞⁻¹ with hMdef
  have hz0 : FractionalIdeal.spanSingleton (𝓞 E)⁰ z ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hz
  have hM0 : M ≠ 0 := mul_ne_zero hz0 (inv_ne_zero h𝔞)
  have hcM : ∀ P, FractionalIdeal.count E P M =
      -WithZero.log (P.valuation E z) - FractionalIdeal.count E P 𝔞 := by
    intro P
    rw [hMdef, FractionalIdeal.count_mul E P hz0 (inv_ne_zero h𝔞), FractionalIdeal.count_inv,
      count_spanSingleton_of_ne P hz]
    ring
  set e : HeightOneSpectrum (𝓞 E) → ℤ := fun P => max (-FractionalIdeal.count E P M) 0 with hedef
  have he : ∀ᶠ P in Filter.cofinite, e P = 0 :=
    (FractionalIdeal.finite_factors M).mono fun P hP => by simp [hedef, hP]
  set D : FractionalIdeal (𝓞 E)⁰ E :=
    ∏ᶠ P : HeightOneSpectrum (𝓞 E), (P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ e P with hDdef
  have hcD : ∀ P, FractionalIdeal.count E P D = e P := fun P => FractionalIdeal.count_finprod E P e he
  have hD0 : D ≠ 0 := by
    rw [hDdef]
    refine finprod_induction (fun I => I ≠ 0) one_ne_zero (fun a b ha hb => mul_ne_zero ha hb) (fun P => ?_)
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 P.ne_bot)
  have hD1 : D ≤ 1 := le_one_of_count_nonneg hD0 fun P => by rw [hcD]; exact le_max_right _ _
  have hDM : D * M ≤ 1 := le_one_of_count_nonneg (mul_ne_zero hD0 hM0) fun P => by
    rw [FractionalIdeal.count_mul E P hD0 hM0, hcD]
    have := le_max_left (-FractionalIdeal.count E P M) 0
    linarith
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hD1
  have hex : ¬ Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) I ≤ v.asIdeal := by
    intro hle
    obtain ⟨Q, hIQ, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal I hle
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      apply v.ne_bot
      rw [← hQv]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
    let w : HeightOneSpectrum (𝓞 E) := ⟨Q, hQ, hQ0⟩
    have hw : w.under (𝓞 F) = v := HeightOneSpectrum.ext ((Ideal.under_def _ _).trans hQv)
    have h1 : FractionalIdeal.count E w D = 0 := by
      rw [hcD, hedef]
      have := h w hw
      have h3 := hcM w
      simp only
      omega
    have h2 : FractionalIdeal.count E w (w.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ≤ FractionalIdeal.count E w D := by
      rw [← hI]
      exact FractionalIdeal.count_mono E w (by rw [hI]; exact hD0) ((FractionalIdeal.coeIdeal_le_coeIdeal E).2 hIQ)
    rw [FractionalIdeal.count_self, h1] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨s, hsI, hsv⟩ := Set.not_subset.1 hex
  refine ⟨s, hsv, ?_⟩
  have hsD : algebraMap F E (s : F) ∈ D := by
    rw [← hI]
    refine (FractionalIdeal.mem_coeIdeal _).2 ⟨algebraMap (𝓞 F) (𝓞 E) s, hsI, ?_⟩
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
  rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
  have hzM : FractionalIdeal.spanSingleton (𝓞 E)⁰ z = M * 𝔞 := by
    rw [hMdef, mul_assoc, inv_mul_cancel₀ h𝔞, mul_one]
  calc _ ≤ D * FractionalIdeal.spanSingleton (𝓞 E)⁰ z :=
        mul_le_mul' (FractionalIdeal.spanSingleton_le_iff_mem.2 hsD) le_rfl
    _ = D * M * 𝔞 := by rw [hzM]; exact (mul_assoc _ _ _).symm
    _ ≤ 1 * 𝔞 := mul_le_mul' hDM le_rfl
    _ = 𝔞 := one_mul _

theorem one_tmul_mem_locId {v : HeightOneSpectrum (𝓞 F)} {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0) (z : E)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
      w.valuation E z ≤ WithZero.exp (-FractionalIdeal.count E w 𝔞)) :
    (1 : Fv F v) ⊗ₜ[F] z ∈ GlobalTheory.SnMass.locId v 𝔞 := by
  by_cases hz : z = 0
  · rw [hz, TensorProduct.tmul_zero]; exact zero_mem _
  have hz' : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
      FractionalIdeal.count E w 𝔞 ≤ -WithZero.log (w.valuation E z) := by
    intro w hw
    have h0 : w.valuation E z ≠ 0 := by simpa using hz
    have := h w hw
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at this
    linarith
  obtain ⟨s, hsv, hs⟩ := exists_mul_mem_of_count h𝔞 hz hz'
  have hval : v.valuation F (s : F) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (v.intValuation_le_one s) (not_lt.1 fun h => hsv ((v.intValuation_lt_one_iff_mem s).1 h))
  have hs0 : (s : F) ≠ 0 := fun h0 => by rw [h0, map_zero] at hval; exact zero_ne_one hval
  have hc : (algebraMap F (Fv F v) (s : F))⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
    have : Valued.v (algebraMap F (Fv F v) (s : F)) = 1 := by
      rw [← hval]; exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (s : F)
    rw [this, inv_one]
  refine AddSubgroup.subset_closure ⟨_, hc, _, hs, ?_⟩
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def,
    mul_inv_cancel₀ ((map_ne_zero _).2 hs0)]

theorem val_le_of_mem_locId {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : w.under (𝓞 F) = v) {𝔞 : FractionalIdeal (𝓞 E)⁰ E} {y : Fv F v ⊗[F] E}
    (hy : y ∈ GlobalTheory.SnMass.locId v 𝔞) :
    Valued.v (toCompl hw y) ≤ WithZero.exp (-FractionalIdeal.count E w 𝔞) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, rfl⟩ := hy
    rw [toCompl_tmul, map_mul]
    have h1 : Valued.v (complMap hw c) ≤ 1 := complMap_mem hw hc
    have h2 : Valued.v (algebraMap E (w.adicCompletion E) a) ≤ WithZero.exp (-FractionalIdeal.count E w 𝔞) := by
      by_cases ha0 : a = 0
      · rw [ha0, map_zero, map_zero]; exact zero_le'
      have e : Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w a
      rw [e]
      have hc := FractionalIdeal.count_mono E w ((FractionalIdeal.spanSingleton_ne_zero_iff).2 ha0)
        (FractionalIdeal.spanSingleton_le_iff_mem.2 ha)
      rw [count_spanSingleton_of_ne w ha0] at hc
      have h0 : w.valuation E a ≠ 0 := by simpa using ha0
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      linarith
    calc _ ≤ 1 * WithZero.exp (-FractionalIdeal.count E w 𝔞) := mul_le_mul' h1 h2
      _ = _ := one_mul _
  | zero => rw [map_zero, map_zero]; exact zero_le'
  | add y z _ _ hy hz => rw [map_add]; exact (Valuation.map_add _ _ _).trans (max_le hy hz)
  | neg y _ hy => rw [map_neg, Valuation.map_neg]; exact hy

theorem mem_locId_of_count_le_ordAt (v : Pl F) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (h𝔞 : 𝔞 ≠ 0)
    (x : (Fv F v ⊗[F] E)ˣ)
    (hx : ∀ w ∈ Formalism.L2.Host.aboveF (L := E) F v, FractionalIdeal.count E w 𝔞 ≤ ordAt v w x) :
    (x : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v 𝔞 := by
  obtain ⟨a, ha0, ha⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger h𝔞
  set b : E := algebraMap (𝓞 E) E a with hb
  have hb0 : b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 ha0
  obtain ⟨x0, hx0⟩ := exists_sub_mem_intLoc v (((1 : Fv F v) ⊗ₜ[F] b⁻¹) * (x : Fv F v ⊗[F] E))
  have hmul : ∀ y ∈ intLoc F E v, ((1 : Fv F v) ⊗ₜ[F] b) * y ∈ GlobalTheory.SnMass.locId v 𝔞 := by
    intro y hy
    refine intLoc_induction (p := fun y => ((1 : Fv F v) ⊗ₜ[F] b) * y ∈ GlobalTheory.SnMass.locId v 𝔞)
      (fun c hc o => ?_) (by rw [mul_zero]; exact zero_mem _)
      (fun y z hy hz => by rw [mul_add]; exact add_mem hy hz) (fun y hy => by rw [mul_neg]; exact neg_mem hy) hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    refine AddSubgroup.subset_closure ⟨c, hc, b * o, ?_, rfl⟩
    have : (o : 𝓞 E) • b ∈ 𝔞 := Submodule.smul_mem _ o ha
    rwa [Algebra.smul_def, mul_comm] at this
  have hd : (x : Fv F v ⊗[F] E) - (1 : Fv F v) ⊗ₜ[F] (b * x0) ∈ GlobalTheory.SnMass.locId v 𝔞 := by
    have := hmul _ hx0
    convert this using 1
    rw [mul_sub, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_inv_cancel₀ hb0, ← Algebra.TensorProduct.one_def, one_mul]
  have hz : (1 : Fv F v) ⊗ₜ[F] (b * x0) ∈ GlobalTheory.SnMass.locId v 𝔞 := by
    refine one_tmul_mem_locId h𝔞 _ fun w hw => ?_
    have e1 : w.valuation E (b * x0) = Valued.v (toCompl hw ((1 : Fv F v) ⊗ₜ[F] (b * x0))) := by
      rw [toCompl_tmul, map_one, one_mul]
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).symm
    have e2 : Valued.v (toCompl hw (x : Fv F v ⊗[F] E)) ≤ WithZero.exp (-FractionalIdeal.count E w 𝔞) := by
      rw [← valAt_of_under hw, valAt_eq_exp, WithZero.exp_le_exp, neg_le_neg_iff]
      exact hx w (GlobalTheory.LFun.mem_aboveF.2 hw)
    have e3 := val_le_of_mem_locId hw hd
    rw [e1, show (1 : Fv F v) ⊗ₜ[F] (b * x0) =
      (x : Fv F v ⊗[F] E) - ((x : Fv F v ⊗[F] E) - (1 : Fv F v) ⊗ₜ[F] (b * x0)) by abel, map_sub]
    exact (Valuation.map_sub _ _ _).trans (max_le e2 e3)
  have := add_mem hd hz
  rwa [sub_add_cancel] at this

end GlobalTheory.UnrTate

end

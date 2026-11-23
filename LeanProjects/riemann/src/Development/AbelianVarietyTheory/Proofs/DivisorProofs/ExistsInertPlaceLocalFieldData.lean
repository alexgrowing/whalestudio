import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertPsi

open Formalism.UG GlobalTheory.LFun.InertChart GlobalTheory.InertCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_tmul (R : Type) [CommRing R] [Algebra F R] [Module.Free F E] [Module.Finite F E] (c : R) (x : E) :
    Algebra.trace R (R ⊗[F] E) (c ⊗ₜ[F] x) = c * algebraMap F R (Algebra.trace F E x) := by
  have h1 : c ⊗ₜ[F] x = c • ((1 : R) ⊗ₜ[F] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, LinearMap.map_smul, smul_eq_mul]
  congr 1
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  refine LinearMap.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem trace_singleTens (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) :
    Algebra.trace (AF F) (AF F ⊗[F] E) (Supp.singleTens E v y) =
      GlobalTheory.EmbChart.atPlace v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [show Supp.singleTens E v (a ⊗ₜ[F] x) = GlobalTheory.EmbChart.atPlace v a ⊗ₜ[F] x from
      GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ a x, trace_tmul, trace_tmul, mul_comm a, ← Algebra.smul_def,
      LinearMap.map_smul, Algebra.smul_def, mul_comm]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem trace_mem {v : HeightOneSpectrum (𝓞 F)} {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y ∈ v.adicCompletionIntegers F := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine intLoc_induction (p := fun y => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y ∈ v.adicCompletionIntegers F)
    (fun a ha x => ?_) (by simp) (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)
    (fun y hy => by rw [map_neg]; exact neg_mem hy) hy
  rw [trace_tmul]
  refine mul_mem ha ?_
  have hint : IsIntegral ℤ (Algebra.trace F E (x : E)) := Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe x)
  have := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) v (⟨_, hint⟩ : 𝓞 F)
  convert this using 1
  first | rfl | simp | (exact (IsScalarTower.algebraMap_apply (𝓞 F) F (Fv F v) (⟨_, hint⟩ : 𝓞 F)))

theorem odd_absNorm {v : HeightOneSpectrum (𝓞 F)} (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : Odd (Ideal.absNorm v.asIdeal) := by
  have hc : Nat.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  haveI := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ h0)
  letI := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)
  by_contra hodd
  have h1 : ringChar (𝓞 F ⧸ v.asIdeal) = 2 := by
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, hc]
    exact Nat.even_iff.1 (Nat.not_odd_iff_even.1 hodd)
  have h3 : ((2 : ℕ) : 𝓞 F ⧸ v.asIdeal) = 0 := (ringChar.spec _ 2).2 (by rw [h1])
  apply h2
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [map_ofNat]
  simpa using h3

end GlobalTheory.InertPsi

namespace GlobalTheory.InertPsi

open Formalism.UG GlobalTheory.LFun.InertChart GlobalTheory.InertCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {σ : E →ₐ[F] E}
  {h : w.under (𝓞 F) = v} {c : w.adicCompletion E →+* w.adicCompletion E}

theorem exists_unif (hσ : IsCMExt F E σ) (hw : IsInertAt F E v w) (hc : IsConjAt σ h c) :
    ∃ s : F, IsUnramInv (complMap h (algebraMap F (Fv F v) s)) c (qV F v) := by
  have hval : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  obtain ⟨s, hs, hs2⟩ := SetLike.not_le_iff_exists.1 (mt Ideal.map_le_iff_le_comap.2 (not_map_le_sq hw))
  have hs1 : algebraMap (𝓞 F) (𝓞 E) s ∈ w.asIdeal := hw ▸ Ideal.mem_map_of_mem _ hs
  refine ⟨(s : F), ?_⟩
  have hϖ : complMap h (algebraMap F (Fv F v) (s : F)) =
      algebraMap E (w.adicCompletion E) (algebraMap (𝓞 F) (𝓞 E) s : E) := by
    rw [complMap_algebraMap]; rfl
  rw [hϖ]
  set ϖ : w.adicCompletion E := algebraMap E _ (algebraMap (𝓞 F) (𝓞 E) s : E) with hϖ'
  have h1 : c ϖ = ϖ := (conj_algebraMap hc _).trans (congrArg _ (σ.commutes (s : F)))
  have h2 : Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
    rw [hϖ', hval, HeightOneSpectrum.valuation_of_algebraMap]
    have a := (w.intValuation_le_pow_iff_mem _ 1).2 (by rwa [pow_one])
    have b := not_le.1 (mt (w.intValuation_le_pow_iff_mem _ 2).1 hs2)
    have h0 : w.intValuation (algebraMap (𝓞 F) (𝓞 E) s) ≠ 0 := b.ne_bot
    rw [← WithZero.exp_log h0] at a b ⊢
    rw [WithZero.exp_le_exp] at a
    rw [WithZero.exp_lt_exp] at b
    congr 1
    omega
  have h3 : ∀ u, Valued.v u = 1 → Valued.v (c u) = 1 := fun u hu => by
    have a : Valued.v (c u) ≤ 1 := conj_mem hw hc hu.le
    have b : Valued.v (c u⁻¹) ≤ 1 := conj_mem hw hc (show Valued.v u⁻¹ ≤ 1 by rw [map_inv₀, hu, inv_one])
    have h0 : u ≠ 0 := fun h0 => by simp [h0] at hu
    rw [map_inv₀, map_inv₀, inv_le_one₀ (by simpa [pos_iff_ne_zero] using h0)] at b
    exact le_antisymm a b
  refine ⟨fun x => ?_, fun x => ?_, h1, h2, ?_, one_lt_absNorm v, ?_⟩
  · obtain ⟨y, rfl⟩ := toCompl_surjective h x
    rw [hc, hc]
    congr 1
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (conj_conj hσ x)
    | add x y hx hy => simp only [map_add, hx, hy]
  · by_cases h0 : x = 0
    · simp [h0]
    have h0' : Valued.v x ≠ 0 := by simpa using h0
    have a : Valued.v (x * ϖ ^ WithZero.log (Valued.v x)) = 1 := by
      rw [map_mul, map_zpow₀, h2, ← WithZero.exp_zsmul, ← WithZero.exp_log h0', ← WithZero.exp_add]
      simp
    have b := h3 _ a
    rw [map_mul, map_zpow₀, h1, ← a, map_mul, map_mul] at b
    exact mul_right_cancel₀ (by rw [map_zpow₀, h2]; exact zpow_ne_zero _ WithZero.exp_ne_zero) b
  · obtain ⟨x, hx⟩ := exists_conj_sub_unit hσ hw
    exact ⟨algebraMap E _ (x : E), GlobalTheory.AdeleBaseChange.algebraMap_int_mem x w, by
      rw [conj_algebraMap hc, ← map_sub, hval, hx]⟩
  · exact (P.tjcosets_card_residue w).trans (absNorm_eq hσ.2.2.1 hw)

end GlobalTheory.InertPsi

open GlobalTheory.InertPsi in
theorem GlobalTheory.InertPsi.exists_field_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v),
    ∃ (ϖ : w.adicCompletion E) (σL : w.adicCompletion E →+* w.adicCompletion E) (q : ℕ) (ψL : AddChar (w.adicCompletion E) ℂ),
      IsConjAt σ h σL ∧ Formalism.UG.IsUnramInv ϖ σL q ∧ Odd q ∧
      (∀ z ∈ Formalism.UG.intL (w.adicCompletion E), σL z = z → ψL z = 1) ∧
      (∃ z ∈ Formalism.UG.intL (w.adicCompletion E), σL z = z ∧ ψL (ϖ⁻¹ * z) ≠ 1) ∧
      ∀ z, ψL ((z + σL z) / 2) = B.ψ (⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) (-1 * ptAt hw h z)) := by
  intro F E _ _ _ _ _ σ B hB v w hw h
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨c, hc, -⟩ := InertChart.existsUnique_isConjAt σ hw h
  obtain ⟨s, hU⟩ := exists_unif hB.cm hw hc
  obtain ⟨h2, -, hψ⟩ := hB.inert v w hw
  set k := evFin F v (⅟(2 : AF F)) with hk'
  have hk2 : k * 2 = 1 := by
    rw [hk', ← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  have hv2 : Valued.v (2 : Fv F v) = 1 := by
    rw [← map_ofNat (algebraMap F (Fv F v)) 2]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (2 : F)).trans ?_
    rw [← map_ofNat (algebraMap (𝓞 F) F) 2, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 h2
  have hk : k ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have := congrArg Valued.v hk2
    rw [map_mul, hv2, mul_one, map_one] at this
    exact this.le
  have hO : ∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v y = 1 := fun y hy => by
    simpa using (hψ 1).2 (one_mem _) y hy
  let ψL : AddChar (w.adicCompletion E) ℂ :=
    { toFun := fun z => B.ψ (⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) (-1 * ptAt hw h z))
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b => by
        simp only [map_add, mul_add, AddChar.map_add_eq_mul] }
  have hval : ∀ z, ψL z = psiLoc B.ψ v
      (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((InertChart.complEquiv hw h).symm (-z)) * k) := fun z => by
    show B.ψ _ = _
    rw [neg_one_mul, ← map_neg (ptAt hw h), ptAt_apply, trace_singleTens, mul_comm,
      GlobalTheory.EmbChart.atPlace_mul_right]
    rfl
  have hcm : ∀ a : Fv F v, (InertChart.complEquiv hw h).symm (complMap h a) = a ⊗ₜ[F] (1 : E) := fun a =>
    (InertChart.complEquiv hw h).symm_apply_eq.2 (by
      show complMap h a = toCompl h (a ⊗ₜ[F] (1 : E))
      rw [toCompl_tmul, map_one, mul_one])
  have htr1 : algebraMap F (Fv F v) (Algebra.trace F E 1) = 2 := by
    rw [show (1 : E) = algebraMap F E 1 from (map_one _).symm, Algebra.trace_algebraMap, hB.cm.2.2.1]
    first | simp [map_ofNat] | (simp; exact map_ofNat _ 2) | (rw [nsmul_eq_mul, mul_one, Nat.cast_ofNat, map_ofNat])
  have hvalc : ∀ a, ψL (complMap h a) = psiLoc B.ψ v (-a) := fun a => by
    rw [hval, ← map_neg, hcm, trace_tmul, htr1, mul_assoc, mul_comm 2 k, hk2, mul_one]
  refine ⟨complMap h (algebraMap F (Fv F v) s), c, Formalism.UG.qV F v, ψL, hc, hU, odd_absNorm h2, ?_, ?_, ?_⟩
  · intro z hz _
    rw [hval]
    refine hO _ (mul_mem (trace_mem ((InertChart.mem_intLoc_iff hw h _).2 ?_)) hk)
    rw [show toCompl h ((InertChart.complEquiv hw h).symm (-z)) = -z from
      (InertChart.complEquiv hw h).apply_symm_apply (-z)]
    exact neg_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hz)
  · have hs : (algebraMap F (Fv F v) s)⁻¹ ∉ v.adicCompletionIntegers F := fun hm => by
      have h4 := complMap_mem h hm
      have h5 : Valued.v (complMap h (algebraMap F (Fv F v) s))⁻¹ ≤ 1 := by
        rw [← map_inv₀]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h4
      rw [map_inv₀, hU.2.2.2.1] at h5
      exact absurd h5 (by decide)
    obtain ⟨y, hy, hne⟩ : ∃ y ∈ v.adicCompletionIntegers F,
        psiLoc B.ψ v ((algebraMap F (Fv F v) s)⁻¹ * y) ≠ 1 := by
      have := mt (hψ _).1 hs
      push_neg at this
      exact this
    have ht : ∀ a, toCompl h (a ⊗ₜ[F] (1 : E)) = complMap h a := fun a => by
      rw [toCompl_tmul, map_one, mul_one]
    refine ⟨complMap h (-y), (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (complMap_mem h (neg_mem hy)),
      ?_, ?_⟩
    · rw [← ht, hc]
      congr 1
      show (-y) ⊗ₜ[F] σ 1 = _
      rw [map_one]
    · rw [← map_inv₀, ← map_mul, hvalc]
      convert hne using 2
      ring
  · intro z
    show B.ψ _ = B.ψ _
    have hcc : ∀ x, cA σ (cA σ x) = x := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (InertChart.conj_conj hB.cm x)
      | add x y hx hy => simp only [map_add, hx, hy]
    let cE : AE F E ≃ₐ[AF F] AE F E := AlgEquiv.ofAlgHom (cA σ) (cA σ) (AlgHom.ext hcc) (AlgHom.ext hcc)
    have hT : ∀ x, Algebra.trace (AF F) (AE F E) (cA σ x) = Algebra.trace (AF F) (AE F E) x := fun x =>
      Algebra.trace_eq_of_algEquiv cE x
    haveI : NeZero (2 : w.adicCompletion E) := ⟨fun h0 => two_ne_zero ((map_eq_zero_iff _ (algebraMap E (w.adicCompletion E)).injective).1 ((map_ofNat _ 2).trans h0))⟩
    set y := (z + c z) / 2
    have hy : y + y = z + c z := add_halves _
    have key : Algebra.trace (AF F) (AE F E) (ptAt hw h y) = Algebra.trace (AF F) (AE F E) (ptAt hw h z) := by
      have e1 : Algebra.trace (AF F) (AE F E) (ptAt hw h y) + Algebra.trace (AF F) (AE F E) (ptAt hw h y) =
          Algebra.trace (AF F) (AE F E) (ptAt hw h z) + Algebra.trace (AF F) (AE F E) (ptAt hw h z) := by
        rw [← map_add, ← map_add (ptAt hw h), hy, map_add, map_add, ← cA_ptAt hw h σ hc, hT]
      have e2 : ∀ t : AF F, t = ⅟(2 : AF F) * (t + t) := fun t => by
        rw [← two_mul, ← mul_assoc, invOf_mul_self, one_mul]
      rw [e2 (Algebra.trace _ _ (ptAt hw h y)), e1, ← e2]
    rw [neg_one_mul, neg_one_mul, map_neg, map_neg, key]

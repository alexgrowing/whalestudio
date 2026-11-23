import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.EtaVCases

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem sig_ne (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  intro hs
  obtain ⟨-, htc, -, h4⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  have hr : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := h4 τ x
    rw [hs, AlgHom.id_apply] at this
    rw [starRingEnd_apply]; exact this.symm
  exact InfinitePlace.not_isReal_iff_isComplex.2 (htc.isComplex (InfinitePlace.mk τ))
    (InfinitePlace.isReal_mk_iff.2 hr)

theorem fix_range (h : IsCMExt F E σ) {y : E} (hy : σ y = y) : ∃ c : F, algebraMap F E c = y := by
  by_contra hne
  push Not at hne
  have li : LinearIndependent F ![(1 : E), y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hne (-(t⁻¹ * s))
      have hy' : y = t⁻¹ • (t • y) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [hy', eq_neg_of_add_eq_zero_right hst, smul_neg, smul_smul, Algebra.algebraMap_eq_smul_one, neg_smul]
  have hsp := li.span_eq_top_of_card_eq_finrank' (by simpa using h.2.2.1.symm)
  apply sig_ne σ h
  have hl : σ.toLinearMap = LinearMap.id := by
    refine LinearMap.ext_on_range hsp fun i => ?_
    fin_cases i
    · simp
    · simpa using hy
  exact AlgHom.ext fun x => LinearMap.congr_fun hl x

theorem fix_int (h : IsCMExt F E σ) (y : 𝓞 E) (hy : sigO σ y = y) :
    ∃ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a = y := by
  have hy' : σ (y : E) = y := by rw [← sigO_coe, hy]
  obtain ⟨c, hc⟩ := fix_range σ h hy'
  have hint : IsIntegral ℤ c := by
    rw [← isIntegral_algebraMap_iff (A := F) (B := E) (FaithfulSMul.algebraMap_injective F E), hc]
    exact y.isIntegral_coe
  refine ⟨⟨c, (mem_integralClosure_iff ℤ F).2 hint⟩, RingOfIntegers.ext ?_⟩
  exact hc

theorem qInert_holds : QInert σ J ψ v := by
  intro hstd hun hp hid
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI : (IE (E := E) v).IsMaximal := hp.isMaximal (IE_ne_bot v)
  letI : Field (QE (E := E) v) := Ideal.Quotient.field _
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := finite_res v
  have hfr : Module.finrank (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) = 2 := by
    rw [Ideal.finrank_quotient_map (p := v.asIdeal) (K := F) (L := E)]
    exact hstd.1.2.2.1
  have hsig : ∀ x : QE (E := E) v, sigQ σ v x = x := fun x => by rw [hid]; rfl

  have hmem : ∀ x : QE (E := E) v, (∃ c, algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c = x + x) ∧
      ∃ c, algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c = x * x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hs : Ideal.Quotient.mk (IE (E := E) v) (sigO σ y) = Ideal.Quotient.mk _ y := by
      rw [← sigQ_mk]; exact hsig _
    have hss : sigO σ (sigO σ y) = y := RingOfIntegers.ext (by simp only [sigO_coe]; exact sig_sig σ hstd.1 _)
    obtain ⟨a, ha⟩ := fix_int σ hstd.1 (y + sigO σ y) (by rw [map_add, hss, add_comm])
    obtain ⟨b, hb⟩ := fix_int σ hstd.1 (y * sigO σ y) (by rw [map_mul, hss, mul_comm])
    refine ⟨⟨Ideal.Quotient.mk _ a, ?_⟩, ⟨Ideal.Quotient.mk _ b, ?_⟩⟩
    · rw [Ideal.Quotient.algebraMap_quotient_map_quotient, ha, map_add, hs]
    · rw [Ideal.Quotient.algebraMap_quotient_map_quotient, hb, map_mul, hs]
  haveI : Module.Finite (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) := Module.finite_of_finrank_pos (by omega)
  haveI : Finite (QE (E := E) v) := Module.finite_of_finite (𝓞 F ⧸ v.asIdeal)
  letI := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)
  letI := Fintype.ofFinite (QE (E := E) v)
  have hc : Fintype.card (QE (E := E) v) = Fintype.card (𝓞 F ⧸ v.asIdeal) ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := 𝓞 F ⧸ v.asIdeal) (V := QE (E := E) v), hfr]
  have h1 : 1 < Fintype.card (𝓞 F ⧸ v.asIdeal) := Fintype.one_lt_card
  have hle : Fintype.card (QE (E := E) v) ≤ Fintype.card (𝓞 F ⧸ v.asIdeal) := by
    by_cases h2 : (2 : QE (E := E) v) = 0
    · refine Fintype.card_le_of_injective (fun x => (hmem x).2.choose) fun x y hxy => ?_
      have hx : algebraMap _ _ (hmem x).2.choose = x * x := (hmem x).2.choose_spec
      have hy : algebraMap _ _ (hmem y).2.choose = y * y := (hmem y).2.choose_spec
      have hxy2 : (hmem x).2.choose = (hmem y).2.choose := hxy
      have hxy' : x * x = y * y := by rw [← hx, ← hy, hxy2]
      have h0 : (x - y) * (x - y) = 0 := by
        have : (x - y) * (x - y) = x * x + y * y - 2 * (x * y) := by ring
        rw [this, h2, zero_mul, sub_zero, hxy', ← two_mul, h2, zero_mul]
      exact sub_eq_zero.1 (mul_self_eq_zero.1 h0)
    · refine Fintype.card_le_of_injective (fun x => (hmem x).1.choose) fun x y hxy => ?_
      have hx : algebraMap _ _ (hmem x).1.choose = x + x := (hmem x).1.choose_spec
      have hy : algebraMap _ _ (hmem y).1.choose = y + y := (hmem y).1.choose_spec
      have hxy2 : (hmem x).1.choose = (hmem y).1.choose := hxy
      have hxy' : x + x = y + y := by rw [← hx, ← hy, hxy2]
      rw [← two_mul, ← two_mul] at hxy'
      exact mul_left_cancel₀ h2 hxy'
  rw [hc] at hle
  nlinarith

end PI.OmLocU.Red

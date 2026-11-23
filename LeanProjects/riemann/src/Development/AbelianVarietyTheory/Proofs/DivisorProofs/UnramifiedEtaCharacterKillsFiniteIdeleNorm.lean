import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced

noncomputable section

namespace GlobalTheory.EtaTildeNorm

section SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.IdlFact GlobalTheory.Mem.Chr.KDVal
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.Col2.SplitChar

theorem map_finPartI_locF {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra F L] (χ : HChar L)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ.1 (finPartI L (locF F v k)) = χ.resFin v k := by
  unfold HChar.resFin
  rw [MonoidHom.finsetProd_apply]
  unfold locF
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun Q _ => congrArg χ.1 (GlobalTheory.Mem.KerDet.finPartI_localIdele Q _)

theorem eq_one (D : D7) (χ : HChar D.host.E) (hχ : IsEtaT D.host χ) (x : (AE D)ˣ) :
    χ.1 (finIdl D (x * sgU D x)) = 1 := by
  classical
  obtain ⟨c, hc, hcm, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have ec : c.toRingEquiv = D.host.conj.toRingEquiv := RingEquiv.ext hc
  set a : Ideles D.host.E := finIdl D (x * sgU D x) with ha_def
  have ha : a ∈ balanced (L := D.host.E) D.host.F := norm_balanced x
  let T : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
    (finite_valAt_ne_one a).toFinset.image fun w => w.under (𝓞 D.host.F)
  let m : HeightOneSpectrum (𝓞 D.host.F) → ℤ := fun v =>
    if h : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v then -WithZero.log (valAt h.choose a) else 0
  let b : Ideles D.host.E := ∏ v ∈ T, locF (L := D.host.E) D.host.F v (unif v) ^ m v
  have hm : ∀ w : HeightOneSpectrum (𝓞 D.host.E), m (w.under (𝓞 D.host.F)) = -WithZero.log (valAt w a) := fun w => by
    have hex : ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := ⟨w, rfl⟩
    simp only [m]
    rw [dif_pos hex, ha w hex.choose hex.choose_spec]
  have hval : ∀ w, valAt w b = valAt w a := fun w => by
    have h1 : ∀ v, v ≠ w.under (𝓞 D.host.F) → valAt w (locF (L := D.host.E) D.host.F v (unif v) ^ m v) = 1 :=
      fun v hv => by rw [map_zpow, valAt_locF, if_neg hv.symm, one_zpow]
    simp only [b]
    rw [map_prod]
    by_cases hw : w.under (𝓞 D.host.F) ∈ T
    · rw [Finset.prod_eq_single_of_mem _ hw (fun v _ hv => h1 v hv), map_zpow, valAt_locF, if_pos rfl, hu,
        ordF_unif_self, ← WithZero.exp_zsmul, hm]
      simp only [smul_eq_mul, mul_neg, neg_neg, mul_one]
      exact WithZero.exp_log (valAt_ne_zero w a)
    · rw [Finset.prod_eq_one (fun v hv => h1 v (fun e => hw (e ▸ hv)))]
      by_contra hne
      exact hw (Finset.mem_image_of_mem _ (by simpa using fun e => hne e.symm))
  have hu' : b⁻¹ * a ∈ unitIdl D.host.E := fun w => by
    rw [← valAt_apply, map_mul, map_inv, hval]
    exact inv_mul_cancel₀ (valAt_ne_zero w a)

  have h1 : χ.1 (finPartI D.host.E (b⁻¹ * a)) = 1 :=
    GlobalTheory.Mem.LocTriv.eq_one_of_local _ χ.1 χ.2.1 _ (finPartI_mem_unitIdl.2 hu') (fun _ => rfl) fun v y hy =>
      hχ.unr v y (by
        unfold IsUnitAt
        rw [hy]
        exact hu' v)

  have h2 : χ.1 (finPartI D.host.E b) = 1 := by
    simp only [b]
    rw [map_prod, map_prod]
    refine Finset.prod_eq_one fun v hv => ?_
    rw [map_zpow, map_zpow, map_finPartI_locF, hχ.res.1 v, etaFin]
    split_ifs with hcard
    · rw [ordF_unif_self, zpow_one]
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hv
      rw [hm]
      obtain ⟨w', hw', -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv w
      have hund : w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) :=
        (under_eq_iff_conjPl c hcm.rank hcm.ne w w').2 (Or.inr (by rw [ec]; exact hw'))
      have hmem : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) →
          Q ∈ aboveF (L := D.host.E) D.host.F (w.under (𝓞 D.host.F)) := fun Q hQ => by
        simp [aboveF, hQ]
      have hww : w' = w := Finset.card_le_one.1 hcard.le _ (hmem w' hund) _ (hmem w rfl)
      subst hww
      have e1 : valAt w' a = vl D w' (x : AE D) * vl D w' (x : AE D) := by
        change vl D w' ((x : AE D) * sgA D x) = _
        rw [map_mul, vl_sgA hw' x]
      have h0 : vl D w' (x : AE D) ≠ 0 := by
        intro h
        have := valAt_ne_zero w' a
        rw [e1, h, zero_mul] at this
        exact this rfl
      rw [e1, WithZero.log_mul h0 h0]
      exact Even.neg_one_zpow (Even.add_self _).neg
    · exact one_zpow _
  have e : a = b * (b⁻¹ * a) := (mul_inv_cancel_left b a).symm
  have e2 : finPartI D.host.E a = a := by rw [ha_def]; exact finPartI_finIdl D _
  rw [← e2, e, map_mul, map_mul, h1, h2, one_mul]

end SlopeTestRemainingChoices

end GlobalTheory.EtaTildeNorm

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

theorem GlobalTheory.EtaTildeNorm.map_finIdl_norm : ∀ (D : D7) (χ : HChar D.host.E), Formalism.L2.Host.IsEtaT D.host χ →
    ∀ x : (AE D)ˣ, χ.1 (finIdl D (x * sgU D x)) = 1 :=
  fun D χ hχ x => GlobalTheory.EtaTildeNorm.eq_one D χ hχ x

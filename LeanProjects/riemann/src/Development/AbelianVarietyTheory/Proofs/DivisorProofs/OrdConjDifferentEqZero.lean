import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniversalTripleFibreAtFramedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSectionThetaKeyRuleWeightFourStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionFourthRootPerComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionNormComplexPointsEqTwoPiPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemCuspFormsOfBoundedSectionComponentStatement

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

namespace GlobalTheory.KeyRootTw

theorem wtOf_zero_fst : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (m : ℤ) (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → (wtOf Dw 0 m).1 (τ, i) = -m := by
  intro E _ _ _ H Dw m τ i hi
  unfold Datum.mult at hi
  by_cases h : τ (H.rt : E) = H.rt0
  · rw [if_pos h] at hi
    simp only [wtOf, dif_pos h, dif_pos hi, Pi.zero_apply, zero_sub]
  · rw [if_neg h] at hi
    have h' : conjEmb τ (H.rt : E) = H.rt0 := conj_mem h
    simp only [wtOf, dif_neg h, dif_pos h', dif_pos hi, Pi.zero_apply, neg_zero, zero_sub]

theorem homN_root : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (ρ : (Rul Xo c)ˣ) (K : Rul Xo c) (a : c.F) (C : ℝ), a ≠ 0 → 0 < C → idem Z * (ρ : Rul Xo c) ^ 4 = a • (idem Z * K) → (∀ k, ∀ y ∈ (U.X k).dom, homN U x (wtOf Dw 0 (-4)) K ⟨k, y⟩ = C) → ∀ z ∈ framesOn U Z, (∀ hz : z.2 ∈ (U.X z.1).dom, Tested (U.un z.1 ⟨z.2, hz⟩)) → homN U x (wtOf Dw 0 1) (idem Z * ((ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c)) z = (‖σ a‖ * C) ^ (-(1 / 4) : ℝ) ∧ homN U x (wtOf Dw 0 (-1)) (idem Z * (ρ : Rul Xo c)) z = (‖σ a‖ * C) ^ ((1 / 4) : ℝ) := by
  intro E _ _ _ H Dw l Xo c σ r U x Z ρ K a C ha hC hρ hK z hz ht
  obtain ⟨hd, hl⟩ := hz
  have hA : 0 < ‖σ a‖ * C := mul_pos (norm_pos_iff.2 ((map_ne_zero σ).2 ha)) hC
  have h1 := homN_idem U x hd hl (ht hd)
  have hm : ∀ (m m' : ℤ) (f g : Rul Xo c), homN U x (wtOf Dw 0 (m + m')) (f * g) z =
      homN U x (wtOf Dw 0 m) f z * homN U x (wtOf Dw 0 m') g z := fun m m' f g => by
    rw [← homN_mul U x (even_wtOf _ _) (even_wtOf _ _) f g z hd, ← wtOf_add, add_zero]
  rw [← wtOf_zero (Dw := Dw)] at h1
  have h2 : homN U x (wtOf Dw 0 (-4)) (a • (idem Z * K)) z = ‖σ a‖ * C := by
    have := hm 0 (-4) (idem Z) K
    rw [zero_add, h1, one_mul] at this
    rw [homN_smul, this, hK z.1 z.2 hd]
  have hi := idem_mul_idem Z
  have h3 : homN U x (wtOf Dw 0 (-1)) (idem Z * (ρ : Rul Xo c)) z ^ 4 = ‖σ a‖ * C := by
    have e : idem Z * (ρ : Rul Xo c) ^ 4 = idem Z * (ρ : Rul Xo c) * (idem Z * (ρ : Rul Xo c)) *
        (idem Z * (ρ : Rul Xo c) * (idem Z * (ρ : Rul Xo c))) := by
      rw [mul_mul_mul_comm (idem Z), hi, mul_mul_mul_comm (idem Z), hi]; ring
    rw [← h2, ← hρ, e, show (-4 : ℤ) = (-1 + -1) + (-1 + -1) by norm_num, hm, hm]
    ring
  have h4 : homN U x (wtOf Dw 0 (-1)) (idem Z * (ρ : Rul Xo c)) z = (‖σ a‖ * C) ^ ((1 / 4) : ℝ) := by
    rw [← h3, ← Real.rpow_natCast, ← Real.rpow_mul (homN_nonneg _ _ _ _ _)]
    norm_num
  refine ⟨?_, h4⟩
  have h5 := hm 1 (-1) (idem Z * ((ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c)) (idem Z * (ρ : Rul Xo c))
  rw [mul_mul_mul_comm, hi, Units.inv_mul, mul_one, add_neg_cancel, h1, h4] at h5
  rw [Real.rpow_neg hA.le]
  exact eq_inv_of_mul_eq_one_left h5.symm

theorem val_root : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : Comp Xo c) (w : HeightOneSpectrum (𝓞 c.F)) (v : Rul Xo c → EReal), v ∈ valOn Z w → ∀ (ρ : (Rul Xo c)ˣ) (K : Rul Xo c) (a : c.F) (B : ℝ), a ≠ 0 → idem Z * (ρ : Rul Xo c) ^ 4 = a • (idem Z * K) → 0 ≤ v K → v K ≤ ((4 * B : ℝ) : EReal) → ((-(vAdd w a : ℝ) / 4 - B : ℝ) : EReal) ≤ v (idem Z * ((ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c)) ∧ v (idem Z * ((ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c)) ≤ ((-(vAdd w a : ℝ) / 4 : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c Z w v hv ρ K a B ha hρ h0 h1
  have hV := isVal_valOn hv
  have hi := val_idem hv
  have hone : v 1 = 0 := by
    have := hV.mul (idem Z) 1
    rwa [mul_one, hi, zero_add, eq_comm] at this
  have hu := hV.mul (ρ : Rul Xo c) ((ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c)
  rw [Units.mul_inv, hone] at hu
  have h4 := congrArg v hρ
  rw [hV.smul _ _ ha, hV.mul, hV.mul, hi, zero_add, zero_add,
    show (ρ : Rul Xo c) ^ 4 = ρ * ρ * (ρ * ρ) by ring, hV.mul, hV.mul] at h4
  rw [hV.mul, hi, zero_add]
  have n1 := hV.ne_bot (ρ : Rul Xo c)
  have n2 := hV.ne_bot ((ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c)
  have t1 : v (ρ : Rul Xo c) ≠ ⊤ := fun h => by
    rw [h, EReal.top_add_of_ne_bot n2] at hu; exact EReal.zero_ne_top hu
  have t2 : v ((ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) ≠ ⊤ := fun h => by
    rw [h, EReal.add_top_of_ne_bot n1] at hu; exact EReal.zero_ne_top hu
  lift v (ρ : Rul Xo c) to ℝ using ⟨t1, n1⟩ with p
  lift v ((ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) to ℝ using ⟨t2, n2⟩ with q
  lift v K to ℝ using ⟨(h1.trans_lt (EReal.coe_lt_top _)).ne, hV.ne_bot K⟩ with k
  rw [← EReal.coe_add, ← EReal.coe_zero, EReal.coe_eq_coe_iff] at hu
  rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_eq_coe_iff] at h4
  rw [← EReal.coe_zero, EReal.coe_le_coe_iff] at h0
  rw [EReal.coe_le_coe_iff] at h1
  exact ⟨EReal.coe_le_coe_iff.2 (by linarith), EReal.coe_le_coe_iff.2 (by linarith)⟩

theorem ord_conjDifferent_eq_zero : ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] (φ : E →+* K) (w : HeightOneSpectrum (𝓞 K)), (∀ p : ℕ, p.Prime → p ∣ (NumberField.discr E).natAbs → ((p : ℕ) : 𝓞 K) ∉ w.asIdeal) → ord_vw w (conjDifferent φ) = 0 := by
  intro K E _ _ _ _ φ w hw
  rw [GlobalTheory.DefectSumCompare.ord_vw_eq_vla w (conjDifferent_ne_bot φ)]
  by_contra h0
  have hd := (QAt.BeSumPf.vla_ne_zero_iff w (conjDifferent_ne_bot φ)).1 h0
  letI := φ.toAlgebra
  have h2 : Ideal.absNorm (conjDifferent φ) = (discr E).natAbs ^ Module.finrank E K := by
    have := Ideal.absNorm_algebraMap (𝓞 E) (𝓞 K) (differentIdeal ℤ (𝓞 E))
    rw [absNorm_differentIdeal E, ← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 K) K] at this
    exact this
  have h3 := Ideal.le_of_dvd hd (Ideal.absNorm_mem (conjDifferent φ))
  rw [h2, Nat.cast_pow] at h3
  have h4 := w.isPrime.mem_of_pow_mem _ h3
  have key : ∀ n : ℕ, n ≠ 0 → (n : 𝓞 K) ∈ w.asIdeal → ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : 𝓞 K) ∈ w.asIdeal := by
    intro n
    induction n using induction_on_primes with
    | zero => exact fun h => absurd rfl h
    | one => exact fun _ h => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) w.isPrime.ne_top
    | prime_mul p n hp ih =>
      intro hn hm
      rw [Nat.cast_mul] at hm
      rcases w.isPrime.mem_or_mem hm with h | h
      · exact ⟨p, hp, dvd_mul_right _ _, h⟩
      · obtain ⟨p', h1, h2, h3⟩ := ih (right_ne_zero_of_mul hn) h
        exact ⟨p', h1, h2.mul_left _, h3⟩
  obtain ⟨p, hp, hpd, hpw⟩ := key _ (Int.natAbs_ne_zero.mpr (discr_ne_zero E)) h4
  exact hw p hp hpd hpw

theorem le_lineDeg_root : ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] (m : (E →+* ℂ) → ℕ) (φ : (E →+* ℂ) → (E →+* K)) (g : ℕ) (a : K) (C : (K →+* ℂ) → ℝ), a ≠ 0 → (∀ σ, 0 < C σ) → (∀ σ, |Real.log (C σ)| ≤ 2 * (g : ℝ) * Real.log (2 * Real.pi)) → ∑ τ, m τ = g → -((g : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd E)) ≤ lineDeg (fun σ => (‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ)) (fun w => -(vAdd w a : ℝ) / 4 - ∑ τ, (m τ : ℝ) * (ord_vw w (conjDifferent (φ τ)) : ℝ)) := by
  intro K E _ _ _ _ m φ g a C ha hC hlog hg
  have hK : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  have h0 := lineDeg_num ha
  have hf := fin_mul (finite_vAdd ha) (lw K)
  have h1 : ∑ᶠ w, (-(vAdd w a : ℝ) / 4 - ∑ τ, (m τ : ℝ) * (ord_vw w (conjDifferent (φ τ)) : ℝ)) * lw K w =
      -(1 / 4) * ∑ᶠ w, (vAdd w a : ℝ) * lw K w - g * lrd E := by
    have e : ∀ w, (-(vAdd w a : ℝ) / 4 - ∑ τ, (m τ : ℝ) * (ord_vw w (conjDifferent (φ τ)) : ℝ)) * lw K w =
        -(1 / 4) * ((vAdd w a : ℝ) * lw K w) -
          ∑ τ, (m τ : ℝ) * ((ord_vw w (conjDifferent (φ τ)) : ℝ) * lw K w) := fun w => by
      rw [sub_mul, Finset.sum_mul]
      simp only [mul_assoc]
      ring
    have f2 : ∀ τ, (Function.support fun w => (m τ : ℝ) * ((ord_vw w (conjDifferent (φ τ)) : ℝ) * lw K w)).Finite :=
      fun τ => (fin_mul (finite_ord (φ τ)) (lw K)).subset (Function.support_mul_subset_right _ _)
    have f3 : (Function.support fun w =>
        ∑ τ, (m τ : ℝ) * ((ord_vw w (conjDifferent (φ τ)) : ℝ) * lw K w)).Finite :=
      (Set.finite_iUnion f2).subset fun w hw => by
        obtain ⟨τ, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
        exact Set.mem_iUnion.2 ⟨τ, h⟩
    rw [finsum_congr e, finsum_sub_distrib (hf.subset (Function.support_mul_subset_right _ _)) f3, ← mul_finsum,
      finsum_sum_comm _ _ fun τ _ => f2 τ]
    simp only [← mul_finsum, sum_ord]
    rw [← Finset.sum_mul, ← hg]
    push_cast
    rfl
  have h2 : ∑ σ : K →+* ℂ, Real.log ((‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ)) =
      -(1 / 4) * (∑ σ : K →+* ℂ, Real.log ‖σ a‖ + ∑ σ, Real.log (C σ)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hp : 0 < ‖σ a‖ := norm_pos_iff.2 ((map_ne_zero σ).2 ha)
    rw [Real.log_rpow (mul_pos hp (hC σ)), Real.log_mul hp.ne' (hC σ).ne']
  have h3 : -(2 * (g : ℝ) * Real.log (2 * Real.pi)) ≤ (∑ σ, Real.log (C σ)) / (Module.finrank ℚ K : ℝ) := by
    rw [le_div_iff₀ hK]
    have := Finset.sum_le_sum (s := Finset.univ) fun σ _ => (abs_le.1 (hlog σ)).1
    rwa [Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul, mul_comm] at this
  unfold lineDeg at h0 ⊢
  rw [h1, h2, mul_div_assoc, add_div]
  linarith

theorem exists_twSec_keyRoot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → FnAlgClosed Xo c → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → UnramPts Xo c (badPrimes H l) → Nonempty (KeySec Xo c) ∧ ∀ Z : Comp Xo c, ∃ t : TwSec U x Z (wtOf Dw 0 1), IntOff (badPrimes H l) t.lo ∧ -(((Module.finrank ℚ E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd E)) ≤ t.degLo := by
  intro E _ _ _ H Dw l Xo c r U x hU hx hF hpq hg hun
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := GlobalTheory.T.exists_unit_section_thetaKeyRule_weightFour κ k₁ k₂ k₆ E H Dw l Xo c _ e hpq
  have hσ0 := goodEmb_goodOf c c.F.val.toRingHom
  obtain ⟨⟨ρ, hρmem⟩, hρ⟩ := GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hU _ hσ0) hF hpq hKmem hKval
  have hkr : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  have hval := GlobalTheory.T.theta_key_section_valuation_bounds_different κ hkr E H Dw l Xo c _ e K hpq hg hKmem hKval
  have hC := fun σ : c.F →+* ℂ => GlobalTheory.T.thetaKeySection_norm_complexPoints_eq_two_pi_pow κ k₁ k₂ k₅ E H Dw l Xo c _ e (goodOf c σ) r (U (goodOf c σ)) x K
    (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) (hx _ (goodEmb_goodOf c σ)) ⟨⟨ρ, hρmem⟩⟩ hpq hKmem hKval
  choose C hCpos hClog hCeq using hC
  have hgE := card_frame_index Dw e
  have hsum : ∑ τ : E →+* ℂ, Dw.mult τ = Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) := by
    simp [Fintype.card_sigma]
  have hwt : ∀ (m : ℤ) (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → (wtOf Dw 0 m).1 (τ, i) = -m :=
    wtOf_zero_fst E H Dw
  have hex : exZ Dw (wtOf Dw 0 1) = -keyEx Dw := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · rfl
    · simp only [exZ, keyEx, Pi.neg_apply]
      exact hwt 1 τ i i.2
  have hadd : wtOf Dw 0 1 + wtOf Dw 0 (-1) = 0 := by
    rw [← wtOf_add, add_zero, add_neg_cancel, wtOf_zero]
  refine ⟨⟨⟨ρ, hρmem⟩⟩, fun Z => ?_⟩
  obtain ⟨a, ha, haK⟩ := hρ Z
  have hP : HasPts U Z := hasPts U hpq hg hU Z
  set s : Rul Xo c := idem Z * ((ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) with hs
  set s' : Rul Xo c := idem Z * (ρ : Rul Xo c) with hs'
  have hsm : s ∈ secZ Xo c (exZ Dw (wtOf Dw 0 1)) := by
    have := mul_mem_secZ (idem_mem_secZ Z) (inv_mem_secZ hρmem)
    rwa [zero_add, ← hex] at this
  have hsm' : s' ∈ secZ Xo c (exZ Dw (wtOf Dw 0 (-1))) := by
    have := mul_mem_secZ (idem_mem_secZ Z) hρmem
    have h2 : exZ Dw (wtOf Dw 0 (-1)) = keyEx Dw := by
      have h3 := exZ_add_eq (Dw := Dw) (wtOf Dw 0 1) (wtOf Dw 0 (-1))
      rw [hadd, hex] at h3
      have h4 : exZ Dw (0 : WTZ E) = 0 := by funext i; cases i <;> rfl
      rw [h4] at h3
      exact (neg_add_eq_zero.1 h3.symm).symm
    rwa [zero_add, ← h2] at this
  have hsupp : s ∈ suppOn Z := by rw [hs, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hsupp' : s' ∈ suppOn Z := by rw [hs', mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hnorm := fun σ : c.F →+* ℂ => fun z (hz : z ∈ framesOn (U (goodOf c σ)) Z) =>
    homN_root E H Dw l Xo c (goodOf c σ) r (U (goodOf c σ)) x Z ρ K a (C σ) ha (hCpos σ) haK (hCeq σ) z hz
      ((hP.1 σ).2 z hz)
  have hgood : ∀ σ, GoodEmb c σ → goodOf c σ = σ := fun σ h => if_pos h
  have hmono : ∀ (m : ℤ) (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ →
      (wtOf Dw 0 m).1 (τ, j) ≤ (wtOf Dw 0 m).1 (τ, i) := fun m τ i j hij hj => by
    rw [hwt m τ i (lt_of_le_of_lt hij hj), hwt m τ j hj]
  have hbd : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 1) s z ≤ D := by
    intro σ hσ
    refine ⟨(‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ), fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).1.le
  have hbd' : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 (-1)) s' z ≤ D := by
    intro σ hσ
    refine ⟨(‖σ a‖ * C σ) ^ ((1 / 4) : ℝ), fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).2.le
  let B : HeightOneSpectrum (𝓞 c.F) → ℝ := fun w =>
    ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ)
  have hbnd := fun w (v : Rul Xo c → EReal) (hv : v ∈ valOn Z w) =>
    val_root E H Dw l Xo c Z w v hv ρ K a (B w) ha haK (hval w v (valOn_subset Z w hv)).1
      (hval w v (valOn_subset Z w hv)).2
  let t : TwSec U x Z (wtOf Dw 0 1) :=
    { even := even_wtOf _ _
      sig := s
      inv := s'
      sig_mem := hsm
      inv_mem := by
        have h5 := exZ_neg_eq (Dw := Dw) (wtOf Dw 0 1)
        have h6 : -wtOf Dw 0 1 = wtOf Dw 0 (-1) := neg_eq_of_add_eq_zero_right hadd
        rw [← h5, h6]; exact hsm'
      idem_sig := by rw [hs, ← mul_assoc, idem_mul_idem]
      idem_inv := by rw [hs', ← mul_assoc, idem_mul_idem]
      mul_inv := by rw [hs, hs', mul_mul_mul_comm, idem_mul_idem, Units.inv_mul, mul_one]
      cInf := fun σ => (‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ)
      cInf_pos := fun σ => Real.rpow_pos_of_pos (mul_pos (norm_pos_iff.2 ((map_ne_zero σ).2 ha)) (hCpos σ)) _
      norm_inf := fun σ z hz => by
        rw [(hnorm σ z hz).1, norm_goodOf]
      cusp_sig := fun G hG f hf =>
        GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component E H Dw l Xo c r U x Z (wtOf Dw 0 1) s ⟨⟨ρ, hρmem⟩⟩ hU hpq (even_wtOf _ _) (hmono 1) hsm hsupp hbd G hG f hf
      cusp_inv := fun G hG f hf => by
        have h7 := GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component E H Dw l Xo c r U x Z (wtOf Dw 0 (-1)) s' ⟨⟨ρ, hρmem⟩⟩ hU hpq (even_wtOf _ _) (hmono (-1))
          hsm' hsupp' hbd' (G + wtOf Dw 0 1) (hG.add (even_wtOf _ _)) f hf
        rwa [add_assoc, hadd, add_zero] at h7
      lo := fun w => -(vAdd w a : ℝ) / 4 - B w
      hi := fun w => -(vAdd w a : ℝ) / 4
      lo_le := fun w v hv => (hbnd w v hv).1
      le_hi := fun w v hv => (hbnd w v hv).2
      finite_lo := by
        refine ((finite_vAdd ha).union (Set.finite_iUnion fun τ => finite_ord (embF c τ))).subset fun w hw => ?_
        by_contra hn
        simp only [Set.mem_union, Function.mem_support, Set.mem_iUnion, not_or, not_exists, not_not] at hn
        apply hw
        simp [B, hn.1, hn.2]
      finite_hi := by
        refine (finite_vAdd ha).subset fun w hw => ?_
        by_contra hn
        simp only [Function.mem_support, not_not] at hn
        apply hw
        simp [hn]
      pts := hP }
  refine ⟨t, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv, hint⟩ := hun Z w hw
    have hB : B w = 0 := by
      refine Finset.sum_eq_zero fun τ _ => ?_
      rw [ord_conjDifferent_eq_zero c.F E (embF c τ) w fun p hp hd => hw p (mem_badPrimes.2 ⟨hp, Or.inr (Or.inr (Or.inl hd))⟩)]
      simp
    obtain ⟨h1, h2⟩ := hbnd w v hv
    rw [hB, sub_zero] at h1
    rcases hint s with h | ⟨n, hn⟩
    · rw [h] at h2; exact absurd h2 (by simp)
    · refine ⟨n, ?_⟩
      show -(vAdd w a : ℝ) / 4 - B w = n
      rw [hB, sub_zero]
      rw [hn] at h1 h2
      exact le_antisymm (EReal.coe_le_coe_iff.1 h1) (EReal.coe_le_coe_iff.1 h2)
  · have h8 := le_lineDeg_root c.F E (fun τ => Dw.mult τ) (fun τ => embF c τ) _ a C ha hCpos hClog hsum
    show _ ≤ lineDeg _ _
    rw [hgE]
    exact h8

end GlobalTheory.KeyRootTw

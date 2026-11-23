import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmMultiplierIntegralSeriesAtInertPrimeProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightTwoFormalGroupUnramifiedMultiplierStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormalGroupHeightLeTwoGoodReductionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIntegralHondaLogarithmPairShortWeierstrassStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MaxUnramifiedResidueAlgClosedAndFrobeniusLiftStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHomotheticPeriodPairLatticeStatement
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.FinalOfNRDense
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

noncomputable section
namespace GlobalTheory.HondaCM3

theorem shortW_map {K L : Type} [Field K] [Field L] (φ : K →+* L) (g2 g3 : K) :
    (Formalism.L2.Th1.A.shortW g2 g3).map φ = Formalism.L2.Th1.A.shortW (φ g2) (φ g3) := by
  ext <;> simp [Formalism.L2.Th1.A.shortW, map_div₀, map_neg, map_ofNat]

theorem ltLog_map {K L : Type} [Field K] [Field L] (φ : K →+* L) (l : ℕ) :
    PowerSeries.map φ (ltLog K l) = ltLog L l := by
  ext n
  simp only [coeff_map, ltLog, coeff_mk]
  split_ifs <;> simp [map_inv₀, map_pow, map_natCast]

theorem constantCoeff_ltLog {K : Type} [Field K] (l : ℕ) (hl : 2 ≤ l) :
    constantCoeff (ltLog K l) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, ltLog, coeff_mk, dif_neg]
  rintro ⟨j, hj⟩
  have : 0 < (l ^ 2) ^ j := pow_pos (pow_pos (by omega) 2) j
  omega

theorem map_subst_of {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) (f s : K⟦X⟧)
    (hs : constantCoeff s = 0) :
    PowerSeries.map φ (f.subst s) = (PowerSeries.map φ f).subst (PowerSeries.map φ s) :=
  Formalism.L2.Th1.A.More.map_subst' φ (HasSubst.of_constantCoeff_zero hs) f

theorem norm_natCast_eq_one {K : Type} [NormedField K] [IsUltrametricDist K] (l n : ℕ)
    (hl : ‖(l : K)‖ < 1) (hcop : Nat.Coprime n l) : ‖(n : K)‖ = 1 := by
  have hb := Nat.gcd_eq_gcd_ab n l
  rw [hcop] at hb
  have h1 : (1 : K) = (n : K) * (n.gcdA l : K) + (l : K) * (n.gcdB l : K) := by
    have := congrArg (fun z : ℤ => (z : K)) hb
    push_cast at this
    exact this
  have hle : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n
  refine le_antisymm hle ?_
  by_contra hlt
  push_neg at hlt
  have ha : ‖(n.gcdA l : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K _
  have hb' : ‖(n.gcdB l : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K _
  have e1 : ‖(n : K) * (n.gcdA l : K)‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) ha) hlt
  have e2 : ‖(l : K) * (n.gcdB l : K)‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hb') hl
  have := IsUltrametricDist.norm_add_le_max ((n : K) * (n.gcdA l : K)) ((l : K) * (n.gcdB l : K))
  rw [← h1, norm_one] at this
  exact absurd this (not_le.2 (max_lt e1 e2))

end GlobalTheory.HondaCM3

namespace GlobalTheory.HondaCM3

theorem one_sub_two_omega_sq (d : ℕ) : (1 - 2 * omegaK d) ^ 2 = -(d : ℂ) := by
  have h : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
  rw [omegaK]
  have : (1 : ℂ) - 2 * ((1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2) = -(Complex.I * ((Real.sqrt d : ℝ) : ℂ)) := by
    ring
  rw [this, neg_sq, mul_pow, Complex.I_sq, h]; ring

theorem cm3 : CM3 := by
  intro d L hsq hd hCM l _ hl5 hld hinert ι g2 g3 hG
  have hG' := hG
  obtain ⟨hg2K, hg3K, hg2n, hg3n, hdisc, lam, hlam0, hg2, hg3⟩ := hG
  haveI : CompleteSpace (MaximalUnramifiedExtension l) := Formalism.L2.Th1.D.kurComplete l
  have hl2 : 2 < l := by omega
  obtain ⟨σ, hσ, -⟩ := Formalism.L2.Th1.D.kurFrob l hl2
  obtain ⟨hRes, hUnr⟩ := GlobalTheory.T.maxUnramified_residueAlgClosed_and_frobeniusLift l hl2
  have hU := hUnr σ hσ
  set φ : MaximalUnramifiedExtension l →+* ℂ_[l] := (MaximalUnramifiedExtension l).subtype with hφ
  have hnφ : ∀ x : MaximalUnramifiedExtension l, ‖φ x‖ = ‖x‖ := fun x => rfl
  set a2 : MaximalUnramifiedExtension l := ⟨g2, hg2K⟩ with ha2
  set a3 : MaximalUnramifiedExtension l := ⟨g3, hg3K⟩ with ha3
  have hφa2 : φ a2 = g2 := rfl
  have hφa3 : φ a3 = g3 := rfl
  set f := Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW a2 a3) with hf
  set e := Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW a2 a3) with he
  have hZ := Formalism.L2.Th1.A.zMap (MaximalUnramifiedExtension l) ℂ_[l] φ (Formalism.L2.Th1.A.shortW a2 a3)
  rw [shortW_map, hφa2, hφa3] at hZ
  have hmf : PowerSeries.map φ f = Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3) := hZ.1
  have hme : PowerSeries.map φ e = uSer g2 g3 := by
    rw [hZ.2.1, Formalism.L2.Th1.A.uSerEq ℂ_[l] g2 g3]
  have hf0 : constantCoeff f = 0 := (Formalism.L2.Th1.A.logSpec (MaximalUnramifiedExtension l) _).1

  have hlK : ‖(l : MaximalUnramifiedExtension l)‖ < 1 := hU.2.2.1
  have h2 : ‖(2 : MaximalUnramifiedExtension l)‖ = 1 := by
    have := norm_natCast_eq_one (K := MaximalUnramifiedExtension l) l 2 hlK
      ((Nat.coprime_primes Nat.prime_two (Fact.out)).2 (by omega))
    simpa using this
  have hInt : IntLog f e := GlobalTheory.T.isIntegralHondaLogarithmPair_shortWeierstrass (MaximalUnramifiedExtension l) a2 a3 h2 hg2n hg3n

  obtain ⟨hωK, hσω⟩ := Formalism.L2.Th1.D.sqrtKur d hsq hd l hl5 hinert ι
  set w : MaximalUnramifiedExtension l := ⟨ι (omegaK d), hωK⟩ with hw
  have hσw : σ w = 1 - w := hσω σ hσ w rfl
  have hσσ : σ (σ w) = w := by rw [hσw, map_sub, map_one, hσw]; ring
  have hsq' : (1 - 2 * w) ^ 2 = -((d : ℕ) : MaximalUnramifiedExtension l) := by
    apply (MaximalUnramifiedExtension l).subtype_injective
    have := congrArg ι (one_sub_two_omega_sq d)
    simp only [map_pow, map_sub, map_one, map_mul, map_ofNat, map_neg, map_natCast] at this
    rw [map_pow, map_sub, map_one, map_mul, map_ofNat, map_neg, map_natCast]
    exact this
  have hd1 : ‖((d : ℕ) : MaximalUnramifiedExtension l)‖ = 1 :=
    norm_natCast_eq_one (K := MaximalUnramifiedExtension l) l d hlK
      ((Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hld)))
  have hnorm : ‖σ w - w‖ = 1 := by
    have e1 : σ w - w = 1 - 2 * w := by rw [hσw]; ring
    rw [e1]
    have : ‖1 - 2 * w‖ ^ 2 = 1 := by rw [← norm_pow, hsq', norm_neg, hd1]
    nlinarith [norm_nonneg (1 - 2 * w), sq_nonneg (‖1 - 2 * w‖ - 1)]

  have hCf : ∀ a : MaximalUnramifiedExtension l, constantCoeff (C a * f) = 0 := fun a => by
    rw [map_mul, hf0, mul_zero]
  have hmapMul : ∀ a : MaximalUnramifiedExtension l, PowerSeries.map φ (Formalism.L2.Th1.C.mulBy f e a) =
      Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3)) (uSer g2 g3) (φ a) := by
    intro a
    rw [Formalism.L2.Th1.C.mulBy, Formalism.L2.Th1.C.mulBy, map_subst_of φ e _ (hCf a), hme, map_mul, map_C, hmf]
  have hCoef : CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) := by
    intro n
    have := GlobalTheory.T.cmMultiplierIntegralSeriesAtInertPrime_proof d L hd hCM l hl5 hld hinert ι g2 g3 hG' n
    rw [← hnφ, ← coeff_map, hmapMul]
    exact this

  have hht : ∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy f e (l : MaximalUnramifiedExtension l))‖ = 1 := by
    have hc : ι.symm lam ≠ 0 := by simpa using hlam0
    obtain ⟨L', -, hL2, hL3, -, -⟩ := GlobalTheory.T.exists_homothetic_periodPair_lattice L (ι.symm lam) hc
    have e2 : ι L'.g₂ = g2 := by rw [hL2, map_mul, map_pow, RingEquiv.apply_symm_apply, hg2]
    have e3 : ι L'.g₃ = g3 := by rw [hL3, map_mul, map_pow, RingEquiv.apply_symm_apply, hg3]
    obtain ⟨n, hn, h1⟩ := GlobalTheory.T.formalGroup_height_le_two_good_reduction L' l hl5 ι (by rw [e2]; exact hg2n) (by rw [e3]; exact hg3n)
      (by rw [e2, e3]; exact hdisc)
    refine ⟨n, hn, ?_⟩
    rw [← hnφ, ← coeff_map, hmapMul, map_natCast]
    rw [e2, e3, ← Formalism.L2.Th1.A.uSerEq ℂ_[l] g2 g3] at h1
    exact h1
  obtain ⟨ε, hε1, hεC⟩ := GlobalTheory.T.heightTwo_formalGroup_unramified_multiplier (MaximalUnramifiedExtension l) l σ hU hRes f e hInt w hCoef hσσ hnorm hht
  refine ⟨φ ε, ε.2, hε1, fun n => ?_⟩
  have hs0 : constantCoeff (C ε * ltLog (MaximalUnramifiedExtension l) l) = 0 := by
    rw [map_mul, constantCoeff_ltLog l (by omega), mul_zero]
  have hEq : (uSer g2 g3).subst (C (φ ε) * ltLog ℂ_[l] l) =
      PowerSeries.map φ (e.subst (C ε * ltLog (MaximalUnramifiedExtension l) l)) := by
    rw [map_subst_of φ e _ hs0, hme, map_mul, map_C, ltLog_map]
  rw [hEq, coeff_map]
  exact ⟨(coeff n (e.subst (C ε * ltLog (MaximalUnramifiedExtension l) l))).2, by rw [hnφ]; exact hεC n⟩

end GlobalTheory.HondaCM3

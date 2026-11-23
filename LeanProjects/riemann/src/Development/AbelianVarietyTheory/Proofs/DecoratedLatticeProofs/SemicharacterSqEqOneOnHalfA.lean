import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPEqCP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AlVEmbHEqNegOneZpow
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsConjPlOfIdemSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.AdForm.HalfASign

open GlobalTheory.LatVac

variable {D : D7}

theorem conjP_conjP_self (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ (Formalism.L2.Col.conjPrime₂ P) = P := by
  ext r
  rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]

theorem infPart_es {es : Formalism.L2.DIV.Pl D.host.E → AE D} {PP : Formalism.L2.DIV.Pl D.host.E}
    (h : Formalism.L2.NTheta.IsIdemAt (es PP) PP) : infPart D (es PP) = 0 :=
  GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨es, fun Q hQ => by rw [Finset.mem_singleton.1 hQ]; exact h,
    (Finset.sum_singleton _ _).symm⟩, h.1.2.1⟩

theorem compP_mem : ∀ (D : D7), D.host.ccK = ⊤ → ∀ (S T : HSp D) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → ∀ (c : ℕ), 0 < c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ((LinearMap.toMatrix' ((c : D.host.E) • x')).map fun r => e * incA D r) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D hcc S T e SS hE N N' hN c hc x' hx
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE
  have e1 : ((LinearMap.toMatrix' ((c : D.host.E) • x')).map fun r => (∑ PP ∈ SS, es PP) * incA D r) =
      ∑ PP ∈ SS, ((LinearMap.toMatrix' ((c : D.host.E) • x')).map fun r => cA D (cA D (es PP)) * incA D r) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sum_apply, Finset.sum_mul, Formalism.L2.Theta.cA_cA]
  rw [e1]
  refine sum_mem fun PP hPP => ?_
  have he' : Formalism.L2.NTheta.IsIdemAt (cA D (es PP)) (Formalism.L2.Col.conjPrime₂ PP) :=
    GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun x => Formalism.L2.Col.mem_conjP _ _
  have h0 : infPart D (cA D (es PP)) = 0 := GlobalTheory.PlaceVec.infPart_cA (infPart_es (hes PP hPP))
  have hm := (Submodule.mem_iInf _).1 hx PP
  simp only [Submodule.mem_comap, expS, if_pos hPP] at hm
  have hm' : (c : D.host.E) • x' ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ (Formalism.L2.Col.conjPrime₂ PP)).asIdeal
      (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
    rw [conjP_conjP_self]
    convert hm using 1
    simp
  exact GlobalTheory.AdForm.HalfPairing.conj_comp_mem hcc hN he' h0 hm'

theorem compC_mem : ∀ (D : D7), D.host.ccK = ⊤ → ∀ (S T : HSp D) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → ∀ (c : ℕ), 0 < c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D e * incA D r) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D hcc S T e SS hE N N' hN c hc x' hx
  have hnc := GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum hE
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE
  have e1 : ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D (∑ PP ∈ SS, es PP) * incA D r) =
      ∑ PP ∈ SS, ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D (es PP) * incA D r) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sum_apply, map_sum, Finset.sum_mul]
  rw [e1]
  refine sum_mem fun PP hPP => ?_
  have hnot : Formalism.L2.Col.conjPrime₂ PP ∉ SS := by
    intro h
    refine hnc PP hPP _ h fun a ha => ⟨Formalism.L2.Col.cO D.host.E a, ?_, rfl⟩
    rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]
    exact ha
  have hm := (Submodule.mem_iInf _).1 hx (Formalism.L2.Col.conjPrime₂ PP)
  simp only [Submodule.mem_comap, expS, if_neg hnot, conjP_conjP_self, if_pos hPP] at hm
  have hm' : (c : D.host.E)⁻¹ • x' ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ PP).asIdeal
      (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
    convert hm using 1
    simp
  exact GlobalTheory.AdForm.HalfPairing.conj_comp_mem hcc hN (hes PP hPP) (infPart_es (hes PP hPP)) hm'

theorem map_mul_incA {m n : ℕ} {z : AE D} (hz : infPart D z = 0) (M : Matrix (Fin m) (Fin n) D.host.E) :
    (M.map fun r => z * incA D r) = z • finTens 1 M := by
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, finTens, Matrix.map_apply]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · simp only [RingHom.map_mul, hz, zero_mul]
  · rw [RingHom.map_mul, RingHom.map_mul, finPart_incA, finPart_pair]

set_option maxHeartbeats 1000000 in

theorem symplO_split {S T : HSp D} {e : AE D} (h1 : e * e = e) (h2 : e * cA D e = 0) (u v : WO S T) :
    symplO S T u v = symplO S T (e • u) (cA D e • v) + symplO S T (cA D e • u) (e • v) +
      symplO S T ((1 - e - cA D e) • u) ((1 - e - cA D e) • v) := by
  have h1' : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have h2' : cA D e * e = 0 := by rw [mul_comm, h2]
  have hc : cA D (1 - e - cA D e) = 1 - e - cA D e := by
    rw [map_sub, map_sub, map_one, Formalism.L2.Theta.cA_cA]; ring
  have ho : (1 - e - cA D e) * (1 - e - cA D e) = 1 - e - cA D e := by
    linear_combination h1 + h1' + 2 * h2
  have k1 : hO S T (e • u) (cA D e • v) = e * hO S T u v := by
    rw [GlobalTheory.LatVacSign.hO_smul_smul, Formalism.L2.Theta.cA_cA, h1]
  have k2 : hO S T (cA D e • u) (e • v) = cA D e * hO S T u v := by
    rw [GlobalTheory.LatVacSign.hO_smul_smul, h1']
  have k3 : hO S T ((1 - e - cA D e) • u) ((1 - e - cA D e) • v) = (1 - e - cA D e) * hO S T u v := by
    rw [GlobalTheory.LatVacSign.hO_smul_smul, hc, ho]
  have k : hO S T u v = hO S T (e • u) (cA D e • v) + hO S T (cA D e • u) (e • v) +
      hO S T ((1 - e - cA D e) • u) ((1 - e - cA D e) • v) := by
    have hs : e + cA D e + (1 - e - cA D e) = 1 := by ring
    rw [k1, k2, k3, ← add_mul, ← add_mul, hs, one_mul]
  unfold symplO
  rw [k, mul_add, mul_add, map_add, map_add]

theorem halfA_smul_mem_locP {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c)
    {x : Formalism.L2.Col.HomE E a b} (hx : x ∈ halfAO SS M c) (Q : HeightOneSpectrum (𝓞 E)) :
    (c : E) • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  have h : ((c : E) ^ (-expS SS Q))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hx Q
  have hc' : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have key : ∀ k : ℕ, (c : E) = (c : E) ^ k * ((c : E) ^ (-expS SS Q))⁻¹ →
      (c : E) • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := fun k hk => by
    have := nsmul_mem h (c ^ k)
    rwa [← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← hk] at this
  unfold expS at key
  split_ifs at key
  · exact key 0 (by rw [_root_.zpow_neg, zpow_one, inv_inv, pow_zero, one_mul])
  · exact key 2 (by rw [neg_neg, zpow_one, pow_two, mul_assoc, mul_inv_cancel₀ hc', mul_one])
  · exact key 1 (by rw [neg_zero, zpow_zero, inv_one, pow_one, mul_one])

theorem exists_den {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c)
    {x : Formalism.L2.Col.HomE E a b} (hx : x ∈ halfAO SS M c) :
    ∃ r : 𝓞 E, r ≠ 0 ∧ r • x ∈ M ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), r ∈ Q.asIdeal → Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS := by
  let I : Ideal (𝓞 E) := M.comap (LinearMap.toSpanSingleton (𝓞 E) _ x)
  have hI : ∀ r, r ∈ I ↔ r • x ∈ M := fun r => Iff.rfl
  have hcx : (c : E) • x ∈ M := GlobalTheory.ThetaMove.mem_of_locP fun Q => halfA_smul_mem_locP hc hx Q
  have hcI : (c : 𝓞 E) ∈ I := by
    rw [hI, Nat.cast_smul_eq_nsmul]
    rwa [Nat.cast_smul_eq_nsmul] at hcx
  have h0 : I ≠ 0 := fun h => by
    rw [h] at hcI
    exact (Nat.cast_ne_zero.2 hc.ne' : (c : 𝓞 E) ≠ 0) hcI
  have hm : I ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero h0
  have hpos : 0 < Fintype.card (ClassGroup (𝓞 E)) := Fintype.card_pos
  have h1 : ClassGroup.mk0 ⟨I ^ Fintype.card (ClassGroup (𝓞 E)), pow_mem hm _⟩ = 1 := by
    have : (⟨I ^ Fintype.card (ClassGroup (𝓞 E)), pow_mem hm _⟩ : nonZeroDivisors (Ideal (𝓞 E))) =
      (⟨I, hm⟩ : nonZeroDivisors (Ideal (𝓞 E))) ^ Fintype.card (ClassGroup (𝓞 E)) := rfl
    rw [this, map_pow, pow_card_eq_one]
  obtain ⟨r, hr⟩ := ((ClassGroup.mk0_eq_one_iff (pow_mem hm _)).1 h1).principal
  have hrm : r ∈ I ^ Fintype.card (ClassGroup (𝓞 E)) := by
    rw [hr]; exact Submodule.mem_span_singleton_self r
  refine ⟨r, fun h => pow_ne_zero (Fintype.card (ClassGroup (𝓞 E))) h0 ?_, (hI r).1 (Ideal.pow_le_self hpos.ne' hrm), fun Q hQ => ?_⟩
  · rw [hr, h]; simp
  · have hle : I ≤ Q.asIdeal := by
      refine (Ideal.IsPrime.pow_le_iff hpos.ne').1 ?_
      rw [hr]
      exact (Submodule.span_singleton_le_iff_mem _ _).2 hQ
    by_contra hn
    rw [not_or] at hn
    have h : ((c : E) ^ (-expS SS Q))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hx Q
    unfold expS at h
    rw [if_neg hn.1, if_neg hn.2, neg_zero, zpow_zero, inv_one, one_smul] at h
    obtain ⟨s, hs, hsx⟩ := h
    exact hs (hle ((hI s).2 hsx))

open GlobalTheory.IdemSupport GlobalTheory.OffIdemDen in

theorem off_den_int : ∀ (D : D7) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ c : 𝓞 D.host.E, c ≠ 0 → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), c ∈ Q.asIdeal → Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) → finPart D ((1 - e - cA D e) * incA D ((c : D.host.E))⁻¹) ∈ intAE D := by
  intro D e SS he c hc0 hcQ
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨⟨es, hes, rfl⟩, horth⟩ := he
  have hd : ∀ P ∈ SS, IsDelta Φ P (es P) := fun P hP => delta_of_isIdemAt hΦ (hes P hP)
  have hdc : ∀ P ∈ SS, IsDelta Φ (cP P) (cA D (es P)) := fun P hP => delta_conj hΦ (hd P hP)
  have hE : ∀ Q, Φ (∑ P ∈ SS, es P) Q = ∑ P ∈ SS, Φ (es P) Q := fun Q => map_sum (evQ Φ Q) _ _
  have hC : ∀ Q, Φ (cA D (∑ P ∈ SS, es P)) Q = ∑ P ∈ SS, Φ (cA D (es P)) Q := fun Q => by
    rw [map_sum]; exact map_sum (evQ Φ Q) _ _
  have hO : ∀ Q, Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q =
      1 - Φ (∑ P ∈ SS, es P) Q - Φ (cA D (∑ P ∈ SS, es P)) Q := fun Q => by
    change evQ Φ Q _ = _
    rw [map_sub, map_sub, map_one]; rfl
  have hprod : ∀ Q, Φ (∑ P ∈ SS, es P) Q * Φ (cA D (∑ P ∈ SS, es P)) Q = 0 := fun Q => by
    rw [← ev_mul, horth, ev_zero]
  rw [hΦ.int]
  intro Q
  rw [ev_mul, hΦ.inc]
  by_cases hcq : c ∈ Q.asIdeal
  · have h0 : Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q = 0 := by
      rw [hO]
      rcases hcQ Q hcq with hQ | hQ
      · have h1 : Φ (∑ P ∈ SS, es P) Q = 1 := by
          rw [hE, Finset.sum_eq_single Q (fun P hP hne => (hd P hP).2.2 Q (Ne.symm hne))
            (fun h => absurd hQ h), (hd Q hQ).2.1]
        have h2 := hprod Q
        rw [h1, one_mul] at h2
        rw [h1, h2, sub_self, sub_zero]
      · rw [conjP_eq_cP] at hQ
        have h1 : Φ (cA D (∑ P ∈ SS, es P)) Q = 1 := by
          rw [hC, Finset.sum_eq_single (cP Q) (fun P hP hne => (hdc P hP).2.2 Q (fun h => hne (by
              rw [h, cP_cP])))
            (fun h => absurd hQ h)]
          have := (hdc (cP Q) hQ).2.1
          rwa [cP_cP] at this
        have h2 := hprod Q
        rw [h1, mul_one] at h2
        rw [h1, h2, sub_zero, sub_self]
    rw [h0, zero_mul]
    exact (Q.adicCompletionIntegers D.host.E).zero_mem
  · refine mul_mem ?_ ?_
    · rw [hO, hE, hC]
      refine sub_mem (sub_mem (Q.adicCompletionIntegers D.host.E).one_mem
        (sum_mem fun P hP => delta_mem (hd P hP) Q)) (sum_mem fun P hP => delta_mem (hdc P hP) Q)
    · exact (inv_mem_iff Q hc0).2 hcq

end GlobalTheory.AdForm.HalfASign

namespace GlobalTheory.AdForm.HalfASign

open GlobalTheory.LatVac

set_option maxHeartbeats 4000000 in

theorem char_symplO_halfA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ y' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ψ (symplO S T (finTens 1 (LinearMap.toMatrix' y')) (finTens 1 (LinearMap.toMatrix' x'))) = 1 := by
  intro D ψ θ S T δ sc hP e SS hE h2qd N N' hN hN' c hc hcQ x' hx y' hy
  have hinf : infPart D e = 0 := GlobalTheory.PlaceVec.idemSum_infPart hE
  have hinfc : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA hinf
  have h1 : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self hE
  have h2 : e * cA D e = 0 := hE.2
  have hcE : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have tm : ∀ (a : D.host.E) (z : Formalism.L2.Col.HomE D.host.E S.rank T.rank), LinearMap.toMatrix' (a • z) = a • LinearMap.toMatrix' z :=
    fun a z => LinearEquiv.map_smul _ a z
  have compE : ∀ z : Formalism.L2.Col.HomE D.host.E S.rank T.rank, e • finTens 1 (LinearMap.toMatrix' z) =
      incA D (c : D.host.E)⁻¹ • ((LinearMap.toMatrix' ((c : D.host.E) • z)).map fun r => e * incA D r) := by
    intro z
    rw [← map_mul_incA hinf, tm]
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      map_mul (incA D), mul_left_comm e, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hcE, map_one, one_mul]
  have compC : ∀ z : Formalism.L2.Col.HomE D.host.E S.rank T.rank, cA D e • finTens 1 (LinearMap.toMatrix' z) =
      incA D (c : D.host.E) • ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • z)).map fun r => cA D e * incA D r) := by
    intro z
    rw [← map_mul_incA hinfc, tm]
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      map_mul (incA D), mul_left_comm (cA D e), ← mul_assoc, ← map_mul, mul_inv_cancel₀ hcE, map_one, one_mul]
  have hoe : (1 - e - cA D e) * e = 0 := by
    rw [sub_mul, sub_mul, one_mul, h1, mul_comm (cA D e), h2, sub_self, sub_zero]
  have ho : (1 - e - cA D e) * (1 - e - cA D e) = 1 - e - cA D e := by
    have h1' : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
    linear_combination h1 + h1' + 2 * h2
  have compO : ∀ z ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c,
      (1 - e - cA D e) • finTens 1 (LinearMap.toMatrix' z) ∈
        (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) := by
    intro z hz
    obtain ⟨r, hr0, hrz, hrQ⟩ := exists_den hc hz
    have hrE : (r : D.host.E) ≠ 0 := fun h => hr0 (by exact_mod_cast h)
    have hrz' : (r : D.host.E) • z ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
      rwa [← algebraMap_smul D.host.E] at hrz
    have hB : ((1 - e - cA D e) * incA D ((r : D.host.E))⁻¹) •
        GlobalTheory.LatVac.finTens 1 (LinearMap.toMatrix' ((r : D.host.E) • z)) ∈
        latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True :=
      GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (off_den_int D e SS hE r hr0 hrQ) _
        (GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _)
          (GlobalTheory.AdForm.HalfPairing.toMatrix_mem_latRat hP.cc hN hrz'))
    have e2 : incA D ((r : D.host.E))⁻¹ • finTens 1 (LinearMap.toMatrix' ((r : D.host.E) • z)) =
        finTens 1 (LinearMap.toMatrix' z) := by
      rw [tm]
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul, finTens, finTens, Matrix.map_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
      · rw [RingHom.map_mul, infPart_pair, infPart_pair, mul_zero]
      · rw [RingHom.map_mul, finPart_incA, finPart_pair, finPart_pair, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          inv_mul_cancel_left₀ hrE]
    rwa [mul_smul, e2] at hB
  have sc1 : ∀ u v : WO S T, symplO S T (incA D (c : D.host.E)⁻¹ • u) (incA D (c : D.host.E) • v) = symplO S T u v := by
    intro u v
    rw [GlobalTheory.LatVacSign.symplO_smul_smul, star_natCast, inv_mul_cancel₀ hcE, mul_one]
    rfl
  have sc2 : ∀ u v : WO S T, symplO S T (incA D (c : D.host.E) • u) (incA D (c : D.host.E)⁻¹ • v) = symplO S T u v := by
    intro u v
    rw [GlobalTheory.LatVacSign.symplO_smul_smul, star_inv₀, star_natCast, mul_inv_cancel₀ hcE, mul_one]
    rfl
  have hcc := hP.cc
  rw [symplO_split h1 h2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, compE y', compC x', compC y', compE x', sc1, sc2,
    char_sympl_eq_one hP.std hN hN' (compP_mem D hcc S T e SS hE N N' hN c hc y' hy) (compC_mem D hcc S T e SS hE N N' hN c hc x' hx),
    char_sympl_eq_one hP.std hN hN' (compC_mem D hcc S T e SS hE N N' hN c hc y' hy) (compP_mem D hcc S T e SS hE N N' hN c hc x' hx),
    char_sympl_eq_one hP.std hN hN' (compO y' hy) (compO x' hx), mul_one, mul_one]

theorem alV_mul_self_halfA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, alV D.host.d sc (embH (tauE D) δ x') * alV D.host.d sc (embH (tauE D) δ x') = 1 := by
  intro D ψ θ S T δ sc hP e SS hE h2qd N N' hN hN' c hc hcQ x' hx
  have hy : (Formalism.MainNotions.BoundaryLocalData.w0 D ^ 2) • x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c :=
    Submodule.smul_mem _ _ hx
  have hpair := char_symplO_halfA D ψ θ S T δ sc hP e SS hE h2qd N N' hN hN' c hc hcQ x' hx _ hy
  have htm : LinearMap.toMatrix' ((Formalism.MainNotions.BoundaryLocalData.w0 D ^ 2) • x') =
      ((1 + D.host.sqrtMinusD) / 2) ^ 2 • LinearMap.toMatrix' x' := by
    rw [← algebraMap_smul D.host.E, LinearEquiv.map_smul]
    rfl
  rw [htm, symplO_finTens, hRat_smul, one_mul, one_mul, ← mul_assoc] at hpair
  obtain ⟨n, hn⟩ := (char_rat hP.std _).1 hpair
  have key := GlobalTheory.SemiTrace.alV_embH_eq_neg_one_zpow D ψ θ S T S.rank T.rank rfl rfl δ sc hP x' n (by
    rw [← hn]
    congr 3 <;> ext i j <;> simp)
  rw [key, ← mul_zpow]
  norm_num

end GlobalTheory.AdForm.HalfASign

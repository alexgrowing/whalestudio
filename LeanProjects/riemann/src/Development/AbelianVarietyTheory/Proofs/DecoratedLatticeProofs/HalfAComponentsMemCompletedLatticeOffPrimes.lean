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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPEqCP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDenominatorAvoidingGivenPrimesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffIdempotentMemIdealTwoIntegersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAComp
open GlobalTheory.AdForm.HalfPairing

theorem conjP_not_mem {D : D7} {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e SS)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ SS) : Formalism.L2.Col.conjPrime₂ P ∉ SS := by
  intro hc
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨⟨es, hes, rfl⟩, horth⟩ := he
  rw [GlobalTheory.OffIdemDen.conjP_eq_cP] at hc
  have hd : ∀ P ∈ SS, GlobalTheory.IdemSupport.IsDelta Φ P (es P) := fun P hP =>
    GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (hes P hP)
  have hdc : ∀ P ∈ SS, GlobalTheory.IdemSupport.IsDelta Φ (GlobalTheory.IdemSupport.cP P) (cA D (es P)) := fun P hP =>
    GlobalTheory.IdemSupport.delta_conj hΦ (hd P hP)
  have h1 : Φ (∑ P ∈ SS, es P) (GlobalTheory.IdemSupport.cP P) = 1 := by
    have hE : Φ (∑ P ∈ SS, es P) (GlobalTheory.IdemSupport.cP P) = ∑ P' ∈ SS, Φ (es P') (GlobalTheory.IdemSupport.cP P) :=
      map_sum (GlobalTheory.OffIdemDen.evQ Φ (GlobalTheory.IdemSupport.cP P)) _ _
    rw [hE, Finset.sum_eq_single (GlobalTheory.IdemSupport.cP P) (fun P' hP' hne => (hd P' hP').2.2 _ (fun h => hne h.symm))
      (fun h => absurd hc h), (hd _ hc).2.1]
  have h2 : Φ (cA D (∑ P ∈ SS, es P)) (GlobalTheory.IdemSupport.cP P) = 1 := by
    have hC : Φ (cA D (∑ P ∈ SS, es P)) (GlobalTheory.IdemSupport.cP P) = ∑ P' ∈ SS, Φ (cA D (es P')) (GlobalTheory.IdemSupport.cP P) := by
      rw [map_sum]; exact map_sum (GlobalTheory.OffIdemDen.evQ Φ (GlobalTheory.IdemSupport.cP P)) _ _
    rw [hC, Finset.sum_eq_single P (fun P' hP' hne => (hdc P' hP').2.2 _ (fun h => hne (by
        have := congrArg GlobalTheory.IdemSupport.cP h
        rwa [GlobalTheory.OffIdemDen.cP_cP, GlobalTheory.OffIdemDen.cP_cP, eq_comm] at this)))
      (fun h => absurd hP h), (hdc P hP).2.1]
  have h3 := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) (∑ P ∈ SS, es P) (cA D (∑ P ∈ SS, es P)) (GlobalTheory.IdemSupport.cP P)
  rw [horth, h1, h2, one_mul, GlobalTheory.IdemSupport.ev_zero] at h3
  exact one_ne_zero h3.symm

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

theorem halfA_mem_locP_conj {D : D7} {a b : ℕ} {SS : Finset (HeightOneSpectrum (𝓞 D.host.E))}
    {M : Submodule (𝓞 D.host.E) (Formalism.L2.Col.HomE D.host.E a b)} {c : ℕ} (hc : 0 < c)
    {x : Formalism.L2.Col.HomE D.host.E a b} (hx : x ∈ halfAO SS M c) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ SS)
    (hP' : Formalism.L2.Col.conjPrime₂ P ∉ SS) : x ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ P).asIdeal M := by
  have h : ((c : D.host.E) ^ (-expS SS (Formalism.L2.Col.conjPrime₂ P)))⁻¹ • x ∈
      Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ P).asIdeal M := (Submodule.mem_iInf _).1 hx _
  have hcc : Formalism.L2.Col.conjPrime₂ (Formalism.L2.Col.conjPrime₂ P) = P := by
    rw [GlobalTheory.OffIdemDen.conjP_eq_cP, GlobalTheory.OffIdemDen.conjP_eq_cP, GlobalTheory.OffIdemDen.cP_cP]
  have he : expS SS (Formalism.L2.Col.conjPrime₂ P) = -1 := by
    unfold expS; rw [if_neg hP', if_pos (by rw [hcc]; exact hP)]
  have hc' : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  rw [he, neg_neg, zpow_one] at h
  have := nsmul_mem h c
  rwa [← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hc', one_smul] at this

theorem halfA_mem_locP_off {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ}
    {x : Formalism.L2.Col.HomE E a b} (hx : x ∈ halfAO SS M c) (Q : HeightOneSpectrum (𝓞 E))
    (hQ : ¬ (Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS)) : x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  have h : ((c : E) ^ (-expS SS Q))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hx Q
  have he : expS SS Q = 0 := by
    unfold expS; rw [if_neg (fun h => hQ (Or.inl h)), if_neg (fun h => hQ (Or.inr h))]
  rwa [he, neg_zero, zpow_zero, inv_one, one_smul] at h

set_option maxHeartbeats 1000000 in

theorem zmem : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D ψ θ S T δ sc hP e SS hE h2 N N' hN hN' c hc _ x' hx
  have hA : ((LinearMap.toMatrix' x').map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
    have hE' := hE
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE'
    have e1 : ((LinearMap.toMatrix' x').map fun r => cA D (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
        ∑ PP ∈ SS, ((LinearMap.toMatrix' x').map fun r => cA D (es PP) * incA D r : WO S T) := by
      ext i j
      rw [Matrix.map_apply, Matrix.sum_apply, map_sum, Finset.sum_mul]
      rfl
    rw [e1]
    refine sum_mem fun PP hPP => conj_comp_mem hP.cc hN (hes PP hPP) ?_
      (halfA_mem_locP_conj hc hx hPP (conjP_not_mem hE hPP))
    exact GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨es, fun Q hQ => by
      rw [Finset.mem_singleton.1 hQ]; exact hes PP hPP, (Finset.sum_singleton _ _).symm⟩, (hes PP hPP).1.2.1⟩
  have hcx : ((c : D.host.E) • x') ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' :=
    GlobalTheory.ThetaMove.mem_of_locP fun Q => halfA_smul_mem_locP hc hx Q
  obtain ⟨d, hd0, hdx, hdG⟩ := GlobalTheory.T.exists_denominator_avoiding_given_primes D.host.E _ _ _ (fun Q => Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) c hc x' hcx
    (fun Q hQ => halfA_mem_locP_off hx Q hQ)
  obtain ⟨a₁, a₂, ha₁, ha₂, ho⟩ := GlobalTheory.T.offIdempotent_mem_ideal_two_integers D e SS hE c hc d hd0 hdG
  have hB : a₁ • GlobalTheory.LatVac.finTens 1 (LinearMap.toMatrix' ((c : D.host.E) • x')) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ha₁ _
      (GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) (toMatrix_mem_latRat hP.cc hN hcx))
  have hC : a₂ • GlobalTheory.LatVac.finTens 1 (LinearMap.toMatrix' ((d : D.host.E) • x')) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ha₂ _
      (GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) (toMatrix_mem_latRat hP.cc hN hdx))
  convert add_mem hA (add_mem hB hC) using 1
  have hinf := GlobalTheory.PlaceVec.idemSum_infPart hE
  have hinfc := GlobalTheory.PlaceVec.infPart_cA hinf
  have i1 : ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j,
      infPart D (GlobalTheory.VacUnique.finRat S T M i j) = 0 := fun M i j => by
    have := congrFun (congrFun (GlobalTheory.VacUnique.finRat_inf S T M) i) j
    simpa using this
  have f1 : ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j,
      finPart D (GlobalTheory.VacUnique.finRat S T M i j) = finPart D (incA D (M i j)) := fun M i j => by
    rw [GlobalTheory.LatVacSign.finRat_eq]; rfl
  rw [← GlobalTheory.LatVacSign.finRat_eq, ← GlobalTheory.LatVacSign.finRat_eq]
  ext i j
  rw [Matrix.sub_apply, Matrix.add_apply, Matrix.add_apply, Matrix.map_apply, Matrix.map_apply, Matrix.smul_apply,
    Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · simp only [RingHom.map_sub, RingHom.map_add, RingHom.map_mul, i1, hinf, hinfc,
      mul_zero, zero_mul, sub_zero, add_zero]
  · have hs : ∀ r : D.host.E, LinearMap.toMatrix' (r • x') i j = r * LinearMap.toMatrix' x' i j := fun r => by
      rw [map_smul]; rfl
    have ho' := congrArg (finPart D) ho
    simp only [RingHom.map_sub, RingHom.map_add, RingHom.map_mul, RingHom.map_one] at ho'
    simp only [RingHom.map_sub, RingHom.map_add, RingHom.map_mul, f1, hs]
    linear_combination (finPart D (incA D (LinearMap.toMatrix' x' i j))) * ho'

end GlobalTheory.HalfAComp

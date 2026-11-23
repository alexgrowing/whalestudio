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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfCocycleIsotropicIdempotentHalvesTrivial
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsConjPlOfIdemSum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.CocycleSS
open GlobalTheory.LatVac

variable {D : D7}

theorem natCast_smul_mem_of_halfAO {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c)
    {x : Formalism.L2.Col.HomE E a b} (hx : x ∈ halfAO SS M c) : (c : E) • x ∈ M := by
  refine GlobalTheory.ThetaMove.mem_of_locP fun Q => ?_
  have h : ((c : E) ^ (-expS SS Q))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hx Q
  have hc' : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have key : ∀ k : ℕ, (c : E) = (c : E) ^ k * ((c : E) ^ (-expS SS Q))⁻¹ →
      (c : E) • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := fun k hk => by
    have := nsmul_mem h (c ^ k)
    rwa [← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← hk] at this
  unfold expS at key
  split_ifs at key
  · exact key 0 (by simp)
  · exact key 2 (by rw [neg_neg, zpow_one]; field_simp)
  · exact key 1 (by simp)

theorem conjP_conjP (Q : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ (Formalism.L2.Col.conjPrime₂ Q) = Q := by
  apply HeightOneSpectrum.ext
  ext r
  rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]

theorem conjP_not_mem {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e SS)
    {PP : HeightOneSpectrum (𝓞 D.host.E)} (hPP : PP ∈ SS) : Formalism.L2.Col.conjPrime₂ PP ∉ SS := fun h' =>
  GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum h PP hPP _ h' fun r hr =>
    ⟨Formalism.L2.Col.cO D.host.E r, by rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]; exact hr, rfl⟩

end GlobalTheory.AdForm.CocycleSS

namespace GlobalTheory.AdForm.CocycleSS
open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D}

theorem smul_tmul_fin {a : AE D} (ha : infPart D a = 0) (r : D.host.E) :
    a * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] r) = a * incA D r :=
  GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, RingHom.map_mul, ha, zero_mul, zero_mul])
    (by rw [RingHom.map_mul, RingHom.map_mul]; rfl)

theorem symplOH_smul (a : AE D) (x y : WO S T) : symplOH S T (a • x) y = symplOH S T x (cA D a • y) := by
  rw [symplOH, symplOH, GlobalTheory.SplitScalar.symplO_smul]

theorem lhs_eq {e : AE D} (hinf : infPart D (cA D e) = 0) (hec : e * cA D e = 0)
    (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (X.map fun r => e * incA D r) (GlobalTheory.VacUnique.finRat S T X - X.map fun r => e * incA D r) =
      symplOH S T (X.map (incA D)) (cA D e • X.map (incA D)) := by
  have hXt : (X.map fun r => e * incA D r : WO S T) = e • (X.map (incA D) : WO S T) := by ext i j; rfl
  have hF : cA D e • GlobalTheory.VacUnique.finRat S T X = cA D e • (X.map (incA D) : WO S T) := by
    ext i j; exact smul_tmul_fin hinf _
  rw [hXt, symplOH_smul, smul_sub, hF, smul_smul, mul_comm, hec, zero_smul, sub_zero]

theorem smul_finRat_natCast {e : AE D} (hinf : infPart D e = 0) (c : ℕ) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    e • GlobalTheory.VacUnique.finRat S T ((c : D.host.E) • X) = (e * incA D (c : D.host.E)) • (X.map (incA D) : WO S T) := by
  ext i j
  show e * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] ((c : D.host.E) * X i j)) = (e * incA D (c : D.host.E)) * incA D (X i j)
  rw [smul_tmul_fin hinf, map_mul, mul_assoc]

theorem smul_map_inv {e : AE D} (hcc : cA D e * cA D e = cA D e) (c : ℕ) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    cA D e • (((c : D.host.E)⁻¹ • X).map fun r => cA D e * incA D r : WO S T) =
      (cA D e * incA D ((c : D.host.E)⁻¹)) • (X.map (incA D) : WO S T) := by
  ext i j
  show cA D e * (cA D e * incA D ((c : D.host.E)⁻¹ * X i j)) = (cA D e * incA D ((c : D.host.E)⁻¹)) * incA D (X i j)
  rw [map_mul, ← mul_assoc, hcc, mul_assoc]

theorem cA_incA_natCast (c : ℕ) : cA D (incA D (c : D.host.E)) = incA D (c : D.host.E) := by
  show incA D (star (c : D.host.E)) = _
  rw [star_natCast]

theorem rhs_eq {e : AE D} (hinf : infPart D e = 0) (hcc : cA D e * cA D e = cA D e) {c : ℕ} (hc : 0 < c)
    (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (e • GlobalTheory.VacUnique.finRat S T ((c : D.host.E) • X))
        (cA D e • (((c : D.host.E)⁻¹ • X).map fun r => cA D e * incA D r : WO S T)) =
      symplOH S T (X.map (incA D)) (cA D e • X.map (incA D)) := by
  have hcE : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hs : cA D e * incA D (c : D.host.E) * (cA D e * incA D ((c : D.host.E)⁻¹)) = cA D e := by
    rw [mul_mul_mul_comm, hcc, ← map_mul, mul_inv_cancel₀ hcE, map_one, mul_one]
  rw [smul_finRat_natCast hinf, smul_map_inv hcc, symplOH_smul, smul_smul, RingHom.map_mul, cA_incA_natCast, hs]

theorem finRat_mem {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hcc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {SS : Finset (HeightOneSpectrum (𝓞 D.host.E))} {c : ℕ} (hc : 0 < c)
    {x' : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c) :
    GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' ((c : D.host.E) • x')) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have e1 : GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' ((c : D.host.E) • x')) =
      finTens 1 (LinearMap.toMatrix' ((c : D.host.E) • x')) := by ext i j; rfl
  rw [e1]
  exact finTens_mem_latO (one_mem_intAf _)
    (GlobalTheory.AdForm.HalfPairing.toMatrix_mem_latRat hcc hN (natCast_smul_mem_of_halfAO hc hx))

theorem conjHalf_mem {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hcc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (hE : IsIdemSum e SS)
    {c : ℕ} {x' : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c) :
    ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have hno : ∀ PP ∈ SS, Formalism.L2.Col.conjPrime₂ PP ∉ SS := fun PP hPP => conjP_not_mem hE hPP
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE
  have e1 : ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
      ∑ PP ∈ SS, ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D (es PP) * incA D r : WO S T) := by
    ext i j
    rw [Matrix.map_apply, Matrix.sum_apply, map_sum, Finset.sum_mul]
    rfl
  rw [e1]
  refine sum_mem fun PP hPP => GlobalTheory.AdForm.HalfPairing.conj_comp_mem hcc hN (hes PP hPP) ?_ ?_
  · refine GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨es, fun Q hQ => ?_, (Finset.sum_singleton _ _).symm⟩, (hes PP hPP).1.2.1⟩
    rw [Finset.mem_singleton.1 hQ]
    exact hes PP hPP
  · have h : ((c : D.host.E) ^ (-expS SS (Formalism.L2.Col.conjPrime₂ PP)))⁻¹ • x' ∈
        Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ PP).asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :=
      (Submodule.mem_iInf _).1 hx _
    have hexp : expS SS (Formalism.L2.Col.conjPrime₂ PP) = -1 := by
      unfold expS
      rw [if_neg (hno PP hPP), conjP_conjP, if_pos hPP]
    rw [hexp, neg_neg, zpow_one] at h
    exact h

theorem cocycle_trivial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ψ (symplOH S T ((LinearMap.toMatrix' x').map fun r => e * incA D r) ((GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r))) = 1 := by
  intro D ψ θ S T δ sc hP e SS hE h2 N N' hN hN' c hc _hodd x' hx
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hE
  have hinfc : infPart D (cA D e) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have H := GlobalTheory.HalfCocycle.char_symplOH_idem_conj D ψ θ S T δ sc hP e SS hE h2 N N' hN hN' _ (finRat_mem hP.cc hN hc hx) _
    (conjHalf_mem hP.cc hN hE hx)
  have e1 : ∀ r : D.host.E, (LinearMap.toMatrix' (r • x') : Matrix (Fin T.rank) (Fin S.rank) D.host.E) =
      r • LinearMap.toMatrix' x' := fun r => LinearEquiv.map_smul LinearMap.toMatrix' r x'
  rw [e1, e1, rhs_eq hinf hcc hc] at H
  rw [lhs_eq hinfc hE.2]
  exact H

end GlobalTheory.AdForm.CocycleSS

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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOne
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfMemCompletedHomLatticeIffLocalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFinitePartMemHomLatticeCompletionIff
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HalfAConj
open GlobalTheory.LatVac

theorem conjPl_eq_conjP {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.L2.DIV.conjPl P = Formalism.L2.Col.conjPrime₂ P := by
  apply HeightOneSpectrum.ext
  apply Ideal.ext
  intro r
  show Formalism.L2.DIV.starOHom r ∈ P.asIdeal ↔ Formalism.L2.Col.cO E r ∈ P.asIdeal
  have : Formalism.L2.DIV.starOHom r = Formalism.L2.Col.cO E r := by
    first
      | rfl
      | (apply RingOfIntegers.ext; simp [Formalism.L2.DIV.starOHom, Formalism.L2.DIV.starO_coe, Formalism.L2.Col.cO])
  rw [this]

set_option maxHeartbeats 1000000 in
theorem mem_perO_inf_halfAO : ∀ (D : D7) (S T : HSp D), D.host.ccK = ⊤ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ c : ℕ, 0 < c → ∀ M ∈ GlobalTheory.LatVac.latRat S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)), (∃ w ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True), cA D e • GlobalTheory.LatVac.finTens 1 M = c • w) → Matrix.toLin' M ∈ (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c := by
  intro D S T hcc e SS hE N N' hN hN' c hc M hM hw
  obtain ⟨w, hw, hcw⟩ := hw
  have h1 : Matrix.toLin' M ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
    have := (GlobalTheory.AdForm.RatLat.mem_latRat_iff_perO N' hN M).1 hM
    rwa [GlobalTheory.AdForm.RatLat.AA_eq hcc] at this
  refine Submodule.mem_inf.2 ⟨h1, ?_⟩
  have hcE : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have h0 : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hE)
  have hconj : ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • Matrix.toLin' M)).map fun r => cA D e * incA D r : WO S T) = w := by
    ext i j
    have hij := congrFun (congrFun hcw i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hij
    have e1 : cA D e * finTens 1 M i j = cA D e * incA D (M i j) := by
      refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
      · rw [RingHom.map_mul, RingHom.map_mul, h0, zero_mul, zero_mul]
      · rw [RingHom.map_mul, RingHom.map_mul]
        rfl
    have e2 : LinearMap.toMatrix' ((c : D.host.E)⁻¹ • Matrix.toLin' M) i j = (c : D.host.E)⁻¹ * M i j := by
      have e2' : (c : D.host.E)⁻¹ • Matrix.toLin' M = Matrix.toLin' ((c : D.host.E)⁻¹ • M) :=
        (map_smul Matrix.toLin' _ _).symm
      rw [e2', LinearMap.toMatrix'_toLin']
      rfl
    rw [Matrix.map_apply, e2, RingHom.map_mul, mul_left_comm, ← e1, hij, nsmul_eq_mul, ← mul_assoc]
    have e3 : incA D (c : D.host.E)⁻¹ * (c : AE D) = 1 := by
      rw [← map_natCast (incA D) c, ← RingHom.map_mul, inv_mul_cancel₀ hcE, map_one]
    rw [e3, one_mul]
  have hloc := (GlobalTheory.T.idempotentHalf_mem_completedHomLattice_iff_local D S T hcc (cA D e) _ (Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj hE) N N' hN hN' _).1
    (hconj ▸ hw)
  rw [halfAO, Formalism.L2.Ker.mem_twO]
  intro Q
  by_cases hQ : Q ∈ SS
  · have ex : expS SS Q = 1 := by simp [expS, hQ]
    rw [ex]
    have e4 : (((c : D.host.E) ^ (-(1 : ℤ)))⁻¹) = (c : D.host.E) := by simp
    rw [e4]
    exact Formalism.L2.Ker.le_locP' _ _ (Formalism.L2.Ker.nat_smul_mem _ c h1)
  · by_cases hQ' : Formalism.L2.Col.conjPrime₂ Q ∈ SS
    · have ex : expS SS Q = -1 := by simp [expS, hQ, hQ']
      rw [ex]
      have e4 : (((c : D.host.E) ^ (-(-1 : ℤ)))⁻¹) = (c : D.host.E)⁻¹ := by simp
      rw [e4]
      refine hloc Q (Finset.mem_image.2 ⟨Formalism.L2.Col.conjPrime₂ Q, hQ', ?_⟩)
      rw [conjPl_eq_conjP, Formalism.L2.Ker.conjP_conjP']
    · have ex : expS SS Q = 0 := by simp [expS, hQ, hQ']
      rw [ex]
      simpa using Formalism.L2.Ker.le_locP' _ _ h1

end GlobalTheory.HalfAConj

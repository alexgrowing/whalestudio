import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumConjOfNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomial
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqUnitMulPeriodJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteHeisenbergTranslateSelfDualVacuumFockJets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnLatticeComapEqStandardLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.FinTransJet

theorem inV_stdL_eq_colLat {D : D7} {n : ℕ} (B : GL (Fin n) D.host.E) :
    GlobalTheory.MovedDict.inV B (Formalism.MainNotions.StandardLatticesGL3.stdL D n) = (Formalism.L2.DIV.colLat B : Set (Fin n → D.host.E)) := by
  have hc := GlobalTheory.ColStd.colLat_comap_eq_stdLat B
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ Formalism.L2.Pj.stdLat D.host.E n := hy
    rw [← hc] at hy'
    exact hy'
  · intro hx
    refine ⟨(B⁻¹ : GL (Fin n) D.host.E).1.mulVec x, ?_, ?_⟩
    · show _ ∈ Formalism.L2.Pj.stdLat D.host.E n
      rw [← hc, Submodule.mem_comap]
      simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      rw [show (B.1 * (B⁻¹).1) = 1 from B.mul_inv, Matrix.one_mulVec]
      exact hx
    · simp only [Matrix.mulVec_mulVec]
      rw [show (B.1 * (B⁻¹).1) = 1 from B.mul_inv, Matrix.one_mulVec]

end GlobalTheory.FinTransJet

namespace GlobalTheory.FinTransJet

theorem fock_jets_heisO_fin : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) →
    ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 →
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 →
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    ∀ (δ t0 : ℂ), StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D D.host.ccK δ) t0 →
    ∀ e0 : TaylorLogMetric.VC D S.rank T.rank → ℂ, StandardLatticesGL3.oddE0 D D.host.ccK δ t0 S.rank T.rank e0 →
    ∀ f, IsVacO ψ θ S T sS sT (colLat frS : Set _) (colLat frT : Set _) f → ∀ c : ℂ,
    (∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ)) (fun τ => frT.1.map (tauE D τ)) f
        (MvPolynomial.monomial k 1) 0 = c * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0)) →
    ∀ u : WO S T, u.map (infPart D) = 0 →
    ∃ (m : ℕ) (a : Fin m → ℂ) (s : Fin m → TaylorLogMetric.VC D S.rank T.rank),
      (∀ l, IsAlgebraic ℚ (a l)) ∧ (∀ l, StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D D.host.ccK δ) (StandardLatticesGL3.stdL D S.rank) (StandardLatticesGL3.stdL D T.rank) (s l)) ∧
      ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ)) (fun τ => frT.1.map (tauE D τ))
        (heisO ψ S T u f) (MvPolynomial.monomial k 1) 0 =
        c * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * GL3Theta.applyAt0 D (MvPolynomial.monomial k 1)
          (StandardLatticesGL3.comb D (TaylorLogMetric.tor0 D D.host.ccK δ) a s e0)) := by
  intro _hP _hI D ψ θ S T sS sT frS frT hS hT hcS hcT δ t0 _hC hδ _ht0 e0 he0 f hf c hjets u hu
  have hlS : Submodule.IsLattice D.host.E (Formalism.L2.DIV.colLat frS) := GlobalTheory.FunObj.VecEx.isLattice_colLat frS
  have hlT : Submodule.IsLattice D.host.E (Formalism.L2.DIV.colLat frT) := GlobalTheory.FunObj.VecEx.isLattice_colLat frT
  obtain ⟨n, hn, hnu⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hlS hlT u hu
  rw [← inV_stdL_eq_colLat frS, ← inV_stdL_eq_colLat frT] at hf hnu
  have he0d : Differentiable ℂ e0 := he0.1.1
  obtain ⟨ζ, s, ⟨m, hm, hζ⟩, hs, hk⟩ := GlobalTheory.HeisTrans.core ψ θ S T sS sT frS frT hS hT hcS hcT
    (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank) (GlobalTheory.NormSum.VacInt.sd_std D S.rank)
    (GlobalTheory.NormSum.VacInt.sd_std D T.rank) δ hδ e0 he0d c f hf hjets n hn u hnu
  have hζalg : IsAlgebraic ℚ ζ := by
    have hint : IsIntegral ℚ ζ := ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', by simp [hζ]⟩
    exact hint.isAlgebraic
  refine ⟨1, ![ζ], ![s], fun l => ?_, fun l => ?_, fun k => ?_⟩
  · fin_cases l; exact hζalg
  · fin_cases l; exact ⟨n, hn, hs⟩
  · refine Eq.trans (hk k) ?_
    congr 3
    funext z
    simp [Formalism.MainNotions.StandardLatticesGL3.comb]

end GlobalTheory.FinTransJet

import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSource
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorWeilOperatorCartan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockRealVec

theorem compAt_central {D : D7} {θ : InfFam D} (τ : D.what₂.Tau) {n : ℕ} (c : AE D) :
    ∃ s : ℂ, compAt θ τ (c • (1 : Matrix (Fin n) (Fin n) (AE D))) = s • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  refine ⟨θ τ (infPart D c), ?_⟩
  ext i j
  by_cases h : i = j
  · subst h; simp [compAt]
  · simp [compAt, h]

theorem vec_theta_fock : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} {N : GlobalTheory.FunObj.Std G U} (Z : GlobalTheory.FunObj.Normal W N) {t : T} {p : GlobalTheory.ChiGrid.Pair T}, GlobalTheory.FunObj.DefPair D.R.m p → ∀ d : GlobalTheory.FunObj.FinDatum G t p, Z.HasVec d → IsThetaFunO W.ψ (G.pS p) (G.pT p) (Z.vec d) ∧ ∀ τ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ τ (cplxO (G.cartS W.cart p τ) (G.onT W.cart p τ)) (Z.vec d) := by
  intro D T L sc G W U N Z t p hp d hv
  obtain ⟨f, hf⟩ := hv
  have hvac := Z.vac_is p hp
  have hψ := hvac.1
  have hV := hvac.2
  have hθ : IsInfFam W.θ := hV.inf
  have hf0 := hV.theta
  have hft : IsThetaFunO W.ψ (G.pS p) (G.pT p) f := GlobalTheory.GalLift.Vec.theta_of_thetaAt hψ hθ hf hf0
  have he : infPart D d.e = 0 := GlobalTheory.PlaceVec.idemSum_infPart d.e_is
  have hfock : ∀ τ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ τ
      (cplxO (G.cartS W.cart p τ) (G.onT W.cart p τ)) f := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ he (GlobalTheory.PlaceVec.infPart_cA he) hf hf0 hft (hV.fock τ)
  have hr : Pair.InRange D.R.m p := by
    have := (DefPair.nodes hp).2
    unfold Pair.InRange
    revert this
    cases p.big <;> simp [DefNode, Node.InRange] <;> omega
  have hW := W.om_is p hr
  have hvec : Z.vec d = W.om p (d.z, 1) f := FinDatum.vec_eq W hf
  rw [hvec]
  refine ⟨hW.om_pres _ _ hft, fun τ z => ?_⟩
  obtain ⟨c, hc⟩ := d.z_cen
  obtain ⟨s, hs⟩ := compAt_central (θ := W.θ) τ (n := (G.pS p).rank) c
  have hS : G.cartS W.cart p τ * compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) d.z) =
      compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) d.z) * G.cartS W.cart p τ := by
    rw [hc, hs, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have hc1 : Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p)) = (1 : AE D) • (1 : Matrix _ _ (AE D)) := by
    simp [Formalism.L2.Theta.mt]
  obtain ⟨s', hs'⟩ := compAt_central (θ := W.θ) τ (n := (G.pT p).rank) (1 : AE D)
  have hT : G.onT W.cart p τ * compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p))) =
      compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p))) * G.onT W.cart p τ := by
    rw [hc1, hs', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  obtain ⟨z₀, rfl⟩ : ∃ z₀ : Matrix (Fin (G.pT p).rank) (Fin (G.pS p).rank) ℂ,
      z = compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p))) * z₀ *
        compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) d.z⁻¹) := by
    refine ⟨compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p))⁻¹) * z *
      compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) d.z), ?_⟩
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.mul_one]
  have h0 := congrArg (W.om p (d.z, 1)) (hfock τ z₀)
  rw [GlobalTheory.FockMove.om_annih hW hθ d.z 1 τ hS hT z₀ hft, map_zero] at h0
  exact h0

end GlobalTheory.FockRealVec

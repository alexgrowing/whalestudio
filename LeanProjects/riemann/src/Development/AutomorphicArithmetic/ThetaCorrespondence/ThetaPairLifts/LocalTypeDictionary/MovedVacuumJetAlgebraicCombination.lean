import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierIndexRationalPairValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierIndexRationalPairValueStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.MovedJet
open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial
end GlobalTheory.MovedJet
namespace GlobalTheory.MovedJet
open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial
end GlobalTheory.MovedJet
namespace GlobalTheory.MovedJet
open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial
theorem jet_moved_vacuum_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∀ k : FVar D WW.rank A.rank →₀ ℕ, ∃ (n : ℕ) (c : Fin n → ℂ) (k' : Fin n → FVar D WW.rank A.rank →₀ ℕ),
        (∀ p, IsAlgebraic ℚ (c p)) ∧ (∀ p, Finsupp.mapDomain Prod.fst (k' p) = Finsupp.mapDomain Prod.fst k) ∧
        pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 = ∑ p, c p * pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.vac) (MvPolynomial.monomial (k' p) 1) 0 := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t γ hγ a _ γ' hγ' a' _ _ _ k
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hom := hI.weil t
  set u : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A γ) with hu
  set hm : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ :=
    fun τ => (compAt W.θ τ (Formalism.L2.Theta.mt WW γ')).map (starRingEnd ℂ) with hhm
  set H : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ := fun τ => Matrix.conjTranspose (hm τ) with hH
  set U : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => Matrix.conjTranspose (u τ) with hU
  set Q := GlobalTheory.CompactHowe.substF H U (MvPolynomial.monomial k 1) with hQdef
  have hHm : hm * H = fun _ => 1 := funext fun τ =>
    map_conj_mul_conjT (mul_conjT_of_unitary (conjT_mul_compAt hθ hX.stdW.1 γ' τ))
  have hUm : u * U = fun _ => 1 := funext fun τ => mul_conjT_of_unitary (conjT_mul_compAt hθ hX.std.1 γ τ)
  have hQ : GlobalTheory.CompactHowe.substF hm u Q = MvPolynomial.monomial k 1 := by
    rw [hQdef, GlobalTheory.CompactHowe.substF_mul, hHm, hUm, substF_one]
  have hact := om_pureTensorO_vac hX t γ γ' Q
  have hjet : pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac)
        (MvPolynomial.monomial k 1) 0 =
      pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac Q 0 := by
    rw [← hQ]
    change pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
      ((X.ω t).toSgn true ((ofSgn true A).symm γ, γ') X.vac) _ 0 = _
    rw [← hact.2]
    exact hom.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) γ' hγ' _ hact.1
  have hHalg : ∀ τ a b, IsAlgebraic ℚ (H τ a b) := by
    intro τ a b
    have e : H τ a b = compAt W.θ τ (Formalism.L2.Theta.mt WW γ') b a := by
      simp [hH, hhm, Matrix.conjTranspose_apply]
    rw [e]
    exact isAlgebraic_compAt_of_mem_GQ hθ hγ' τ b a
  have hUalg : ∀ τ a b, IsAlgebraic ℚ (U τ a b) := by
    intro τ a b
    have e : U τ a b = starRingEnd ℂ (compAt W.θ τ (Formalism.L2.Theta.mt A γ) b a) := by
      simp [hU, hu, Matrix.conjTranspose_apply]
    rw [e]
    exact isAlgebraic_conj (isAlgebraic_compAt_of_mem_GQ hθ hγ τ b a)
  let e := Q.support.equivFin
  refine ⟨Q.support.card, fun p => MvPolynomial.coeff (e.symm p).1 Q, fun p => (e.symm p).1, fun p => ?_, fun p => ?_, ?_⟩
  · exact (GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic k (e.symm p).1).2 H U hHalg hUalg
  · exact GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero H U k (e.symm p).1
      (MvPolynomial.mem_support_iff.1 (e.symm p).2)
  · rw [hjet]
    calc pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac Q 0
        = ∑ x ∈ Q.support, MvPolynomial.coeff x Q *
            pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac (MvPolynomial.monomial x 1) 0 := by
          conv_lhs => rw [Q.as_sum]
          rw [map_sum, Finset.sum_apply]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [show MvPolynomial.monomial x (MvPolynomial.coeff x Q) = MvPolynomial.coeff x Q • MvPolynomial.monomial x 1 by
            rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, Pi.smul_apply, smul_eq_mul]
      _ = _ := by
          rw [← Finset.sum_coe_sort]
          exact (Equiv.sum_comp e.symm (fun x : Q.support => MvPolynomial.coeff x.1 Q *
            pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac (MvPolynomial.monomial x.1 1) 0)).symm
end GlobalTheory.MovedJet
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moved_vacuum_jet_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∀ k : FVar D WW.rank A.rank →₀ ℕ, ∃ (n : ℕ) (c : Fin n → ℂ) (k' : Fin n → FVar D WW.rank A.rank →₀ ℕ),
        (∀ p, IsAlgebraic ℚ (c p)) ∧ (∀ p, Finsupp.mapDomain Prod.fst (k' p) = Finsupp.mapDomain Prod.fst k) ∧
        pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 = ∑ p, c p * pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.vac) (MvPolynomial.monomial (k' p) 1) 0 := by
  first | exact @_root_.GlobalTheory.MovedJet.jet_moved_vacuum_algebraic | exact _root_.GlobalTheory.MovedJet.jet_moved_vacuum_algebraic | (intros; apply _root_.GlobalTheory.MovedJet.jet_moved_vacuum_algebraic <;> assumption)
end

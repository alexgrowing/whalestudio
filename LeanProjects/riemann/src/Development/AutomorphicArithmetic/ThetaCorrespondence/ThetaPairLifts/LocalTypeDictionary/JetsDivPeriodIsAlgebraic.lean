import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicFixedDegree
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FockJetsHeisenbergOrbitFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicFixedDegreeStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.BotTransJet
open GlobalTheory.Grid (neg)
end GlobalTheory.BotTransJet
namespace GlobalTheory.BotTransJet
open GlobalTheory.Grid (neg)
theorem isAlgebraic_pureTensorO_div_period : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ dg : D.what₂.Tau →₀ ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ u : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 →
      ∀ k : FVar D WW.rank A.rank →₀ ℕ, Finsupp.mapDomain Prod.fst k = dg →
        IsAlgebraic ℚ (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
          (heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX dg
  classical
  have hIs := hX.is
  have hψ : IsStdChar D W.ψ (-1) := hIs.isVac.1
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  set f : WO A WW → ℂ := fun w => starRingEnd ℂ (X.vac w) with hfdef
  have hf0 : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s X.rA.Λ X.rW.Λ f :=
    GlobalTheory.VacConj.isVacO_conj_negSp W.ψ W.θ A WW X.rA.s X.rW.s _ _ X.vac hIs.isVac
  have hf : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s (colLat (1 : GL (Fin A.rank) D.host.E) : Set _)
      (colLat (1 : GL (Fin WW.rank) D.host.E) : Set _) f := by
    rw [← std_eq_colLat_one X.rA.Λ hX.std.2.1, ← std_eq_colLat_one X.rW.Λ hX.stdW.2.1]
    exact hf0
  have hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin A.rank) D.host.E).1 * A.gram *
      (1 : GL (Fin A.rank) D.host.E).1 = 1 := by
    rw [hX.std.1]
    simp [Formalism.UG.cT]
  have hW : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin WW.rank) D.host.E).1 * WW.gram *
      (1 : GL (Fin WW.rank) D.host.E).1 = 1 := by
    rw [hX.stdW.1]
    simp [Formalism.UG.cT]
  have hcA : ∀ τ, IsCartanInv (gramAt D A τ) (X.rA.s τ) := fun τ => (hIs.rigA.2.2 τ).1
  have hcW : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hIs.rigW.2.2 τ).1
  have hBA : (fun τ => (1 : GL (Fin A.rank) D.host.E).1.map (tauE D τ)) = X.rA.B := by
    funext τ
    rw [(hX.std.2.2 τ).2]
    simp
  have hBW : (fun τ => (1 : GL (Fin WW.rank) D.host.E).1.map (tauE D τ)) = X.rW.B := by
    funext τ
    rw [(hX.stdW.2.2 τ).2]
    simp
  obtain ⟨δ, hC, hδ⟩ := GlobalTheory.FunObj.exists_delta D
  obtain ⟨t0, ht0⟩ := ((hI D).t0Ex D.host.ccK δ hC).1
  have hev : Even (A.rank * WW.rank) := even_bot hX
  obtain ⟨e0, he0, -⟩ := GlobalTheory.Vacuum.exists_vacuum D D.host.ccK δ hC t0 ht0 A.rank WW.rank hev
  obtain ⟨c, hc⟩ := GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets W.ψ W.θ A WW X.rA.s X.rW.s 1 1 hS hW hcA hcW δ t0 hC hδ
    ht0 e0 he0 f hf
  have hΩ : starRingEnd ℂ ((c : ℂ) * dg.prod fun τ n => GlobalTheory.FunObj.period δ τ ^ n) ≠ 0 :=
    (map_ne_zero _).2 (mul_ne_zero c.ne_zero (Finsupp.prod_ne_zero_iff.2 fun τ _ =>
      pow_ne_zero _ (GlobalTheory.FunObj.period_ne_zero hδ τ)))
  refine ⟨_, hΩ, fun u hu k hk => ?_⟩
  obtain ⟨m, a, s, ha, hs, hjet⟩ := _root_.GlobalTheory.T.finite_translate_jets_fock hP hI W.ψ W.θ A WW X.rA.s X.rW.s 1 1 hS hW hcA hcW δ t0 hC hδ ht0 e0 he0 f hf
    c (fun k => hc k) u hu
  have hconj := jet_negSp_heis W.ψ W.θ hψ hθ A WW X.rA.s X.rW.s X.rA.B X.rW.B X.vac u k
  have hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) = dg.prod fun τ n => GlobalTheory.FunObj.period δ τ ^ n := by
    rw [← hk, Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  have hcoef : TaylorLogMetric.CoefIn D (StandardLatticesGL3.comb D (TaylorLogMetric.tor0 D D.host.ccK δ) a s e0) TaylorLogMetric.Qbar :=
    ((hI D).alg D.host.ccK δ hC t0 ht0 A.rank WW.rank (StandardLatticesGL3.stdL D A.rank) (StandardLatticesGL3.stdL D WW.rank)
      (GlobalTheory.MovedVacuum.sd_stdL D _) (GlobalTheory.MovedVacuum.sd_stdL D _) hev e0 he0.2.2.2.1).2.2.1 m a s
      (fun l => (mem_algebraicClosure_iff).2 (ha l)) hs
  have hY : IsAlgebraic ℚ (GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) (StandardLatticesGL3.comb D (TaylorLogMetric.tor0 D D.host.ccK δ) a s e0)) := by
    refine applyAt0_isAlgebraic (fun α => ?_) hcoef
    rw [MvPolynomial.coeff_monomial]
    split_ifs
    · exact isAlgebraic_one
    · exact isAlgebraic_zero
  change IsAlgebraic ℚ (pureTensorO W.ψ W.θ (negSp A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (heisO W.ψ (negSp A) WW u X.vac)
    (MvPolynomial.monomial k 1) 0 / _)
  rw [hconj, ← hBA, ← hBW, hjet k, hprod, show ∀ x y z : ℂ, x * (y * z) = (x * y) * z from fun _ _ _ => (mul_assoc _ _ _).symm,
    map_mul, mul_div_cancel_left₀ _ hΩ]
  exact conj_isAlgebraic hY
end GlobalTheory.BotTransJet
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
theorem _root_.GlobalTheory.T.bottom_translate_jets_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ dg : D.what₂.Tau →₀ ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ u : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 →
      ∀ k : FVar D WW.rank A.rank →₀ ℕ, Finsupp.mapDomain Prod.fst k = dg →
        IsAlgebraic ℚ (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
          (heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
  first | exact @_root_.GlobalTheory.BotTransJet.isAlgebraic_pureTensorO_div_period | exact _root_.GlobalTheory.BotTransJet.isAlgebraic_pureTensorO_div_period | (intros; apply _root_.GlobalTheory.BotTransJet.isAlgebraic_pureTensorO_div_period <;> assumption)
end

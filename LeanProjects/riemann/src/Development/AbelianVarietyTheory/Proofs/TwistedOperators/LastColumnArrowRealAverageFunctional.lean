import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerMovedVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockFrameChangeLastColumnDefinitePairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactPairRealAverageFockEqJetOperatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open GlobalTheory.FockReal MvPolynomial
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.LastColAvg

theorem exps_chi : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ0 : T}, L.Is μ0 → ∀ (i : ℕ), i < D.R.m →
    ∃ (a b : D.what₂.Tau → ℚ) (e₁ e₂ : D.what₂.Tau → ℤ),
      (∀ τ, HasInfExp D (G.chrS (.chi i D.R.m : Pair T)) τ (a τ)) ∧ (∀ τ, HasInfExp D (G.chrT (.chi i D.R.m : Pair T)) τ (b τ)) ∧
      (∀ τ, (e₁ τ : ℚ) = a τ + sgnP (.chi i D.R.m : Pair T) * (G.pS (.chi i D.R.m : Pair T)).rank / 2) ∧
      (∀ τ, (e₂ τ : ℚ) = -(b τ + sgnP (.chi i D.R.m : Pair T) * (G.pT (.chi i D.R.m : Pair T)).rank / 2)) := by
  intro D T L sc G μ0 hL i hi
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have h0 : ∀ τ, HasInfExp D (G.ch.chi (D.R.m - i)) τ (cen D sc.cGap τ (D.R.m - i) : ℚ) := fun τ =>
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ)) (G.ch.chi_eq _ hm1 hm2)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - i), fun τ => by push_cast; ring, G.ch.inf _ hm1 hm2⟩ τ
  have hatt : ∀ (n : ℕ) τ, HasInfExp D (Formalism.IndefR.Lift.attChr (G.ch.chi (D.R.m - i)) L.eta n) τ
      ((cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd n then 1 / 2 else 0) := by
    intro n τ
    unfold Formalism.IndefR.Lift.attChr
    split_ifs
    · rw [sub_eq_add_neg]
      exact GlobalTheory.Chain.StepVac.hasInfExp_mul (h0 τ) (GlobalTheory.Chain.StepVac.hasInfExp_inv (GlobalTheory.SquareExps.eta_exp hL τ))
    · simpa using h0 τ
  refine ⟨fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd (G.pS (.chi i D.R.m : Pair T)).rank then 1 / 2 else 0,
    fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd (G.pT (.chi i D.R.m : Pair T)).rank then 1 / 2 else 0,
    fun τ => (cen D sc.cGap τ (D.R.m - i) : ℤ) - (((G.pS (.chi i D.R.m : Pair T)).rank + 1) / 2 : ℕ),
    fun τ => ((((G.pT (.chi i D.R.m : Pair T)).rank + 1) / 2 : ℕ) : ℤ) - (cen D sc.cGap τ (D.R.m - i) : ℤ),
    fun τ => hatt _ τ, fun τ => hatt _ τ, fun τ => ?_, fun τ => ?_⟩
  · simp only [sgnP]
    rcases Nat.even_or_odd (G.pS (.chi i D.R.m : Pair T)).rank with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [if_neg (Nat.not_odd_iff_even.2 ⟨k, hk⟩), hk, show (k + k + 1) / 2 = k by omega]
      push_cast; ring
    · rw [if_pos ⟨k, hk⟩, hk, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
      push_cast; ring
  · simp only [sgnP]
    rcases Nat.even_or_odd (G.pT (.chi i D.R.m : Pair T)).rank with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [if_neg (Nat.not_odd_iff_even.2 ⟨k, hk⟩), hk, show (k + k + 1) / 2 = k by omega]
      push_cast; ring
    · rw [if_pos ⟨k, hk⟩, hk, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
      push_cast; ring

theorem ker_fock_moved_fin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T},
    L.Is μ0 → ∀ (i : ℕ), i < D.R.m → ∀ (t : T), t ∈ U → ∀ (d : FinDatum G t (.chi i D.R.m)), S.Z.HasVec d →
    ∀ (P : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank) (x : GA D (G.V (.grid i D.R.m))) (y : GA D (G.V (.grid (i + 1) D.R.m))),
    W.ker (.chi i D.R.m) (W.fock (.chi i D.R.m) (movedVec t S d) P) x y =
      W.ker (.chi i D.R.m) (W.fock (.chi i D.R.m) (S.Z.vec d) P) (x * (S.N.u (.grid i D.R.m)).1) (y * (S.N.u (.grid (i + 1) D.R.m)).1) := by
  intro D T L sc G W U S μ0 hL i hi t ht d hd P x y
  have hp : DefPair D.R.m (.chi i D.R.m : Pair T) := ⟨hi, rfl⟩
  have hn := DefPair.nodes hp
  have hom := W.om_is (.chi i D.R.m) (by
    simp only [DefPair, DefNode] at hp hn; simp only [Pair.InRange, Node.InRange]; omega)
  obtain ⟨h1, -⟩ := GlobalTheory.T.gridFiniteDatumVector_theta_fockVacuum W S.Z hp d hd
  have m1 : (G.toPair (.chi i D.R.m) (S.N.u (.grid i D.R.m)).1 (S.N.u (.grid (i + 1) D.R.m)).1).1 ∈
      GfC (G.pS (.chi i D.R.m : Pair T)) := negGA_mem_GfC _ (S.N.u _).2
  have m2 : (G.toPair (.chi i D.R.m) (S.N.u (.grid i D.R.m)).1 (S.N.u (.grid (i + 1) D.R.m)).1).2 ∈
      GfC (G.pT (.chi i D.R.m : Pair T)) := (S.N.u _).2
  have e : W.fock (.chi i D.R.m) (movedVec t S d) P =
      W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (S.N.u (.grid i D.R.m)).1 (S.N.u (.grid (i + 1) D.R.m)).1)
        (W.fock (.chi i D.R.m) (S.Z.vec d) P) :=
    (GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ _ hom W.θ W.θ_is _ m1 _ m2 _ _ _ _ (S.Z.vec d) P h1).symm
  rw [e]
  unfold GridData.Weil.ker
  rw [GlobalTheory.RowClaim.toPair_mul]
  simp only [thetaKO, Prod.mk.eta, map_mul, Module.End.mul_apply]

theorem real_average : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (i : ℕ), i < D.R.m →
    ∀ (Q : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank)
      (Λ : Module.Dual ℂ (VV ℂ (wt G (.grid i D.R.m)))),
    ∃ Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid (i + 1) D.R.m))), ∀ t ∈ U, ∀ d : FinDatum G t (.chi i D.R.m), S.Z.HasVec d →
      ∀ κ : Measure (GinfC (G.V (.grid i D.R.m))), κ.IsHaarMeasure → IsProbabilityMeasure κ →
      ∀ (x : FinPt G (.grid i D.R.m)) (h : GA D (G.V (.grid (i + 1) D.R.m))) (v : VV ℂ (wt G (.grid i D.R.m))),
        ∫ k, W.kerA (.right i D.R.m : Arrow T) (W.fock (.chi i D.R.m) (movedVec t S d) Q)
            ((x : GA D (G.V (.grid i D.R.m))) * (k : GA D (G.V (.grid i D.R.m)))) h *
            Λ (realAct W.θ S.N.fr (.grid i D.R.m) ((k : GA D (G.V (.grid i D.R.m)))⁻¹) v) ∂κ =
          Λ' (realAct W.θ S.N.fr (.grid (i + 1) D.R.m) h⁻¹
            (fockComp W S.N.frC (.chi i D.R.m : Pair T) (S.Z.vec d) (x * S.N.u _) (finOf _ h * S.N.u _) v)) := by
  intro D T L sc G W U S μ0 hL i hi Q Λ
  obtain ⟨a, b, e₁, e₂, ha, hb, he₁, he₂⟩ := exps_chi G hL i hi
  obtain ⟨σ₀, hσf, hσr⟩ := GlobalTheory.T.exists_fockFrameChange_lastColumn_definitePair S hL i hi
  obtain ⟨Λ', hΛ'⟩ := GlobalTheory.T.compactPair_realAverage_fock_eq_jetOperator S hL i hi a b ha hb e₁ e₂ he₁ he₂ (σ₀ Q) Λ
  refine ⟨Λ', fun t ht d hd κ hκ hκp x h v => ?_⟩
  have hp : DefPair D.R.m (.chi i D.R.m : Pair T) := ⟨hi, rfl⟩
  have hh : h = ((finOf _ h : GfC (G.V (.grid (i + 1) D.R.m))) : GA D (G.V (.grid (i + 1) D.R.m))) *
      ((infOf _ h : GinfC (G.V (.grid (i + 1) D.R.m))) : GA D (G.V (.grid (i + 1) D.R.m))) := by
    rw [← GlobalTheory.AdelicSplit.commute_GinfC_GfC _ (infOf _ h).2 (finOf _ h).2, infOf_mul_finOf]
  let ℓ : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →ₗ[ℂ] ℂ :=
    ((LinearMap.proj 0 : (WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
      W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) ((x * S.N.u _ : FinPt G (.grid i D.R.m)) : GA D (G.V (.grid i D.R.m)))
        ((finOf _ h * S.N.u _ : FinPt G (.grid (i + 1) D.R.m)) : GA D (G.V (.grid (i + 1) D.R.m))))) ∘ₗ
      fockIn W S.N.frC (.chi i D.R.m) (S.Z.vec d)
  have key : ∀ k : GinfC (G.V (.grid i D.R.m)),
      W.kerA (.right i D.R.m : Arrow T) (W.fock (.chi i D.R.m) (movedVec t S d) Q)
        ((x : GA D (G.V (.grid i D.R.m))) * (k : GA D (G.V (.grid i D.R.m)))) h =
      realChar W (.chi i D.R.m) e₁ e₂ (k : GA D (G.V (.grid i D.R.m))) (infOf _ h : GA D (G.V (.grid (i + 1) D.R.m))) *
        ℓ (realSubst W S.N.frC (.chi i D.R.m) (k : GA D (G.V (.grid i D.R.m))) (infOf _ h : GA D (G.V (.grid (i + 1) D.R.m))) (σ₀ Q)) := by
    intro k
    show W.ker (.chi i D.R.m) (W.fock (.chi i D.R.m) (movedVec t S d) Q) _ _ = _
    conv_lhs => rw [hh]
    rw [ker_fock_moved_real hL W S t hp d hd a b ha hb e₁ e₂ he₁ he₂ _ k.2 _ (infOf _ h).2 Q _ _,
      ker_fock_moved_fin S hL i hi t ht d hd, hσf t ht d hd, hσr _ k.2 _ (infOf _ h).2]
    rfl
  simp_rw [key]
  rw [hΛ' ℓ κ hκ hκp _ (infOf _ h).2 v]
  have hY : realAct W.θ S.N.fr (.grid (i + 1) D.R.m) h⁻¹ =
      realAct W.θ S.N.fr (.grid (i + 1) D.R.m) ((infOf _ h : GA D (G.V (.grid (i + 1) D.R.m))))⁻¹ := by
    conv_lhs => rw [hh]
    rw [mul_inv_rev, map_mul, realAct_fin _ _ _ (inv_mem (finOf _ h).2), mul_one]
  rw [hY]
  rfl

end GlobalTheory.LastColAvg

end

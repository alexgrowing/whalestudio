import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.JetDeg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem jetOp_mul_tab' {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a)
    (lam' : ι → DomWeight b) (c : K) (J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) :
    Formalism.L2.Ker.jetOp lam lam' (fun k => c * J k) n = c • Formalism.L2.Ker.jetOp lam lam' J n := by
  have e : Formalism.L2.Ker.jetLin (fun k => c * J k) = c • Formalism.L2.Ker.jetLin J := by
    refine (MvPolynomial.basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) K).ext fun m => ?_
    simp only [Formalism.L2.Ker.jetLin, LinearMap.smul_apply, Module.Basis.constr_basis, MvPolynomial.smul_monomial,
      smul_eq_mul]
  ext1 P
  simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, e, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

private theorem prod_pow_fiber {α ι : Type} [Fintype ι] [DecidableEq ι] (f : α → ι) (c : ι → ℂ) (m : α →₀ ℕ) :
    (m.prod fun v e => c (f v) ^ e) = ∏ τ, c τ ^ (m.sum fun v e => if f v = τ then e else 0) := by
  simp only [Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp [pow_ite]

private theorem degree_fiber {α ι : Type} [Fintype ι] [DecidableEq ι] (f : α → ι) (m : α →₀ ℕ) :
    m.degree = ∑ τ, (m.sum fun v e => if f v = τ then e else 0) := by
  simp only [Finsupp.sum]
  rw [Finset.sum_comm, Finsupp.degree_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp

private theorem period_ne {D : D7} {δ : ℂ} (hδ : δ ≠ 0) (τ : D.what₂.Tau) : period δ τ ≠ 0 := by
  refine div_ne_zero hδ (Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 ?_))
  have : 0 < ‖tauE D τ D.host.xi0‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
  positivity

private theorem delta_ne {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) : δ ≠ 0 := by
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hc
  rintro rfl
  have h1 := (hL L.ω₁).2 L.ω₁_mem_lattice
  have h2 : Formalism.MainNotions.TaylorLogMetric.lamOf D cc 0 ≤ ⊥ := by
    rw [Formalism.MainNotions.TaylorLogMetric.lamOf, AddSubgroup.closure_le]
    rintro w ⟨c, -, rfl⟩
    simp
  exact L.indep.ne_zero 0 (by simpa using h2 h1)

theorem UpperTheory.WildA.kkTab :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U : Set T} {N : Std G U} (Z : Normal W N) {t : T} {p : GlobalTheory.ChiGrid.Pair T}, DefPair D.R.m p →
      ∀ (d : FinDatum G t p) (x : FinPt G p.small) (y : FinPt G p.big) (Θ : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS p).rank (G.pT p).rank → ℂ),
      (∀ mon, jetTab W N.frC p (Z.vec d) (x * N.u _) (y * N.u _) mon =
        Z.c0 p * opp p (((mon.mapDomain (fvar G p)).prod fun v e => period Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar G p)) 1) Θ)) →
      Z.kkMap 1 d x y = Formalism.L2.Ker.jetOp (wt G p.small) (wt G p.big)
        (fun mon => if mon.degree = ∑ τ, fockDeg G p τ then
          opp p (Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar G p)) 1) Θ) else 0) (nuEnd G p) := by
  intro D T L sc G W U N Z t p hp d x y Θ h
  classical
  have hδ : Z.δ ≠ 0 := delta_ne Z.crv
  have hf : ∀ k, (fvar G p k).1 = k.1 := fun k => by cases p <;> rfl
  rw [Normal.kkMap, fockComp, ← jetOp_mul_tab']
  refine UpperTheory.WildA.jetDeg _ _ _ (wtOK_of_defPair G p hp).2 _ _ fun m hm => ?_
  have hm' : ∀ τ, (m.sum fun v e => if v.1 = τ then e else 0) = fockDeg G p τ := hm
  have h1 : m.degree = ∑ τ, fockDeg G p τ := by
    rw [degree_fiber Prod.fst m]
    exact Finset.sum_congr rfl fun τ _ => hm' τ
  have h2 : ((m.mapDomain (fvar G p)).prod fun v e => period Z.δ v.1 ^ e) = ∏ τ, period Z.δ τ ^ fockDeg G p τ := by
    rw [Finsupp.prod_mapDomain_index (by simp) (by simp [pow_add])]
    simp only [hf]
    rw [prod_pow_fiber Prod.fst (period Z.δ) m]
    exact Finset.prod_congr rfl fun τ _ => by rw [hm' τ]
  have h3 : (∏ τ, opp p ((1 : D.what₂.Tau → ℂ) τ / period Z.δ τ) ^ fockDeg G p τ) *
      opp p (∏ τ, period Z.δ τ ^ fockDeg G p τ) = 1 := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [map_pow, ← mul_pow, ← map_mul, Pi.one_apply, div_mul_cancel₀ _ (period_ne hδ τ), map_one, one_pow]
  rw [if_pos h1, h, h2, Normal.scal, map_mul, mul_mul_mul_comm, Units.inv_mul, one_mul, ← mul_assoc, h3, one_mul]

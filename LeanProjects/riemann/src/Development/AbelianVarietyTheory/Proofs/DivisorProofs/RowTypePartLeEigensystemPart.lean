import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabelThetaLiftSpaceIffDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEqSmulOfIsot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalEigenvaluesIndependentOfStandardFrameStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsLevelSubPrincipalLevelHilbertModel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.TypePart

variable {D : D7}

theorem star_eq_of_adj {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    {ok : Pl D.host.E → Prop} {h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ H}
    (hN : GlobalTheory.Hk3.NormalFam ok h) {P : Pl D.host.E} (hP : ok P) (d : List ℤ) {x : H} (hx : x ≠ 0) {a b : ℂ}
    (h1 : h P (Finsupp.single d 1) x = a • x) (h2 : h P (Finsupp.single (dualLab d) 1) x = b • x) : star a = b := by
  have hadj := hN.2 P hP (Finsupp.single d 1)
  have hc : GlobalTheory.Hk3.dualC (Finsupp.mapRange star (star_zero ℂ) (Finsupp.single d (1 : ℂ))) = Finsupp.single (dualLab d) 1 := by
    simp [GlobalTheory.Hk3.dualC, Finsupp.mapRange_single, Finsupp.mapDomain_single]
  rw [hc] at hadj
  have e := LinearMap.adjoint_inner_right (h P (Finsupp.single d 1)) x x
  rw [hadj, h1, h2, inner_smul_left, inner_smul_right] at e
  have h0 : (inner ℂ x x : ℂ) ≠ 0 := inner_self_ne_zero.2 hx
  exact (mul_right_cancel₀ h0 e).symm

theorem heckeOperator_conj {V : HSp D} {n : ℕ} (Q : principalLevelFrame.RowPsi V n) (B : Finset (GA D V)) (y : Formalism.AUTREP.GAf D.host.E n → ℂ) :
    principalLevelFrame.Hecke₃ Q B (fun g => star (y g)) = fun g => star (principalLevelFrame.Hecke₃ Q B y g) := by
  funext g
  simp only [principalLevelFrame.Hecke₃, principalLevelFrame.heckeG, LinearMap.sum_apply, Finset.sum_apply, principalLevelFrame.rt_apply, star_sum]

theorem isotE_sub_eigenpart : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, Core R F → SchurAll R → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π i0 c, principalLevelFrame.IsEigOf (PW i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF π c → ∀ b, ∀ U ∈ principalLevelFrame.isotE R.θ PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F b))) (levChi _ (R.βY 0) (R.dat0 (R.levR F b))) R.e0 π, ∃ x ∈ EEc R SF c, R.HE.e x = U := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hC hS SF hSF n hF PY PW hPY hPW π i0 c hEig b U hU
  obtain ⟨h, hOps, hNorm, -, -, hIn⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R F hC hS SF hSF
  obtain ⟨-, hg, hoff, -⟩ := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  obtain ⟨nY, hβY⟩ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  obtain ⟨nW, hβW⟩ := hC.lev.βW i0
  have hi := hC.models.HE.1
  have hUi := Submodule.mem_inf.1 hU
  have hUE : U ∈ R.EEat (R.levR F b) := hUi.1
  have hUT : U ∈ R.EEat R.triv := GlobalTheory.GoodRowsLevel.eeat_le_triv R _ hUE
  obtain ⟨x, rfl⟩ : U ∈ LinearMap.range R.HE.e := by rw [hC.models.HE.2.1]; exact hUT
  have key : ∀ P, Good R A.μ0 P → ∀ d, IsLab (Yc D 0) P d → h P (Finsupp.single d 1) x = star (c P d) • x := by
    intro P hP d hd
    have levY := GlobalTheory.LevOp.level_operators (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβY P
      (by rw [Nat.cast_pow]; exact fun hm => (hg _ P hP).1 (P.isPrime.mem_of_pow_mem nY hm))
      (fun PP hPP => hP PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
    have levW := GlobalTheory.LevOp.level_operators (Wc D i0) (R.βW i0) (R.ΛW i0) _ (R.datWp i0 (R.levL F false (sg0 D A))) hβW P
      (by rw [one_pow, Nat.cast_one]; exact fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1))
      (fun PP hPP => hP PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
    have hB := GlobalTheory.Hk3.OpsRows.sphOp_rep hd
    have hdW : IsLab (Wc D i0) P d := ((GlobalTheory.LabEq.isLab_W_iff (s := s) R F hC i0 P d hP).2).2 hd
    have hB' := GlobalTheory.Hk3.OpsRows.sphOp_rep hdW
    obtain ⟨a, ha⟩ := GlobalTheory.T.sphericalHecke_scalar_on_spherical_vectors hF (PW i0) (hPW i0) π P d _ hB'
    obtain ⟨⟨x0, hx0S, hx0ne, hx0T⟩, hE2, -⟩ := hEig
    have hx0fix : ∀ κ, (PW i0).ψ κ ∈ hyp (Wc D i0) P → Formalism.L2.NG.rt D.host.E n κ x0 = x0 := by
      intro κ hκ
      have e0 := hx0T κ (levW.1 _ hκ).1
      simp only [(levW.1 _ hκ).2, one_smul] at e0
      exact e0
    have haeq : a = c P d := by
      have e1 := ha x0 hx0S hx0fix
      rw [hE2 P d _ ((levW.2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, hB'⟩) x0 hx0S hx0T] at e1
      exact smul_left_injective ℂ hx0ne e1.symm
    obtain ⟨htr1, htr2⟩ := GlobalTheory.T.sphericalEigenvalues_independent_of_standardFrame hF PY (PW i0) hPY (hPW i0) P d
    have hvec : ∀ y ∈ (principalLevelFrame.FinTyp.conjT π).S, (∀ κ, PY.ψ κ ∈ hyp (Yc D 0) P → Formalism.L2.NG.rt D.host.E n κ y = y) →
        principalLevelFrame.Hecke₃ PY (GlobalTheory.Hk3.rep (Yc D 0) P d) y = star (c P d) • y := by
      intro y hy hfy
      have hy' : (fun g => star (y g)) ∈ π.S := hy
      have hfy' : ∀ κ, PY.ψ κ ∈ hyp (Yc D 0) P →
          Formalism.L2.NG.rt D.host.E n κ (fun g => star (y g)) = fun g => star (y g) := by
        intro κ hκ
        rw [← principalLevelFrame.conj_rt, hfy κ hκ]
      have e := htr2 _ _ hB hB' _ hfy'
      rw [ha _ hy' (fun κ hκ => hfy' κ ((htr1 κ).2 hκ)), haeq, heckeOperator_conj] at e
      funext g
      have e2 := congrArg star (congrFun e g)
      simp only [Pi.smul_apply, smul_eq_mul, star_star, star_mul'] at e2
      rw [Pi.smul_apply, smul_eq_mul, e2, mul_comm]
    have hfixU : ∀ k ∈ hyp (Yc D 0) P, postOn (R.MY 0) (principalLevelFrame.rtA k) (R.HE.e x) = R.HE.e x := by
      intro k hk
      ext1 v
      rw [postOn_apply]
      funext g
      have := GlobalTheory.Hk3.OpsRows.mult_lev (goodPart_le _ _ _ _ _ hUT) v k (levY.1 k hk).1 g
      rw [(levY.1 k hk).2, one_mul] at this
      exact this
    have hU2 := GlobalTheory.IsotSph.hecke_eq_smul_of_isot hF PY hPY R.θ (R.MY 0) (principalLevelFrame.FinTyp.conjT π) P d _ _ hB hvec _ hUi.2 hfixU
    apply hi
    rw [hOps P hP, map_smul, GlobalTheory.Hk3.OpsRows.hk_single]
    exact hU2
  refine ⟨x, hIn c x fun P d hP hd => ?_, rfl⟩
  by_cases hx0 : x = 0
  · subst hx0
    simp
  have hdd : IsLab (Yc D 0) P (dualLab d) := by
    have l1 := GlobalTheory.LabEq.isLab_W_iff (s := s) R F hC i0 P d hP
    exact l1.1.1 (l1.2.2 hd)
  have h1 := key P hP d hd
  have e := star_eq_of_adj hNorm hP d hx0 h1 (key P hP _ hdd)
  have e' : star (c P d) = c P (dualLab d) := by
    rw [star_star] at e
    rw [e, star_star]
  rw [h1, e']

end GlobalTheory.TypePart

end

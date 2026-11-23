import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffFrob
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupFormalChartOfConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDimAddFinrankDualLieEqHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusMatrixQuasiLogarithmBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusMatrixIsUnitAdaptedBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusNilpotentModMaximalConnectedPDivGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilDualFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedQuasiLogBasisPDivGroupLieDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogarithmOfDualCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartHasPeriodLinearIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdDivGroupChartFormsBasisAndDifferentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryOneMapEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePeriodQuasiLogarithmPDivGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPeriodFrobeniusTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPeriodReduceAlongThetaToIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPeriodEqTangentHodgeTateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGroupLawLiftOfSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAdaptedBasisQuasiLogarithmsFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmIntegersAdaptedBasisNoLieComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentEqZeroOfFormalGroupLawCoboundaryOneEqZeroStatement

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open GlobalTheory.QLog.Window

namespace GlobalTheory.QLog.WindowMat

section Frame

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O) {ε : PreTilt O p}
  (hε : IsPrimitiveSystem ε) (F : BFrame ε) {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)
  {μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B} (hL : IsLift F.θ μ')
  (hμ : ∀ i, map F.θ (μ' i) = c.μ i)
include hv hε hL hμ

theorem hasPeriod_add_smul (t : G.Tate) {f g : MvPowerSeries (Fin d) F.Q} {y y' : F.B} (b : F.B)
    (hg : DIn (⊤ : Ideal F.B) g) (h1 : c.HasPeriod F.θ t f y) (h2 : c.HasPeriod F.θ t g y') :
    c.HasPeriod F.θ t (f + algebraMap F.B F.Q b • g) (y + b * y') := by
  first
  | exact (GlobalTheory.T.formalChart_hasPeriod_linear_integral p C v O hv ε hε F G d c μ' hL hμ f g t y y' b hg h1 h2).1
  | exact (GlobalTheory.T.formalChart_hasPeriod_linear_integral p C v O hv ε hε F G d c μ' hL hμ f g t y y' b h1 h2).1

theorem hasPeriod_map_zero (t : G.Tate) (s : MvPowerSeries (Fin d) F.B) (hs : constantCoeff s = 0) :
    c.HasPeriod F.θ t (map (algebraMap F.B F.Q) s) 0 := by
  have hz := hasPeriod_zero c F.frame t
  have hd : DIn (⊤ : Ideal F.B) (0 : MvPowerSeries (Fin d) F.Q) := din_of_in (in_zero ⊤)
  first
  | exact (GlobalTheory.T.formalChart_hasPeriod_linear_integral p C v O hv ε hε F G d c μ' hL hμ 0 0 t 0 0 0 hd hz hz).2 s hs
  | exact (GlobalTheory.T.formalChart_hasPeriod_linear_integral p C v O hv ε hε F G d c μ' hL hμ 0 0 t 0 0 0 hz hz).2 s hs

theorem hasPeriod_comb (t : G.Tate) {ι : Type} [Fintype ι] (e : ι → MvPowerSeries (Fin d) F.Q)
    (hd : ∀ i, DIn (⊤ : Ideal F.B) (e i)) (y : ι → F.B) (hy : ∀ i, c.HasPeriod F.θ t (e i) (y i))
    (b : ι → F.B) : c.HasPeriod F.θ t (comb b e) (∑ i, b i * y i) := by
  classical
  unfold comb
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using hasPeriod_zero c F.frame t
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, add_comm (b a * y a)]
    exact hasPeriod_add_smul hv hε F c hL hμ t (b a) (hd a) ih (hy a)

theorem hasPeriod_integral (t : G.Tate) {D : MvPowerSeries (Fin d) F.Q}
    (hD : In (⊤ : Ideal F.B) D) (h0 : constantCoeff D = 0) : c.HasPeriod F.θ t D 0 := by
  obtain ⟨s, rfl⟩ := (in_top_iff D).1 hD
  have hs : constantCoeff s = 0 := by
    apply F.frame.inj
    rw [← constantCoeff_map, h0, map_zero]
  exact hasPeriod_map_zero hv hε F c hL hμ t s hs

theorem hasPeriod_unique (t : G.Tate) {f : MvPowerSeries (Fin d) F.Q} {y y' : F.B}
    (h1 : c.HasPeriod F.θ t f y) (h2 : c.HasPeriod F.θ t f y') : y = y' :=
  h1.unique F.frame h2

theorem hasPeriod_of_in (t : G.Tate) {f g : MvPowerSeries (Fin d) F.Q} {y : F.B}
    (hf : c.HasPeriod F.θ t f y) (hfg : In (⊤ : Ideal F.B) (f - g))
    (h0 : constantCoeff (f - g) = 0) : c.HasPeriod F.θ t g y := by
  have h := hasPeriod_add_smul hv hε F c hL hμ t (-1) (din_of_in hfg) hf
    (hasPeriod_integral hv hε F c hL hμ t hfg h0)
  rwa [map_neg, map_one, neg_one_smul, mul_zero, add_zero, neg_sub, add_sub_cancel] at h

end Frame

theorem window_matrices : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, PDivLat.IsConn G → PDivLat.IsConn G.dual → ∀ F : BFrame ε, ∃ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin G.height) F.B) (Gm : Matrix (Fin G.height) (Fin d ⊕ Fin k) F.B) (tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate) (χ : Fin G.height → G.dual.Tate) (w : Module.Basis (Fin d) O G.omega) (lb : Module.Basis (Fin k) O G.dual.Lie), d + k = G.height ∧ IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin G.height) (Fin G.height) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) ∧ (∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0) ∧ (∀ j m, F.θ (Y (Sum.inr j) m) = lb j (hodgeTate G (tb m))) ∧ ∀ m, dlog G (χ m) = ∑ i, F.θ (Gm m (Sum.inl i)) • w i := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG hGd F
  obtain ⟨d, ⟨c⟩⟩ := GlobalTheory.T.exists_pDivGroupFormalChart_of_connected p C v O hv G hG
  have hdk := GlobalTheory.T.chartDim_add_finrank_dual_lie_eq_height p C v O hv G d c
  have hCf := GlobalTheory.T.isTorsionFreePDThickeningFrame_valuation_integers p C v O hv
  obtain ⟨k, e0, lb, hB0, hA0, hcob0, hLie0⟩ := GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual p C v O hv G d c C hCf
  obtain ⟨μ', hL, hμ⟩ := GlobalTheory.T.exists_formalGroupLawLift_of_surjective F.B O F.θ F.frame.surj d c.μ c.isLaw
  obtain ⟨Θ, hΘ⟩ := frame_fraction_map p F.B O F.Q F.θ F.frame C hCf
  obtain ⟨e, he0, hB, hA⟩ := GlobalTheory.T.exists_lift_adapted_basis_quasi_logarithms_frame p C v O hv ε hε F G d c μ' hL hμ Θ hΘ k e0 hB0 hA0
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_frobenius_matrix_quasiLogarithm_basis p C v O hv ε hε F G d c μ' hL hμ k e hB hA
  have hUu := GlobalTheory.T.frobenius_matrix_isUnit_adapted_basis p C v O hv ε hε F G d c μ' hL hμ k e hB hA U hU
  have hN1 := GlobalTheory.T.frobenius_nilpotent_mod_maximal_connected_pDivGroup p C v O hv ε hε F G d c μ' hL hμ k e hB hA U fun i => (hU i).1
  have hN2 := GlobalTheory.T.isNil_dual_frobenius_alt p C v O hv ε hε F G d c μ' hL hμ k e hB hA hGd U hUu hU
  haveI := integers_isIntegrallyClosedIn hv
  haveI := G.finite_tate C
  haveI := G.free_tate C
  let tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate :=
    Module.finBasisOfFinrankEq ℤ_[p] G.Tate (G.finrank_tate C)
  obtain ⟨χ, hχ, -⟩ :=
    GlobalTheory.DieudonneSandwich.exists_dual_basis hε (G.pairing_flip_bijective C) tb.equivFun
  have hpair : ∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0 := by
    intro m m'
    have h1 := epsPairing_smul hε G (tb m) (χ m')
    rw [hχ m' (tb m)] at h1
    have h2 : epsPairing hε G (tb m) (χ m') = tb.equivFun (tb m) m' := (epsEquiv hε).injective h1
    rw [h2, Module.Basis.equivFun_self]
    all_goals
      by_cases h : m = m'
      · subst h; simp
      · simp [Pi.single_apply, h, Ne.symm h]
  have hQLe : ∀ l, QL μ' ⊤ (e l) := hB.1
  have hDe : ∀ l, DIn (⊤ : Ideal F.B) (e l) := fun l =>
    GlobalTheory.QLogDiff.dIn_of_QL p F.B O F.Q F.θ F.frame d μ' hL ⊤ (e l) (hQLe l)
  choose Y hY using fun l m =>
    (GlobalTheory.T.exists_unique_period_quasiLogarithm_pDivGroup p C v O hv ε hε F G d c μ' hL hμ (e l) (tb m) (hQLe l)).exists
  choose fχ wχ hfχ using fun m => GlobalTheory.T.exists_quasiLogarithm_of_dualCharacter p C v O hv ε hε F G d c μ' hL hμ (χ m)
  choose g hg using fun m => (hB.2 (fχ m) (hfχ m).1).exists
  obtain ⟨hbij, -⟩ := GlobalTheory.T.pdDivGroupChart_forms_basis_and_differential p C v O hv G d c
  let w : Module.Basis (Fin d) O G.omega :=
    Module.Basis.ofEquivFun (LinearEquiv.ofBijective (Fintype.linearCombination O c.form) hbij).symm
  have hw : ∀ i, w i = c.form i := by
    intro i
    simp [w, Module.Basis.ofEquivFun]
  have hcomb0 : ∀ m, constantCoeff (fχ m - comb (g m) e) = 0 := fun m => by
    rw [map_sub, (hfχ m).1.1, (ql_comb hL.const e hQLe (g m)).1, sub_zero]

  have hred : ∀ m, (∀ j, F.θ (g m (Sum.inr j)) = 0) ∧
      ∀ i, lin (map Θ (fχ m)) i = algebraMap O C (F.θ (g m (Sum.inl i))) := fun m => by
    refine GlobalTheory.T.logarithm_integers_adapted_basis_no_lie_components p C v O hv G d c k e0 lb hB0 hA0 hLie0 (map Θ (fχ m))
      (ql_map F.θ Θ hΘ hμ hL.const (hfχ m).1)
      (formalGroupLawCoboundaryOne_map_eq_zero F.θ Θ hΘ hμ hL.const (hfχ m).2.1) (fun l => F.θ (g m l)) ?_
    have := in_map_top F.θ Θ hΘ (hg m)
    rwa [map_sub, map_comb F.θ Θ hΘ, show (fun l => map Θ (e l)) = e0 from funext he0] at this

  have hperO : ∀ l m, c.HasPeriod (RingHom.id O) (tb m) (e0 l) (F.θ (Y l m)) := fun l m => by
    have h := GlobalTheory.T.hasPeriod_reduce_along_theta_to_integers p C v O hv ε hε F G d c μ' hL hμ C hCf Θ hΘ (e l) (tb m) (Y l m)
      (hQLe l) (hY l m)
    rwa [he0] at h
  refine ⟨d, k, U, Matrix.of Y, Matrix.of g, tb, χ, w, lb, ?_, hUu, ?_, ?_, ?_, ?_, ?_, hN1, hN2,
    hpair, ?_, ?_⟩
  · have := Module.finrank_eq_card_basis lb
    rw [Fintype.card_fin] at this
    omega
  ·
    ext i m
    have key : F.σ (Y i m) = ∑ l, (U * blk d k (p : F.B) 1) l i * Y l m := by
      have hc := hasPeriod_comb hv hε F c hL hμ (tb m) e hDe (fun l => Y l m) (fun l => hY l m)
        (fun l => (U * blk d k (p : F.B) 1) l i)
      have hf := GlobalTheory.T.quasiLogarithm_period_frobenius_twist p C v O hv ε hε F G d c μ' hL hμ (e i) (tb m) (Y i m) (hQLe i)
        (hY i m)
      refine hasPeriod_unique hv hε F c hL hμ (tb m)
        (hasPeriod_of_in hv hε F c hL hμ (tb m) hf (hU i).1 ?_) hc
      rw [map_sub, constantCoeff_frob p F.s (hQLe i).1, (ql_comb hL.const e hQLe _).1, sub_zero]
    rw [Matrix.map_apply, Matrix.of_apply, key, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [blk, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
      Matrix.of_apply]
    ring
  ·
    ext l m
    have key : (fun l => ∑ i, (U * blk d k (p : F.B) 1) l i * F.σ (g m i)) =
        fun l => (p : F.B) * g m l := by
      have hP : QL μ' ⊤ (algebraMap F.B F.Q (p : F.B) • fχ m) := by
        simpa using ql_add_smul hL.const (ql_zero (Q := F.Q) hL.const ⊤) (hfχ m).1 (p : F.B)
      refine (hB.2 _ hP).unique ?_ ?_
      · have e1 : algebraMap F.B F.Q (p : F.B) • fχ m -
            comb (fun l => ∑ i, (U * blk d k (p : F.B) 1) l i * F.σ (g m i)) e =
            -(frob p F.s (fχ m) - (p : F.Q) • fχ m) + frob p F.s (fχ m - comb (g m) e) +
              ∑ i, algebraMap F.B F.Q (F.σ (g m i)) •
                (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) := by
          rw [comb_sum (fun l i => (U * blk d k (p : F.B) 1) l i) (fun i => F.σ (g m i)) e, frob_sub, frob_comb p F.s F.σ F.s_alg, map_natCast]
          simp only [comb, smul_sub, Finset.sum_sub_distrib]
          abel
        rw [e1]
        refine in_add (in_add (in_neg (hfχ m).2.2.1) (in_frob p F.s F.σ F.s_alg (hg m)))
          (in_sum _ _ fun i _ => in_smul (hU i).1 _)
      · have e2 : algebraMap F.B F.Q (p : F.B) • fχ m - comb (fun l => (p : F.B) * g m l) e =
            algebraMap F.B F.Q (p : F.B) • (fχ m - comb (g m) e) := by
          simp only [comb, map_mul, mul_smul, smul_sub, Finset.smul_sum]
        rw [e2]
        exact in_smul (hg m) _
    have := congrFun key l
    simp only [Matrix.smul_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, ← this,
      Matrix.mul_apply, Matrix.map_apply]
  ·
    ext m m'
    have key : ∑ l, g m l * Y l m' =
        F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G (tb m') (χ m))) := by
      refine hasPeriod_unique hv hε F c hL hμ (tb m')
        (hasPeriod_comb hv hε F c hL hμ (tb m') e hDe (fun l => Y l m') (fun l => hY l m') (g m)) ?_
      exact hasPeriod_of_in hv hε F c hL hμ (tb m') ((hfχ m).2.2.2.2.2 (tb m')) (hg m) (hcomb0 m)
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    rw [key, hpair]
    by_cases h : m' = m
    · subst h; simp
    · simp [h, Ne.symm h]
  ·
    intro i m
    have hlie := GlobalTheory.T.tangent_eq_zero_of_formalGroupLawCoboundaryOne_eq_zero p C v O hv G d c (e0 (Sum.inl i)) (hB0.1 (Sum.inl i)).1 (hcob0 i)
    have h2 := GlobalTheory.T.quasiLogarithm_period_eq_tangent_hodgeTate p C v O hv G d c C hCf (e0 (Sum.inl i)) 0 (hB0.1 _) hlie (tb m)
    simpa using (hperO _ m).unique hCf h2
  · intro m j
    exact (hred m).1 j
  · intro j m
    exact (hperO _ m).unique hCf
      (GlobalTheory.T.quasiLogarithm_period_eq_tangent_hodgeTate p C v O hv G d c C hCf (e0 (Sum.inr j)) (lb j) (hB0.1 _) (hLie0 j) (tb m))
  · intro m
    rw [(hfχ m).2.2.2.2.1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := (hred m).2 i
    rw [lin_map F.θ Θ hΘ, (hfχ m).2.2.2.1 i, hΘ] at h1
    rw [hw, Matrix.of_apply, hCf.inj h1]

end GlobalTheory.QLog.WindowMat

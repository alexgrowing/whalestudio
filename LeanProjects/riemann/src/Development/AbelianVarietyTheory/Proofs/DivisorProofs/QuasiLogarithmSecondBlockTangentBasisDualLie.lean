import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameReflTransGenCyclicChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisLiftPdThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftQuasiLogarithmAlongPdThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedQuasiLogBasisPDivGroupLieDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentOfQuasiLogarithmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentLinearKillsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisOfBlockLowerTriangularInvStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisTransitionMatricesInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorQuasiLogarithmOfCongruentCombinatioStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecondTangent

theorem tangent_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → ∃ lb : Module.Basis (Fin k) O G.dual.Lie, ∀ j, c.IsLie (map Θ (e (Sum.inr j))) (lb j) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hμ k e he hadapt Θ hΘ
  have hF : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  have hμeq : (fun i => map F.θ (μ' i)) = c.μ := funext hμ
  obtain ⟨k', es, lbs, hbs, -, hcobs, hlies⟩ := GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual p C v O hv G d c C hF

  have hlift1 : ∀ m, ∃ f : MvPowerSeries (Fin d) F.Q, QL μ' ⊤ f ∧ map Θ f = es m := by
    intro m
    have hq : QL (fun i => map F.θ (μ' i)) ⊤ (es m) := hμeq ▸ hbs.1 m
    choose b _ hb using hq.2.1
    choose w hw using fun i => F.frame.surj (b i)
    obtain ⟨f, hf, hf', -⟩ := GlobalTheory.QLog.KLift.lift_quasiLog p F.B O F.Q F.θ F.frame d μ' hlift C hF
      Θ hΘ (es m) w hq (fun i => by rw [hb, hw])
    exact ⟨f, hf, hf'⟩
  choose f hfq hfm using hlift1
  have hfb : IsBasis μ' f := by
    refine GlobalTheory.basis_lift p F.B O F.Q F.θ F.frame d μ' hlift C hF Θ hΘ _ f hfq ?_
      (GlobalTheory.BChain.reflTransGen_isStep p C v O hv ε hε F)
    have : (fun i => map Θ (f i)) = es := funext hfm
    rw [this, hμeq]; exact hbs

  choose P hP using fun i => (hfb.2 (e i) (he.1 i)).exists
  choose P' hP' using fun j => (he.2 (f j) (hfq j)).exists
  obtain ⟨h1, h2⟩ := GlobalTheory.T.quasiLogarithmBasis_transitionMatrices_inverse μ' e f he hfb P P' hP hP'

  let Ls : Fin d ⊕ Fin k' → G.dual.Lie := Sum.elim 0 lbs
  have hLs : ∀ m, c.IsLie (es m) (Ls m) := by
    rintro (i | j)
    · obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c C hF (es (Sum.inl i)) (hbs.1 _)
      have := (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c C hF _ _ l l 0 hl hl).2.2 (hcobs i)
      subst this; exact hl
    · exact hlies j
  have hμc : ∀ i, constantCoeff (μ' i) = 0 := hlift.const
  have hg : ∀ i, QL c.μ ⊤ (map Θ (e i)) := fun i => by
    rw [← hμeq]; exact GlobalTheory.SmallSecond.ql_map hΘ μ' hμc (he.1 i)
  have hrow : ∀ i, c.IsLie (map Θ (e i)) (∑ m, F.θ (P i m) • Ls m) := by
    intro i
    refine GlobalTheory.T.tangentVector_quasiLogarithm_of_congruent_combination p C v O hv G d c es (hbs.1) Ls hLs _ (hg i) _ ?_
    intro α
    obtain ⟨b, -, hb⟩ := hP i α
    refine ⟨F.θ b, trivial, ?_⟩
    have : map Θ (e i) - comb (fun m => F.θ (P i m)) es = map Θ (e i - comb (P i) f) := by
      rw [map_sub, GlobalTheory.SmallSecond.map_comb hΘ, funext hfm]
    rw [this, coeff_map, hb, hΘ]

  have hzero : ∀ i j, F.θ (P (Sum.inl i) (Sum.inr j)) = 0 := by
    intro i
    have hc : cob1 (up C c.μ) (map Θ (e (Sum.inl i))) = 0 := by
      rw [← hμeq]; exact GlobalTheory.SmallSecond.formalGroupLawCoboundaryOne_map_eq_zero hΘ μ' hμc (hadapt i).1
    have h0 := (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c C hF _ _ _ _ 0 (hrow (Sum.inl i)) (hrow (Sum.inl i))).2.2 hc
    simp only [Fintype.sum_sum_type, Ls, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, smul_zero,
      Finset.sum_const_zero, zero_add] at h0
    exact (Fintype.linearIndependent_iff.1 lbs.linearIndependent) _ h0
  obtain ⟨lb, hlb⟩ := GlobalTheory.T.exists_basis_of_blockLowerTriangular_inv' O G.dual.Lie d k k' lbs ((Matrix.of P).map F.θ)
    ((Matrix.of P').map F.θ) (by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]) hzero
  refine ⟨lb, fun j => ?_⟩
  have := hrow (Sum.inr j)
  simp only [Fintype.sum_sum_type, Ls, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, smul_zero,
    Finset.sum_const_zero, zero_add] at this
  rw [hlb]; exact this

end GlobalTheory.SmallSecondTangent

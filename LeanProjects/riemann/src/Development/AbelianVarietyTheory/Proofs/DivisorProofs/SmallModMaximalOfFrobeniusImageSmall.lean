import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCoordsNonunitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryFrobeniusCommuteModPQuasiLogStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLinearCombinationZeroLeftAinfFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusCongruenceCombinationOverIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotIsUnitCoeffOfCoboundarySmallStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCoboundaryOneCongrFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmSecondBlockTangentBasisDualLieStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecond

theorem small_second : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ b : Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) j)) l))) → ∀ j, ¬IsUnit (F.θ (b j)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hμ' hc k e he hA U hU b hW j
  have hC : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  obtain ⟨Θ, hΘ⟩ := frame_fraction_map p F.B O F.Q F.θ F.frame C hC
  have hcμ : (fun i => map F.θ (μ' i)) = c.μ := funext hc
  have hconst : ∀ i, constantCoeff (μ' i) = 0 := hμ'.const

  have hQL : ∀ i, QL c.μ ⊤ (map Θ (e i)) := fun i => hcμ ▸ ql_map hΘ μ' hconst (he.1 i)
  have hlog : ∀ i, cob1 (up C c.μ) (map Θ (e (Sum.inl i))) = 0 := fun i =>
    hcμ ▸ formalGroupLawCoboundaryOne_map_eq_zero hΘ μ' hconst (hA i).1
  obtain ⟨lb, hlb⟩ := GlobalTheory.T.quasiLogarithm_secondBlock_tangent_basis_dual_lie p C v O hv ε hε F G d c μ' hμ' hc k e he hA Θ hΘ

  have hT := GlobalTheory.T.frobenius_linearCombination_zero_left_ainfFrame p O ε F d k e U (fun i => (hU i).1) b
  have hC1 := GlobalTheory.T.coboundary_frobenius_commute_mod_p_quasiLog p O ε F d μ' hμ' (Fin d ⊕ Fin k) e he.1 (Sum.elim (fun _ => 0) b)
  obtain ⟨F₁, t, hF₁, hlin, hpβ, hα⟩ := GlobalTheory.T.frobenius_congruence_combination_over_integers p C v O hv ε F d c.μ μ' hμ' hc k e he.1 _ b hW hT hC1
  have ht := GlobalTheory.T.not_isUnit_coeff_of_coboundary_small' p C v O hv d c.μ c.isLaw t hlin hα
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_integral_coboundaryOne_congr_frobenius p C v O hv d c.μ c.isLaw (map F.θ F₁) t ht
    (fun β => by rw [coeff_map]; exact hpβ β)
  have key : cob1 (up C c.μ) (comb (Sum.elim 0 fun j => F.θ (b j)) fun i => map Θ (e i)) =
      map (algebraMap O C) (map F.θ F₁) := by
    have h1 : (Sum.elim 0 fun j => F.θ (b j) : Fin d ⊕ Fin k → O) =
        fun i => F.θ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) i) := by
      funext i; rcases i with i | i <;> simp
    rw [h1, ← map_comb hΘ, ← hcμ, ← map_formalGroupLawCoboundaryOne_square hΘ μ' hconst, ← hF₁]
    ext α; simp [coeff_map, hΘ]
  refine GlobalTheory.T.tangent_coords_nonunit_alt p C v O hv G d c C hC k (fun i => map Θ (e i)) lb hQL hlb hlog
    (fun j => F.θ (b j)) u (fun α => ⟨_, hu α, ?_⟩) j
  rw [key, ← map_sub, coeff_map, map_sub]

end GlobalTheory.SmallSecond

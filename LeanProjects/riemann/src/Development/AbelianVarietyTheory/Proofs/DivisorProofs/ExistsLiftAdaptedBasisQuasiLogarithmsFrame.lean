import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffFrob
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryOneMapEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftQuasiLogarithmAlongPdThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisLiftPdThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameReflTransGenCyclicChainStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.LiftBasis

theorem exists_lift_isAdapted : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → ∀ (k : ℕ) (e0 : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C), IsBasis c.μ e0 → IsAdapted (RingHom.id O) c.μ e0 → ∃ e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q, (∀ l, map Θ (e l) = e0 l) ∧ IsBasis μ' e ∧ IsAdapted F.θ μ' e := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hμ' hμ Θ hΘ k e0 hB hA
  have hC : IsFrame p C (RingHom.id O) := GlobalTheory.T.isTorsionFreePDThickeningFrame_valuation_integers p C v O hv
  have hF : IsFrame p F.Q F.θ := F.frame
  have hμf : (fun i => map F.θ (μ' i)) = c.μ := funext hμ

  have hw : ∀ l, ∃ w : Fin d → F.B, (∀ i, lin (e0 l) i = algebraMap O C (F.θ (w i))) ∧
      ∀ j, l = Sum.inl j → w = Pi.single j 1 := by
    intro l
    cases l with
    | inl j =>
      refine ⟨Pi.single j 1, fun i => ?_, fun j' h => by cases h; rfl⟩
      rw [(hA j).2]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    | inr j =>
      refine ⟨fun i => Classical.choose (hF.surj (Classical.choose ((hB.1 (Sum.inr j)).2.1 i))),
        fun i => ?_, fun j' h => by cases h⟩
      rw [Classical.choose_spec (hF.surj _)]
      exact (Classical.choose_spec ((hB.1 (Sum.inr j)).2.1 i)).2
  choose w hw1 hw2 using hw
  have hlift : ∀ l, ∃ f : MvPowerSeries (Fin d) F.Q, QL μ' ⊤ f ∧ map Θ f = e0 l ∧
      ∀ i, lin f i = algebraMap F.B F.Q (w l i) := by
    intro l
    refine GlobalTheory.T.lift_quasiLogarithm_along_pdThickening p F.B O F.Q F.θ hF d μ' hμ' C hC Θ hΘ (e0 l) (w l) ?_ (hw1 l)
    rw [hμf]; exact hB.1 l
  choose e he1 he2 he3 using hlift
  refine ⟨e, he2, ?_, ?_⟩
  · refine GlobalTheory.T.quasiLogarithm_basis_lift_pdThickening p F.B O F.Q F.θ hF d μ' hμ' C hC Θ hΘ (Fin d ⊕ Fin k) e he1 ?_
      (GlobalTheory.T.ainfSquareZeroFrame_reflTransGen_cyclic_chain p C v O hv ε hε F)
    rw [hμf]
    have : (fun i => map Θ (e i)) = e0 := funext he2
    rw [this]; exact hB
  · intro i
    refine ⟨fun α => ?_, ?_⟩
    · obtain ⟨b, -, eb⟩ := (he1 (Sum.inl i)).2.2 α
      refine ⟨b, RingHom.mem_ker.2 ?_, eb⟩
      obtain ⟨b', hb', eb'⟩ := (hA i).1 α
      have hb0 : b' = 0 := RingHom.mem_ker.1 hb'
      have hup : up C c.μ = fun j => map Θ (up F.Q μ' j) :=
        funext (WindowMat.up_map F.θ Θ hΘ hμ)
      have key : algebraMap O C (F.θ b) = 0 := by
        rw [← hΘ, ← eb, ← coeff_map, Window.map_formalGroupLawCoboundaryOne_eq Θ _ (Window.constantCoeff_up hμ'.const),
          ← hup, he2, eb', hb0, map_zero]
      exact hC.inj (by rw [key, map_zero])
    · funext j
      rw [he3, hw2 _ i rfl]
      by_cases hij : j = i
      · subst hij; simp
      · simp [Pi.single_apply, hij]

end GlobalTheory.QLog.LiftBasis

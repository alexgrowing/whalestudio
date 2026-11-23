import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OneLeAPlLast
import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSLowK

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLift

theorem holShape_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_order → ∀ i, HolShape (R.MW i (sg0 D A)) ∧ ∃ w, WtIs (R.MW i (sg0 D A)) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R ho i
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 = (Wc D i).rank :=
    fun τ => GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam ((R.MW i (sg0 D A)).lam ρ) := fun ρ => by
    have he := (R.MW i (sg0 D A)).enum ρ
    refine ⟨he.1, fun a => ?_⟩
    obtain ⟨-, f, hf, hS⟩ := he
    have hp : Links.parAt (Wc D i) (sg0 D A) ρ = Formalism.L2.NTheta.holPar _ _ (Formalism.L2.NTheta.wtOf D (Wc D i) ρ) := by
      rw [hs]; exact GlobalTheory.ThetaFiresProbe.parAt_fixed _ ρ
    rw [hp] at hS
    have hm : (f a, (R.MW i (sg0 D A)).ε ρ a) ∈ Formalism.L2.NTheta.holPar _ _ (Formalism.L2.NTheta.wtOf D (Wc D i) ρ) := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hm
    have hx1 := congrArg Prod.fst hx
    have hn : (((Wc D i).rank : ℕ) : ℝ) = (((Wc D i).sig (tauE D ρ)).1 : ℝ) + ((Wc D i).sig (tauE D ρ)).2 := by
      rw [← hpq ρ]; push_cast; rfl
    dsimp only at hx1
    rw [hf a, ← hx1, hn]
    rcases x with c | c
    · refine ⟨Formalism.L2.NTheta.wtOf D (Wc D i) ρ (Sum.inl c) - ((Wc D i).sig (tauE D ρ)).2 - (c : ℕ), ?_⟩
      simp only [Formalism.L2.NTheta.holEnt, Sum.elim_inl]
      push_cast
      ring
    · refine ⟨Formalism.L2.NTheta.wtOf D (Wc D i) ρ (Sum.inr c) - (c : ℕ), ?_⟩
      simp only [Formalism.L2.NTheta.holEnt, Sum.elim_inr]
      push_cast
      ring
  refine ⟨fun ρ => ⟨hc ρ, _, (Nat.le_add_right _ _).trans (hpq ρ).le, fun a => ho i ρ a⟩, ?_⟩
  choose w hw using fun ρ a => Formalism.QuantumDeterminants.low_k_integrable_holds _ ((R.MW i (sg0 D A)).ε ρ) _ (hc ρ).2 a
  exact ⟨fun ρ c => w ρ (revNeg ((R.MW i (sg0 D A)).ε ρ) (arr (nNeg ((R.MW i (sg0 D A)).ε ρ)) c)),
    fun ρ c => (hw ρ _).symm⟩

end GlobalTheory.DefLift

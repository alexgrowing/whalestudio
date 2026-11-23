import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaLiftLinearMapCuspFormMultiplicity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalLevelFixesFockVectorsFiniteDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModelHolomorphicOverReflexFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LoweringPartKillsFockProductMinorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFockVectorHeisenbergAverageIsotropicEqZeroStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow.CuspLift

theorem liftIsCuspC : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), LiftIsCuspC R F := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F
  intro i t σ s P cμ cη m ω BW f₀ f c io hd ν 𝓕 hν φ hφ
  obtain ⟨hcore, -, hemb, -, -, hom, -, -, hpt, hc, hio⟩ := id hd
  have h5 := GlobalTheory.Core5.of_core hcore
  have hm := h5.models
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [hm.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  obtain ⟨hM, w, hw⟩ := GlobalTheory.T.liftModel_holomorphic_overReflexField R F h5 i σ s hemb
  have : IsTopologicalGroup (GA D (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hF := GlobalTheory.ThetaIntegrand.form_continuous (finHom (Vc D i)).rangeRestrict (GQ (Vc D i)) c.ρ hc.2.2.1
    (eventually_grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) hφ
  have key := GlobalTheory.DefLift.ThetaMap.exists_member hP hom hm.inf hpos hM hw hc
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) BW f) hpt hio
    (GlobalTheory.T.lowering_part_kills_fock_product_minors R F i t σ s P cμ cη m ω BW f₀ f c io hd)
    (J := levS _ (R.βW i) (R.datWp i R.triv)) (fun _ hk => hk.1) (GlobalTheory.DefLift.ThetaMap.level_open _ _ _)
    (fun k hk Q => GlobalTheory.PrincipalLevelFock.levW_fix_ptAt R F i t σ s P cμ cη m ω BW f₀ f c io hd Q k hk)
    (GlobalTheory.IndefiniteRowSideFullHecke.VectorLevelCharacters.principalLevelCharacter_eq_one R i)
    (fun Q h g ξ hξ => GlobalTheory.T.levelFockVector_heisenbergAverage_isotropic_eq_zero R F i t σ s P cμ cη m ω BW f₀ f c io hd Q h g ξ hξ)
    hF (GlobalTheory.ThetaIntegrand.ext_invariant c hφ) hν.1.1 hν.2
  obtain ⟨Θ, hΘ, hΘv⟩ := key
  refine ⟨Θ, Submodule.subset_span hΘ, fun v g => ?_⟩
  rw [hΘv v]
  rfl

end GlobalTheory.LowRow.CuspLift

end

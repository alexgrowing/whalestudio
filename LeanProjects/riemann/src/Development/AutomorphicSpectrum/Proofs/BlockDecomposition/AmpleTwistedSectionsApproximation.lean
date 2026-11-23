import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealElementMapsClosedSystemDownStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedClosedSystemCoherentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedPiecesGeneratedByIdealGeneratorsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreVanishingFirstCohomologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftingBaseOfVanishingCohomologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedGradedGenerationGlobalSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftingInductiveSuccessiveApproximationStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

theorem step_uniform : UniformGen → ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∃ n₁ : ℤ, ∀ n, n₁ ≤ n → ∀ e, ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1) := by
  intro hG A _ _ I X _ _ H hH P hP S hS
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hPq : P.IsQuasicoherent := hP.1
  have hL : H.IsLB := hH.isLB
  obtain ⟨k, g, hg⟩ := exists_fin_generators I
  have hgI : ∀ i, g i ∈ I := fun i => hg ▸ Ideal.subset_span ⟨i, rfl⟩
  have hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i)) :=
    fun i => GlobalTheory.T.ideal_element_maps_closed_system_down I hPq S hS (g i) (hgI i)
  have hO : OpSeq k (fun e => gr (anti hS) e) (fun i e => grT (anti hS) (hr i) e) 0 :=
    ⟨fun e => GlobalTheory.T.graded_closed_system_coherent I hP S hS e, fun i j e => grT_comm _ _ _ _,
      fun e _ U => GlobalTheory.T.graded_pieces_generated_by_ideal_generators I hPq S hS g hg hr e U⟩
  obtain ⟨n₁, h₁⟩ := @hG A _ _ X _ _ H hH k _ _ 0 hO
  have hS0 : IsCoherent (S 0 : X.Modules) := GlobalTheory.T.coherent_subobject_coherent hP (S 0) (hS.qcoh 0)
  obtain ⟨n₂, h₂⟩ := GlobalTheory.T.serre_vanishing_first_cohomology A H hH hS0
  refine ⟨max n₁ n₂, fun n hn e => ?_⟩
  have hl : ∀ e, Lifts I H hS n e := by
    intro e
    induction e with
    | zero => exact GlobalTheory.T.lifting_base_of_vanishing_cohomology I H hL S hS n (h₂ n (le_of_max_le_right hn))
    | succ e ih => exact GlobalTheory.T.twisted_graded_generation_global_sections I H S hS g hgI hr n e (h₁ n (le_of_max_le_left hn) e (Nat.zero_le _)) ih
  exact GlobalTheory.T.lifting_inductive_successive_approximation I H hL S hS n e (hl (e + 1))

end GlobalTheory.CompanionTheory.GE.Step

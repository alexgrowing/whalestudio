import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafQuasicoherentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeOfTwistedSectionMemStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafAddLeSupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeIdealPowerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentNoetherianMaximalSubsheafStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AmpleTwistSectionsGenerateSubsheafStatement

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem exists_alg_of_twSecs : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsNoetherian X] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ (n₁ : ℤ) (W : ∀ n : ℤ, Set Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ n e, W n ⊆ twSecs H n (S e)) → (∀ n, n₁ ≤ n → ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W n, x - b ∈ twPow I H n P (e + 1)) → ∃ B : Subobject P, (B : X.Modules).IsQuasicoherent ∧ ∀ e, B ⊔ powSub I P (e + 1) = S e := by
  intro A _ _ I X _ _ H hA P hP S hS n₁ W hW hgen
  have hH := hA.isLB
  let F : Set (Subobject P) := {B | (B : X.Modules).IsQuasicoherent ∧ ∀ e, B ≤ S e}
  have h0 : (0 : Γ(GlobalTheory.twistZ P H n₁, ⊤)) ∈ twSecs H n₁ (S 0) := ⟨0, map_zero _⟩
  obtain ⟨b₀, hb₀, -⟩ := hgen n₁ le_rfl 0 0 h0
  have hF : F.Nonempty :=
    ⟨genSub hH n₁ b₀, GlobalTheory.T.generated_subsheaf_quasicoherent hH hP.1 n₁ b₀, fun e => GlobalTheory.T.generated_subsheaf_le_of_twisted_section_mem hH (S e) n₁ b₀ (hW n₁ e hb₀)⟩
  obtain ⟨M, ⟨hMq, hMS⟩, hMmax⟩ := GlobalTheory.T.coherent_noetherian_maximal_subsheaf hP F hF (fun B hB => hB.1)
  have hgenM : ∀ n, ∀ b ∈ W n, genSub hH n b ≤ M := by
    intro n b hb
    have hmem : M ⊔ genSub hH n b ∈ F :=
      ⟨(GlobalTheory.T.quasicoherent_sup_sections hP.1 M (genSub hH n b) hMq (GlobalTheory.T.generated_subsheaf_quasicoherent hH hP.1 n b)).1,
        fun e => sup_le (hMS e) (GlobalTheory.T.generated_subsheaf_le_of_twisted_section_mem hH (S e) n b (hW n e hb))⟩
    rw [← hMmax _ hmem le_sup_left]
    exact le_sup_right
  refine ⟨M, hMq, fun e => le_antisymm (sup_le (hMS e) (hS.pow_le e)) ?_⟩
  have hSe : IsCoherent (S e : X.Modules) := GlobalTheory.T.coherent_subobject_coherent hP (S e) (hS.qcoh e)
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.ample_twist_sections_generate_subsheaf hA (S e) hSe
  refine hn₀ (max n₀ n₁) (le_max_left _ _) _ fun x hx => ?_
  obtain ⟨b, hb, hxb⟩ := hgen (max n₀ n₁) (le_max_right _ _) e x hx
  rw [← add_sub_cancel b x]
  exact (GlobalTheory.T.generated_subsheaf_add_le_sup hH _ b (x - b)).trans (sup_le_sup (hgenM _ b hb) (GlobalTheory.T.generated_subsheaf_le_ideal_power I hH hP.1 _ _ _ hxb))

end GlobalTheory.CompanionTheory.GE.TwGen

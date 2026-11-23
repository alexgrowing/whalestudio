import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedNoetherianStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishingOfGradedNoetherianStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformGenerationOfVanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AmpleTwistedSectionsApproximationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsFiniteGeneratorsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsUniformGeneratorsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentExtensionSurjectionOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemRestrictionOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemRestrictionSubobjectStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemOpenIdealContainmentStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem exists_sub_of_ample {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : IsAdicComplete I A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (hH : GlobalTheory.IsAmpleLB H) {P : X.Modules} (hP : IsCoherent P) (S : ℕ → Subobject P) (hS : ClosedSys I P S) :
    ∃ B : Subobject P, (B : X.Modules).IsQuasicoherent ∧ ∀ e, B ⊔ powSub I P (e + 1) = S e := by
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have hno : IsNoetherian X := ⟨⟩
  have hV : UniformVanishing := @GlobalTheory.T.uniform_vanishing_of_graded_noetherian GlobalTheory.T.graded_noetherian
  have hG : UniformGen := @GlobalTheory.T.uniform_generation_of_vanishing GlobalTheory.T.graded_noetherian (@hV)
  obtain ⟨n₁, h₁⟩ := GlobalTheory.T.ample_twisted_sections_approximation (@hG) I H hH hP S hS
  have hW : ∀ n : ℤ, ∃ W : Set Γ(GlobalTheory.twistZ P H n, ⊤), (∀ e, W ⊆ twSecs H n (S e)) ∧
      (n₁ ≤ n → ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W, x - b ∈ twPow I H n P (e + 1)) := fun n => by
    by_cases hn : n₁ ≤ n
    · obtain ⟨W, a, b⟩ := GlobalTheory.T.twisted_sections_finite_generators I hI H hH hP S hS n (h₁ n hn)
      exact ⟨W, a, fun _ => b⟩
    · exact ⟨∅, fun _ => Set.empty_subset _, fun h => absurd h hn⟩
  choose W a b using hW
  exact GlobalTheory.T.twisted_sections_uniform_generators I H hH hP S hS n₁ W a b

theorem statement_open_projective : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {N : ℕ} {Y : Scheme.{0}} (i : Y ⟶ projectiveSpace A N), IsClosedImmersion i → ∀ (O : Y.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ i ≫ ProjSpace.toSpecBase A N⟩; Statement I (⊥ : (O : Scheme.{0}).IdealSheafData) := by
  intro A _ _ I hI N Y i hi O
  letI : Y.Over (Spec (.of A)) := ⟨i ≫ ProjSpace.toSpecBase A N⟩
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (Y ↘ Spec (.of A))⟩
  have hpr : IsProper (ProjSpace.toSpecBase A N) := by
    open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ProjSpace in exact isProper_str A N
  have hp : IsProper (Y ↘ Spec (.of A)) := (inferInstance : IsProper (i ≫ ProjSpace.toSpecBase A N))
  have hln : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of A))
  have hcs : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of A))
  have hno : IsNoetherian Y := ⟨⟩
  have hH : GlobalTheory.IsAmpleLB ((GlobalTheory.ProjSpace.O1 A N).pull i) := (GlobalTheory.isAmple_projective_O_one A N).pull_of_isAffineHom i
  intro E hE S hS _ hP
  obtain ⟨P, hPc, f, hf⟩ := GlobalTheory.T.coherent_extension_surjection_open _ hH O E hE
  obtain ⟨T, hT, hTs⟩ := hP
  obtain ⟨hcl, Sb, hSb, hb, hc⟩ := GlobalTheory.T.closed_system_restriction_open I O hPc hE f hf S hS T hT hTs
  obtain ⟨Bb, hBq, hBb⟩ := exists_sub_of_ample I hI _ hH hPc Sb hSb
  obtain ⟨B, hBq', hB, hBs⟩ := GlobalTheory.T.closed_system_restriction_subobject I O hPc hE f hf S hS Sb hb Bb hBq hBb
  exact ⟨B, hBq', GlobalTheory.T.closed_system_open_ideal_containment I hI O hPc hE f hf (Sb 0) T hcl (hc 0) Bb hBq (hBb 0) B hBs, hB⟩

end GlobalTheory.CompanionTheory.GE

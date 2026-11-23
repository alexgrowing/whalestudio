import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnIdempotentSplits
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfRetract
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.IdemImage

theorem isSemiAbelian_image : ∀ (S : Scheme.{0}) (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ e : G' ⟶ G', IsMonHom e → e ≫ e = e → ∃ (G : Over S) (_ : GrpObj G) (_ : IsCommMonObj G) (inc : G ⟶ G') (pr : G' ⟶ G), IsSemiAbelian G ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 G ∧ pr ≫ inc = e := by
  intro S G' _ _ hG e he hee
  have hsm : GlobalTheory.SS.SmConn G' :=
    ⟨hG.comm, hG.smooth, hG.separated, hG.quasiCompact, hG.geomConnected⟩
  obtain ⟨G, hgrp, inc, pr, hG₁, hinc, hpr, hip, hpi⟩ :=
    GlobalTheory.SS.smConn_idempotent_splits S G' hsm e he hee
  exact ⟨G, hgrp, hG₁.1, inc, pr,
    GlobalTheory.SS.isSemiAbelian_of_retract S G' G hG hG₁ inc pr hpr hip, hinc, hpr, hip, hpi⟩

end GlobalTheory.Mum.IdemImage

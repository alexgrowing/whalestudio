import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSmConnOfIsProper
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperSmoothConnGroupSchemeDvrOfProperFibres
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ToricRankZero

theorem isProper_of_torusExtension_of_finrank_eq_zero {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G]
    (E : TorusExtension G) (hX : (letI := E.addCommGroup; Module.finrank ℤ E.X) = 0) : IsProper G.hom := by
  letI := E.addCommGroup
  letI := E.free
  letI := E.finite
  letI := E.grpB
  haveI := E.q_hom
  have hsub : Subsingleton E.X := Module.finrank_zero_iff.1 hX
  have hp := E.isKernel
  have : Mono E.q := ⟨fun {Y} x y hxy => by
    have h1 : (x * y⁻¹) ≫ E.q = toUnit _ ≫ η[E.B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
      rfl
    have h2 : hp.lift _ _ h1 = 1 := by
      apply (GlobalTheory.splitTorusPointsEquiv (Sp k) E.X Y).injective
      refine MonoidHom.ext fun a => ?_
      have ha1 : a = 1 := by
        show a = Multiplicative.ofAdd 0
        rw [← ofAdd_toAdd a, Subsingleton.elim (Multiplicative.toAdd a) 0]
      rw [ha1, map_one, map_one]
    have h3 := hp.lift_fst _ _ h1
    haveI := E.i_hom
    rw [h2, MonObj.one_comp] at h3
    exact mul_inv_eq_one.1 h3.symm⟩
  have : Mono E.q.left := inferInstanceAs (Mono ((Over.forget _).map E.q))
  have := E.isAbelian.proper
  have : Flat E.q.left := E.q_flat
  have : Surjective E.q.left := E.q_surjective
  have : QuasiCompact E.q.left := E.q_quasiCompact
  have : IsIso E.q.left := Flat.isIso_of_surjective_of_mono E.q.left
  rw [← Over.w E.q]
  infer_instance

theorem isAbelianScheme_of_finrank_eq_zero : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], IsSemiAbelian G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → ∀ E : TorusExtension (GlobalTheory.SS.spFibre G), (letI := E.addCommGroup; Module.finrank ℤ E.X) = 0 → IsAbelianScheme G := by
  intro W L _ _ _ _ _ _ G _ hG hgen E hE
  have hS : GlobalTheory.SS.SmConn G := ⟨hG.comm, hG.smooth, hG.separated, hG.quasiCompact, hG.geomConnected⟩
  have hsp : IsProper (GlobalTheory.SS.spFibre G).hom := isProper_of_torusExtension_of_finrank_eq_zero _ E hE
  exact GlobalTheory.SmConnProper.isAbelianScheme_of_smConn_of_isProper _ G hS
    (GlobalTheory.GoodRedProper.isProper_of_proper_fibres W L G hS hgen hsp)

end GlobalTheory.ToricRankZero

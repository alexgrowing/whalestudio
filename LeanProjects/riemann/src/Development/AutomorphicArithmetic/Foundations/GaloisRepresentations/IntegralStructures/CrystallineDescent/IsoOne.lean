import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobInvAway
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

theorem UpperTheory.Gal.Int.Core.isoOne_holds :
    IsoOne := by
  intro F Ω _ _ _ _ _ l _ ι a r r' hr hr' hs hs' hev
  rw [Filter.eventually_cofinite] at hev
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hev
  refine GlobalTheory.SplitAttUniq.repIso_of_dense r r' hr hr' hs hs' _ (hD.preimage (Homeomorph.inv (G F Ω)).isOpenMap) ?_
  intro g hg
  obtain ⟨v, hv, hdeg, B, hB, hfr⟩ := hg
  have hprime : Nat.Prime (normV v) := by
    have h := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hdeg
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h
  have hv' : ¬¬(Nat.Prime (normV v) → ∃ S, FrobEig ι r v S ∧ FrobEig ι r' v S) := hv
  obtain ⟨S, h1, h2⟩ := (not_not.1 hv') hprime
  have e1 := (h1 B hB).2 _ hfr
  have e2 := (h2 B hB).2 _ hfr
  simp only [Homeomorph.coe_inv, inv_inv] at e1 e2
  exact Polynomial.map_injective _ ι.injective (e1.trans e2.symm)

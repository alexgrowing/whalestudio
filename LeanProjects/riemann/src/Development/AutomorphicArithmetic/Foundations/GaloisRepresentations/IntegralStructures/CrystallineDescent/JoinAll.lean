import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CoreAtQIffRowQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitAtOfDegOne
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core
open UpperTheory.Gal.TP

namespace UpperTheory.Gal.Int.Core

theorem goodGuard_usPl (h1 : OneUs) (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (d : ℕ) (hd : ImQ E d) : GoodGuard Ω l (UsPl (E := E) d) := by
  refine ⟨fun _ h => h.1, fun S hS => ?_⟩
  have hT := hS.union (Filter.eventually_cofinite.1 ((h1 E d hd).and (GlobalTheory.CongEx.eventually_not_mem_l E l)))
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hT
  refine (hD.preimage (Homeomorph.inv (G E Ω)).isOpenMap).mono ?_
  rintro g ⟨v, hv, hdeg, A, hA, hσ⟩
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
  exact ⟨v, hv.1, hv.2.1 (((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hdeg), hv.2.2, A, hA, hσ⟩

theorem joinAll_of (h1 : OneUs) (hS : SubtractQ) : JoinAll := by
  intro hT hU E Ω _ _ _ _ _ _ l _ ι hF hI d hd hsq n hn
  exact allCoreQ_of hS hT E Ω l ι hF hI _ (goodGuard_usPl h1 E Ω l d hd) (fun m hm => hU m hm E Ω l ι hF d hd hsq) n hn

end UpperTheory.Gal.Int.Core

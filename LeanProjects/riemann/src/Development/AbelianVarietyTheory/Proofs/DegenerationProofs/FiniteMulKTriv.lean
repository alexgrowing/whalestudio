import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteClosedSubschemeRepresentsKernelAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FormallyUnramifiedOfIsFinite
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyTorsionFiniteEndomorphismDivisible

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.KTrivPoints

theorem finite_mul_kTriv : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ M : LB B.left, M.IsLB → Out.RelAmple B M → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // GlobalTheory.MemKL B M x} ∧ (∀ x y : (𝟙_ (Over (Sp k)) ⟶ B), GlobalTheory.MemKL B M x → GlobalTheory.MemKL B M y → GlobalTheory.MemKL B M (x * y)) ∧ ((∀ x : (𝟙_ (Over (Sp k)) ⟶ B), GlobalTheory.MemKL B M x → x = 1) → Out.KTriv B M) := by
  intro k _ _ _ B _ hB M hM hA
  obtain ⟨H, j, hj, hfin, hH⟩ :=
    GlobalTheory.KernelRep.exists_finite_closed_kernel GlobalTheory.abelianSchemeLaws_all.1.globalFns k B hB M hM hA
  have := hB.comm
  refine ⟨?_, fun x y hx hy => GlobalTheory.UU.InK.mul hM hx hy, fun hx => ?_⟩
  · have : IsFinite (toUnit H).left := hfin
    have hf := GlobalTheory.TorsionDivisible.finite_fibre_points (toUnit H) (𝟙 _)
    refine Finite.of_surjective
      (fun z : {x : 𝟙_ (Over (Sp k)) ⟶ H // x ≫ toUnit H = 𝟙 _} =>
        (⟨z.1 ≫ j, (hH _ _).2 ⟨z.1, rfl⟩⟩ : {x : (𝟙_ (Over (Sp k)) ⟶ B) // GlobalTheory.MemKL B M x})) fun x => ?_
    obtain ⟨z, hz⟩ := (hH _ _).1 x.2
    exact ⟨⟨z, toUnit_unique _ _⟩, Subtype.ext hz⟩
  · have hm : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
    have key := GlobalTheory.FiniteOnePoint.main _ B H j hm hfin ((hH _ _).1 (GlobalTheory.memKL_one hM _))
      (fun T x y => (hH _ _).1 (GlobalTheory.UU.InK.mul hM ((hH _ _).2 ⟨x, rfl⟩)
        (GlobalTheory.UU.InK.inv hM ((hH _ _).2 ⟨y, rfl⟩))))
      k (𝟙 _) (fun x => hx _ ((hH _ _).2 ⟨x, rfl⟩))
    refine GlobalTheory.UU.kTriv_iff_forall.2 fun T x hxK => ?_
    obtain ⟨y, rfl⟩ := (hH T x).1 hxK
    exact key T (toUnit T) y

end GlobalTheory.KTrivPoints

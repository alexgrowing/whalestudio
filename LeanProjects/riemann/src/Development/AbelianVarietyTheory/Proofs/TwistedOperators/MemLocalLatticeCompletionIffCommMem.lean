import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

namespace GlobalTheory.TwistLat

theorem comm_symm_mem_intLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {a : E ⊗[F] Fv F v} (ha : a ∈ Formalism.BasicNotions.intV E v) :
    (Algebra.TensorProduct.comm F (Fv F v) E).symm a ∈ GlobalTheory.AdelicU.intLoc F E v := by
  have hle : Formalism.BasicNotions.intV E v ≤ (GlobalTheory.AdelicU.intLoc F E v).comap
      ((Algebra.TensorProduct.comm F (Fv F v) E).symm : E ⊗[F] Fv F v →+* Fv F v ⊗[F] E) := by
    unfold Formalism.BasicNotions.intV Formalism.UG.tensInt
    rw [Subring.closure_le]
    rintro z (⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩)
    · obtain ⟨x, rfl⟩ := RingHom.mem_range.1 (show e ∈ (algebraMap (𝓞 E) E).range from he)
      simp only [SetLike.mem_coe, Subring.mem_comap, RingHom.coe_coe]
      simpa using GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) (v := v) (one_mem _) x
    · simp only [SetLike.mem_coe, Subring.mem_comap, RingHom.coe_coe]
      simpa using GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) (v := v) (a := b) hb 1
  exact hle ha

theorem mem_latLoc_iff_comm_mem_locL : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E), y ∈ GlobalTheory.AdelicU.latLoc F L v ↔ (fun i => Algebra.TensorProduct.comm F (Fv F v) E (y i)) ∈ Formalism.L2.Herm.locL v L := by
  intro F E _ _ _ _ _ n L v y
  constructor
  · intro hy
    refine GlobalTheory.AdelicU.latLoc_induction
      (p := fun y => (fun i => Algebra.TensorProduct.comm F (Fv F v) E (y i)) ∈ Formalism.L2.Herm.locL v L)
      (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy
    · have hmem : ((1 : E) ⊗ₜ[F] a) ∈ Formalism.BasicNotions.intV E v :=
        Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
      have h2 := (Formalism.L2.Herm.locL v L).smul_mem ⟨_, hmem⟩
        (Submodule.subset_span ⟨x, hx, rfl⟩ : (fun i => Formalism.UG.inclE (F := F) (Fv F v) (x i)) ∈ Formalism.L2.Herm.locL v L)
      convert h2 using 1
      funext i
      simp [Formalism.UG.inclE, Subring.smul_def]
    · convert (Formalism.L2.Herm.locL v L).zero_mem using 1
      funext i; simp
    · convert (Formalism.L2.Herm.locL v L).add_mem hy hz using 1
      funext i; simp
    · convert (Formalism.L2.Herm.locL v L).neg_mem hy using 1
      funext i; simp
  · intro hy
    have key : ∀ z : Fin n → E ⊗[F] Fv F v, z ∈ Formalism.L2.Herm.locL v L →
        (fun i => (Algebra.TensorProduct.comm F (Fv F v) E).symm (z i)) ∈ GlobalTheory.AdelicU.latLoc F L v := by
      intro z hz
      unfold Formalism.L2.Herm.locL Formalism.UG.latS at hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        convert GlobalTheory.AdelicU.tmul_mem_latLoc (F := F) (v := v) (one_mem _) hx using 1
        funext i; simp [Formalism.UG.inclE]
      | zero =>
        convert (GlobalTheory.AdelicU.latLoc F L v).zero_mem using 1
        funext i; simp
      | add z w _ _ hz hw =>
        convert (GlobalTheory.AdelicU.latLoc F L v).add_mem hz hw using 1
        funext i; simp
      | smul c z _ hz =>
        have h2 := (GlobalTheory.AdelicU.latLoc F L v).smul_mem ⟨_, comm_symm_mem_intLoc v c.2⟩ hz
        convert h2 using 1
        funext i; simp [Subring.smul_def]
    convert key _ hy using 1
    funext i; simp

end GlobalTheory.TwistLat

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelSpecTensorPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCPullbackBijectiveFiniteStrictlyHenselianStatement
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep.LevelZero

variable {R : Type} [CommRing R]

theorem pull_iso_bijective {E E' : Spc} (e : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem cechC_pull_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (A' : Type) [CommRing A'] [Algebra A A'], Module.Finite A A' → ∀ (k : ℕ) (i : ℤ),
    Function.Bijective (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0) := by
  intro q _ A _ hA hq A' _ _ hfin k i
  obtain ⟨e0, e, h1, -⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  haveI := hfin
  have hT : Module.Finite A (PiTensorProduct A (fun _ : Fin (k + 1) => A')) := inferInstance
  have hr0 := GlobalTheory.T.laurentC_pullback_bijective_finite_strictlyHenselian q A hA hq (PiTensorProduct A (fun _ : Fin (k + 1) => A')) hT i
  have hmap := congrArg (fun f => disc.map f) h1
  simp only [Functor.map_comp] at hmap
  have heq : ∀ x, pull _ (disc.map e.hom) (tw q i) 0 (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0 x) =
      pull _ (spMap (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) (tw q i) 0
        (pull _ (disc.map e0.hom) (tw q i) 0 x) := by
    intro x
    rw [← pull_comp, hmap, pull_comp]
    rfl
  have hcomp : (pull _ (disc.map e.hom) (tw q i) 0) ∘ (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0) =
      (pull _ (spMap (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) (tw q i) 0) ∘
        (pull _ (disc.map e0.hom) (tw q i) 0) := funext heq
  have he : Function.Bijective (pull _ (disc.map e.hom) (tw q i) 0) :=
    pull_iso_bijective (disc.mapIso e) (tw q i) 0
  have he0 : Function.Bijective (pull _ (disc.map e0.hom) (tw q i) 0) :=
    pull_iso_bijective (disc.mapIso e0) (tw q i) 0
  rw [← Function.Bijective.of_comp_iff' he, hcomp]
  exact hr0.comp he0

end GlobalTheory.EtC.GmStep.LevelZero

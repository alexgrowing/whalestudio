import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NumberFieldGLDenseInCompletionGLTwoSidedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceBadPrimeIffCompletionStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT.Approx

open scoped TensorProduct

variable {F E : Type} {_iF : Field F} [NumberField F] {_iE : Field E} [NumberField E] {_iA : Algebra F E} {n : ℕ}

theorem comp_mul_rat (P : HeightOneSpectrum (𝓞 E)) (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E) :
    ((k⁻¹ * GlobalTheory.TwU.ratA F γ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) _).map (adAt F P) =
      ((Formalism.UG.bc (adAt F P) k)⁻¹ : GL (Fin n) (P.adicCompletion E)).1 * γ.1.map (algebraMap E (P.adicCompletion E)) := by
  rw [← map_inv, Units.val_mul, Matrix.map_mul]
  congr 1
  show (γ.1.map (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (adAt F P) = _
  rw [Matrix.map_map]
  congr 1
  funext x
  exact adAt_inclE F P x

theorem comp_rat_mul (P : HeightOneSpectrum (𝓞 E)) (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E) :
    (((GlobalTheory.TwU.ratA F γ)⁻¹ * k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) _).map (adAt F P) =
      (γ⁻¹).1.map (algebraMap E (P.adicCompletion E)) * (Formalism.UG.bc (adAt F P) k : GL (Fin n) (P.adicCompletion E)).1 := by
  rw [← map_inv, Units.val_mul, Matrix.map_mul]
  congr 1
  show ((γ⁻¹).1.map (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (adAt F P) = _
  rw [Matrix.map_map]
  congr 1
  funext x
  exact adAt_inclE F P x

end GlobalTheory.Mem.Col2.AdT.Approx

namespace GlobalTheory.Mem.Col2.AdT

theorem frNear_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (n : ℕ) (k : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), ∃ fb : SBof I a → GL (Fin n) (I.rec7 l Z).host.E, FrNear I l Z a k fb := by
  intro B X I hOk l Z a n k
  have key : ∀ P : SBof I a, ∃ γ : GL (Fin n) (I.rec7 l Z).host.E,
      GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (k⁻¹ * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F γ) ∧
      GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) ((GlobalTheory.TwU.ratA (I.rec7 l Z).host.F γ)⁻¹ * k) := by
    intro P
    obtain ⟨γ, hγ⟩ := GlobalTheory.T.numberFieldGL_dense_in_completionGL_two_sided B.fields.E P.1 n ((I.cst a).D P) (Formalism.UG.bc (adAt B.host.F P.1) k)
    refine ⟨γ, ?_, ?_⟩
    · rw [(GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a n ((I.cst a).D P) P _).2.2]
      intro r s
      have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) _ => M r s) (Approx.comp_mul_rat P.1 k γ)
      simp only [Matrix.map_apply] at h1
      have h2 := (hγ r s).1
      rw [Matrix.sub_apply] at h2
      convert h2 using 3
      exact h1
    · rw [(GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a n ((I.cst a).D P) P _).2.2]
      intro r s
      have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) _ => M r s) (Approx.comp_rat_mul P.1 k γ)
      simp only [Matrix.map_apply] at h1
      have h2 := (hγ r s).2
      rw [Matrix.sub_apply] at h2
      convert h2 using 3
      exact h1
  choose fb hfb using key
  exact ⟨fb, hfb⟩

end GlobalTheory.Mem.Col2.AdT

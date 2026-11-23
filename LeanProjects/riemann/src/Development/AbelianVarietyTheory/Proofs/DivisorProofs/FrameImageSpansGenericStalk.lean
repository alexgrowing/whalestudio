import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameCokernelP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagOfTriangularFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.VB GlobalTheory.LieFilt GlobalTheory.GrFilt
open GlobalTheory.Twist (resM)
open scoped Classical

namespace GlobalTheory

theorem span_germ_map_frame_eq_top_of_mono : ∀ {X : Scheme.{0}} [IsIntegral X] {E E' : X.Modules} {n : ℕ} (u : E ⟶ E'), Mono u → ∀ {V : X.Opens} (f : Fin n → Γ(E, V))
    (f' : Fin n → Γ(E', V)), IsFrame f → IsFrame f' → ∀ hV : genericPoint X ∈ V,
    Submodule.span X.functionField (Set.range fun i => (E'.presheaf.germ V _ hV ((u.app V (f i))) : genStalk E')) = ⊤ := by
  intro X _ E E' n u hu V f f' hf hf' hV
  let b : Module.Basis (Fin n) X.functionField (genStalk E) := hf.stalkBasis _ hV
  let b' : Module.Basis (Fin n) X.functionField (genStalk E') := hf'.stalkBasis _ hV
  let φ : genStalk E →ₗ[X.functionField] genStalk E' := QCoh.stalkLinear u (genericPoint X)
  have hφ : Function.Injective φ := QCoh.stalkLinear_injective u (genericPoint X)
  have hli : LinearIndependent X.functionField (φ ∘ b) :=
    b.linearIndependent.map' φ (LinearMap.ker_eq_bot.2 hφ)
  have heq : (fun i => (E'.presheaf.germ V _ hV ((u.app V (f i))) : genStalk E')) = φ ∘ b := by
    funext i
    have h1 : b i = E.presheaf.germ V _ hV (f i) := hf.stalkBasis_apply _ hV i
    rw [Function.comp_apply, h1]
    exact (QCoh.stalkLinear_germ u _ hV (f i)).symm
  haveI : Module.Finite X.functionField (genStalk E') := Module.Finite.of_basis b'
  rw [heq]
  exact hli.span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis b').symm

end GlobalTheory

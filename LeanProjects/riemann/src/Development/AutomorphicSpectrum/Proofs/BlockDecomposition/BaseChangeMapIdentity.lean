import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfVB

theorem bc_self (R C : Type) [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) :
    ∃ l : BC F F, ∀ T b, l.α T b = b :=
  ⟨⟨fun _ => RingHom.id _, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ => ⟨TensorProduct.lid R _, fun b => by simp [TensorProduct.lid_tmul]⟩⟩, fun _ _ => rfl⟩

end GlobalTheory.CompanionTheory.PerfVB

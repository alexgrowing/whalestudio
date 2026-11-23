import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr

open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapRho

theorem rho_add {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K]
    (C : Chain.{1} Λ A B K) {j : ℕ} (x y : ∀ n, C.S n j) (f g : Module.Dual K (C.V j) →+ B) :
    C.Rho x f → C.Rho y g → C.Rho (x + y) (f + g) := by
  rintro ⟨hf, e₁, z₁, hz₁, hb₁⟩ ⟨hg, e₂, z₂, hz₂, hb₂⟩
  refine ⟨fun k φ => by simp only [AddMonoidHom.add_apply, hf, hg, mul_add], e₁ + e₂,
    ((C.ℓ : A) ^ e₂) • z₁ + ((C.ℓ : A) ^ e₁) • z₂, fun n => ?_, fun {m} bs => ?_⟩
  · simp only [map_add, map_smul, hz₁, hz₂, Pi.add_apply]
    rw [pow_add]
    module
  · simp only [AddMonoidHom.add_apply, add_smul, Finset.sum_add_distrib, map_add,
      LinearMap.map_smulₛₗ, map_pow, map_natCast, ← hb₁ bs, ← hb₂ bs]
    rw [pow_add]
    module

end GlobalTheory.CompanionTheory.KapRho

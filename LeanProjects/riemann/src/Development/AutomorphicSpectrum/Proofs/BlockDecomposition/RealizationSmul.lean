import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr

open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapChain

theorem rho_smul : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) {j : ℕ}
    (c : Λ) (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B), C.Rho x f →
    C.Rho (c • x) ((AddMonoidHom.mulLeft (C.ι (C.lam c))).comp f) := by
  intro Λ A B K _ _ _ _ C j c x f hf
  obtain ⟨h1, e, z, h2, h3⟩ := hf
  refine ⟨?_, e, C.lam c • z, ?_, ?_⟩
  · intro k φ
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, h1]
    ring
  · intro n
    rw [map_smul, h2 n, Pi.smul_apply, LinearMap.map_smulₛₗ, smul_comm]
  · intro m bs
    rw [LinearMap.map_smulₛₗ, ← h3 bs]
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, mul_smul]
    rw [← Finset.smul_sum, smul_comm]

end GlobalTheory.CompanionTheory.KapChain

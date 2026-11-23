import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

section NM
variable {O A A' : Type} [CommRing O] [CommRing A] [CommRing A'] [Algebra O A] [Algebra O A'] {I : Ideal A} {I' : Ideal A'}
  (γ : DividedPowers I) (γ' : DividedPowers I') {X X' : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O))
  (q' : X' ⟶ Spec (CommRingCat.of O))

def nmK (σ : A →+* A') (hσ : IsDPMorphism γ γ' σ) (hO : ∀ a, σ (algebraMap O A a) = algebraMap O A' a) (u : X' ⟶ X)
    (hu : u ≫ q = q') : NMor γ q (κA O I) γ' q' (κA O I') σ where
  hI := hσ
  u := u
  g := RingHom.id O
  hu := by rw [hu, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  hκ a r h := by
    have h1 : algebraMap O A a - r ∈ I := Ideal.Quotient.eq.1 h
    have h2 : σ (algebraMap O A a - r) ∈ I' := hσ.1 (Ideal.mem_map_of_mem σ h1)
    rw [map_sub, hO] at h2
    exact Ideal.Quotient.eq.2 h2

end NM

end CrystallineSemistableComparison.Pb.Kap

import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

noncomputable section

open IsLocalRing UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.X

variable {O : Type} [CommRing O] [IsLocalRing O] {G Γ : Type} [Group G] [Group Γ] {ι : Type} (F : Frame O G Γ ι)

def etaO : Γ →* Oˣ := (Units.map (Int.castRingHom O).toMonoidHom).comp F.η

def lineChar (j : ℤ) (s : ℕ) : Γ →* Oˣ := F.Ψ ^ j * etaO F ^ s

def LineVan [TopologicalSpace Γ] (j : ℤ) (θ : Γ →* Oˣ) : Prop :=
  ∀ z : Γ → O, Coc θ z → Alg.AdicCont (maximalIdeal O) z →
    (∀ v ∉ F.Tb, ∀ s ∈ F.Nv v, z (F.loc v s) = 0) →
    (j = 0 → ∀ v ∈ F.Tb, ∀ s ∈ F.Iv v, z (F.loc v s) = 0) →
    (j < 0 → ∃ y : O, ∀ g : F.D F.vl, F.ηv F.vl g = 1 → z (F.loc _ g) = (θ (F.loc _ g) : O) * y - y) →
    CobOn θ z ⊤

end UpperTheory.V.X

end

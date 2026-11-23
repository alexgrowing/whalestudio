import Development.EtaleCohomology.KummerTheory.InjSlice

noncomputable section
open scoped TensorProduct
open GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def SHInsepLoc : Prop := ∀ (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [IsPurelyInseparable κ K] [CommRing A]
  [Algebra κ A], SH A → IsLocalRing (A ⊗[κ] K)

def SHInsepHens : Prop := ∀ (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [IsPurelyInseparable κ K] [CommRing A]
  [Algebra κ A], SH A → ∀ [IsLocalRing (A ⊗[κ] K)], HenselianLocalRing (A ⊗[κ] K)

def SHInsepRes : Prop := ∀ (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [IsPurelyInseparable κ K] [CommRing A]
  [Algebra κ A], SH A → ∀ [IsLocalRing (A ⊗[κ] K)], IsSepClosed (IsLocalRing.ResidueField (A ⊗[κ] K))

theorem SHInsep_of (hL : SHInsepLoc) (hH : SHInsepHens) (hR : SHInsepRes) : SHInsep := by
  intro κ K A _ _ _ _ _ _ hA
  have := hL κ K A hA
  exact ⟨hH κ K A hA, hR κ K A hA⟩

end LateralTheory.KummerTheory

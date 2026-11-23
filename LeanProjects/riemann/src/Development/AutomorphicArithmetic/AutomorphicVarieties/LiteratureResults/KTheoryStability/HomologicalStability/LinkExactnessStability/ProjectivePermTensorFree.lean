import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

noncomputable section

namespace GlobalTheory.HomStab

variable {k G : Type} [CommRing k] [Group G]

def freeSwap (G X ι : Type) [Group G] [MulAction G X] : (X × ι) × G ≃ (X × ι) × G where
  toFun p := ((p.2⁻¹ • p.1.1, p.1.2), p.2)
  invFun p := ((p.2 • p.1.1, p.1.2), p.2)
  left_inv p := by simp
  right_inv p := by simp

def freeLEquiv (k G X ι : Type) [CommRing k] [Group G] [MulAction G X] :
    (X →₀ ι →₀ MonoidAlgebra k G) ≃ₗ[k] ((X × ι) →₀ MonoidAlgebra k G) :=
  Finsupp.mapRange.linearEquiv (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k)) ≪≫ₗ
    (Finsupp.curryLinearEquiv k).symm ≪≫ₗ (Finsupp.curryLinearEquiv k).symm ≪≫ₗ
    Finsupp.domLCongr (freeSwap G X ι) ≪≫ₗ Finsupp.curryLinearEquiv k ≪≫ₗ
    Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k).symm

theorem freeLEquiv_single (X ι : Type) [MulAction G X] (x : X) (i : ι) (g : G) (r : k) :
    freeLEquiv k G X ι (Finsupp.single x (Finsupp.single i (MonoidAlgebra.single g r))) =
      Finsupp.single (g⁻¹ • x, i) (MonoidAlgebra.single g r) := by
  simp [freeLEquiv, freeSwap]

def permFreeIso (k G : Type) [CommRing k] [Group G] (X ι : Type) [MulAction G X] :
    permT X (Rep.free k G ι) ≅ Rep.free k G (X × ι) :=
  Rep.mkIso { freeLEquiv k G X ι with
    isIntertwining' := fun h => by
      ext x i g : 4
      simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, MonoidAlgebra.lsingle_apply]
      rw [permRep_single]
      erw [Representation.free_single_single]
      simp [freeLEquiv_single, Representation.free_single_single, mul_smul] }

theorem main : ∀ (k G : Type) [CommRing k] [Group G] (X ι : Type) [MulAction G X],
    Projective (permT X (Rep.free k G ι)) := by
  intro k G _ _ X ι _
  exact Projective.of_iso (permFreeIso k G X ι).symm inferInstance

end GlobalTheory.HomStab

end

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.projective_perm_tensor_free : ∀ (k G : Type) [CommRing k] [Group G] (X ι : Type) [MulAction G X], Projective (permT X (Rep.free k G ι)) := by
  first
  | exact @GlobalTheory.HomStab.main
  | exact @GlobalTheory.HomStab.freeLEquiv_single
end

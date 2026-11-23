import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NaturalPointwiseCochainConstOfGlobalSectionsBaseStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem isSymCoc_of_isAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (f : Fn1 A) (g : Fn2 A), IsAdd f g → IsSymCoc g := by
  intro R _ A _ hA f g hfg
  have hc : IsCommMonObj A := hA.comm
  intro D _ _
  constructor
  · let k : Fn0 (A ⊗ A) := fun E _ _ w ↦
      g E (w ≫ fst A A) (w ≫ snd A A) - g E (w ≫ snd A A) (w ≫ fst A A)
    have hk : IsCob (whole (A ⊗ A)) (Fn1.zero (A ⊗ A)) k := by
      intro E _ _ E' _ _ φ w _
      have h1 := hfg E E' φ (w ≫ fst A A) (w ≫ snd A A)
      have h2 := hfg E E' φ (w ≫ snd A A) (w ≫ fst A A)
      rw [mul_comm (w ≫ snd A A) (w ≫ fst A A)] at h2
      simp only [k, Fn1.zero, Category.assoc, map_sub]
      linear_combination h2 - h1
    obtain ⟨r, hr⟩ := GlobalTheory.T.natural_pointwiseCochain_const_of_globalSections_base R (A ⊗ A) Unit (whole (A ⊗ A)) (by simp [whole])
      (GlobalTheory.globalFns_holds (Sp R) (A ⊗ A)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA)).2 k hk
    intro x y
    have e1 := hr D (lift x y) (sm_whole _)
    have e0 := hr D (lift 1 1) (sm_whole _)
    simp only [k, lift_fst, lift_snd, sub_self] at e0 e1
    exact sub_eq_zero.mp (e1.trans e0.symm)
  · let k : Fn0 (A ⊗ (A ⊗ A)) := fun E _ _ w ↦
      g E (w ≫ snd _ _ ≫ fst A A) (w ≫ snd _ _ ≫ snd A A)
        - g E ((w ≫ fst _ _) * (w ≫ snd _ _ ≫ fst A A)) (w ≫ snd _ _ ≫ snd A A)
        + g E (w ≫ fst _ _) ((w ≫ snd _ _ ≫ fst A A) * (w ≫ snd _ _ ≫ snd A A))
        - g E (w ≫ fst _ _) (w ≫ snd _ _ ≫ fst A A)
    have hk : IsCob (whole (A ⊗ (A ⊗ A))) (Fn1.zero _) k := by
      intro E _ _ E' _ _ φ w _
      have h1 := hfg E E' φ (w ≫ snd _ _ ≫ fst A A) (w ≫ snd _ _ ≫ snd A A)
      have h2 := hfg E E' φ ((w ≫ fst _ _) * (w ≫ snd _ _ ≫ fst A A)) (w ≫ snd _ _ ≫ snd A A)
      have h3 := hfg E E' φ (w ≫ fst _ _) ((w ≫ snd _ _ ≫ fst A A) * (w ≫ snd _ _ ≫ snd A A))
      have h4 := hfg E E' φ (w ≫ fst _ _) (w ≫ snd _ _ ≫ fst A A)
      rw [_root_.mul_assoc] at h2
      simp only [MonObj.comp_mul] at h2 h3
      simp only [k, Fn1.zero, Category.assoc, map_sub, map_add, MonObj.comp_mul]
      linear_combination h2 - h1 - h3 + h4
    obtain ⟨r, hr⟩ := GlobalTheory.T.natural_pointwiseCochain_const_of_globalSections_base R (A ⊗ (A ⊗ A)) Unit (whole _) (by simp [whole])
      (GlobalTheory.globalFns_holds (Sp R) (A ⊗ (A ⊗ A))
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A (A ⊗ A) hA
          (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA))).2 k hk
    intro x y z
    have e1 := hr D (lift x (lift y z)) (sm_whole _)
    have e0 := hr D (lift 1 (lift 1 1)) (sm_whole _)
    simp only [k, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, _root_.mul_one, sub_self, add_sub_cancel_right,
      sub_add_cancel] at e0 e1
    rw [← e0] at e1
    exact e1

end GlobalTheory.PtExt

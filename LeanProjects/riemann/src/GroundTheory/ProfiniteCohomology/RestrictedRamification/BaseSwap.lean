import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseReverse
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFormal
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

attribute [local instance 2000] Rep.hV2

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {n : ℕ} (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D] (hD : ∀ d : D, n • d = 0)

theorem neg_one_pow_one_mul_two_smul {R M : Type*} [Ring R] {_ : AddCommGroup M} {_ : Module R M} (x : M) :
    ((-1 : R) ^ (1 * 2)) • x = x := by
  rw [show (1 * 2 : ℕ) = 2 from rfl, neg_one_sq, one_smul]

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep D] in
theorem braiding_comp_zmodMulPairingRight :
    (β_ (zmodRep.{u} G n) D).hom ≫ zmodMulPairingRight n D hD = zmodMulPairing n D hD := by
  rw [zmodMulPairingRight, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

theorem compactCupRes_zmodMulPairingRight_swap
    (hsurj : Function.Surjective
      (localToCompact φ D (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 2).hom)
    (yc : compactCohomologyRes φ D 1) (xc : compactCohomologyRes φ (zmodRep.{u} G n) 2) :
    compactCupRes φ (zmodMulPairingRight n D hD) (show 1 + 2 = 3 from rfl) yc
        ((compactToGlobal φ _ (fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n)) (fun _ => 𝟙 _) 2).hom xc) =
      compactCupRes φ (zmodMulPairing n D hD) (show 2 + 1 = 3 from rfl) xc
        ((compactToGlobal φ D (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 1).hom yc) := by
  refine (compactCupRes_eq_neg_one_pow_smul_compactCupRightRes φ (zmodMulPairingRight n D hD) hsurj
    (show 1 + 2 = 3 from rfl) (show 2 + 1 = 3 from rfl) le_rfl (by norm_num) yc _).trans ?_
  refine (neg_one_pow_one_mul_two_smul _).trans ?_
  refine (congrArg (fun μ => compactCupRightRes φ μ (show 2 + 1 = 3 from rfl)
    ((compactToGlobal φ _ (fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n)) (fun _ => 𝟙 _) 2).hom xc) yc)
    (braiding_comp_zmodMulPairingRight D hD)).trans ?_
  exact (compactCup_eq_compactCupRight (Aᵥ := fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n))
    (Bᵥ := fun v => Rep.res (φ v).toMonoidHom D) (Cᵥ := fun v => Rep.res (φ v).toMonoidHom D)
    (a := fun _ => 𝟙 _) (b := fun _ => 𝟙 _) (c := fun _ => 𝟙 _) φ (zmodMulPairing n D hD)
    (fun v => pairingRes (φ v).toMonoidHom (zmodMulPairing n D hD))
    (fun v => pairingRes (φ v).toMonoidHom (zmodMulPairing n D hD))
    (fun v => pairingRes (φ v).toMonoidHom (zmodMulPairing n D hD))
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom (zmodMulPairing n D hD))
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom (zmodMulPairing n D hD))
    (fun _ => by rw [MonoidalCategory.id_tensorHom_id, Category.id_comp])
    (fun _ => by rw [MonoidalCategory.id_tensorHom_id, Category.id_comp])
    (show 2 + 1 = 3 from rfl) xc yc).symm

end GroundTheory.ProfCoh

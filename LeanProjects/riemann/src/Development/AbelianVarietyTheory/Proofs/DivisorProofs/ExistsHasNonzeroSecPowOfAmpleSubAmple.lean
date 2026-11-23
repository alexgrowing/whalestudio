import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicMorseExistsSectionAmpleSubGeneratedStatement

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem exists_hasNonzeroSec_pow_of_ample_sub_ample : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsAmpleLB B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  intro k _ _ X _ _ hX d hdim L B M hL hB hM hcls hineq

  have hgen : ∀ᶠ n : ℕ in atTop, IsGenerated (lbPow B n) := by
    filter_upwards [hB.eventually_isGloballyGenerated_twist (LB.unitMod X)] with n hn
    obtain ⟨ι, hι, φ, hφ⟩ := hn
    exact (isGloballyGenerated_toMod_iff (isLB_lbPow hB.isLB n)).1
      ⟨ι, hι, φ ≫ (unitTwistIso (X := X) (L := lbPow B n)).hom, epi_comp _ _⟩
  obtain ⟨m, hmB, hm1⟩ := (hgen.and (eventually_ge_atTop 1)).exists

  have hLm : IsAmpleLB (lbPow L m) := (isAmpleLB_basic.2.1 hL.isLB hm1).2 hL
  have hMm : (lbPow M m).IsLB := isLB_lbPow hM m
  have hclsm : cls (lbPow L m) hLm.isLB = cls (lbPow M m) hMm + cls (lbPow B m) hmB.isLB := by
    rw [CechPic.cls_lbPow hL.isLB m, CechPic.cls_lbPow hM m, CechPic.cls_lbPow hB.isLB m, hcls,
      smul_add]

  have hv : DiffVanish (d + 1 + 1) (chiPic k (structureModule X)) := by
    apply diffVanish_chiPic_of_isProjOver (f := strHom k X) (algebraMap_eq_strHom k X) _ hX
    unfold QCoh.suppDim
    exact (topologicalKrullDim_subspace_le _ _).trans hdim
  have hprod : (∏ _i : Fin (d + 1), (m : ℤ)) = (m : ℤ) ^ (d + 1) := by simp
  have hP : ∀ i, ((Fin.cons B fun _ : Fin d => L : Fin (d + 1) → LB X) i).IsLB := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hB.isLB
    · exact hL.isLB
  have hQ : ∀ i, ((Fin.cons (lbPow B m) fun _ : Fin d => lbPow L m : Fin (d + 1) → LB X) i).IsLB := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hmB.isLB
    · exact hLm.isLB
  have hI : interNum k (structureModule X)
      (Fin.cons (lbPow B m) fun _ : Fin d => lbPow L m : Fin (d + 1) → LB X) =
      (m : ℤ) ^ (d + 1) * interNum k (structureModule X)
        (Fin.cons B fun _ : Fin d => L : Fin (d + 1) → LB X) := by
    rw [← hprod]
    refine hv.interNum_of_cls_eq_zsmul hP hQ (fun _ => (m : ℤ)) ?_
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (CechPic.cls_lbPow hB.isLB m _).trans (natCast_zsmul _ _).symm
    · exact (CechPic.cls_lbPow hL.isLB m _).trans (natCast_zsmul _ _).symm
  have hT : topSelfIntersection k (lbPow L m) (d + 1) = (m : ℤ) ^ (d + 1) * topSelfIntersection k L (d + 1) := by
    rw [topSelf_def, topSelf_def, ← hprod]
    exact hv.interNum_of_cls_eq_zsmul (fun _ => hL.isLB) (fun _ => hLm.isLB) (fun _ => (m : ℤ))
      (fun _ => (CechPic.cls_lbPow hL.isLB m _).trans (natCast_zsmul _ _).symm)
  have hpos : (0 : ℤ) < (m : ℤ) ^ (d + 1) := pow_pos (by exact_mod_cast hm1) _
  have hineqm : ((d : ℤ) + 1) * interNum k (structureModule X)
      (Fin.cons (lbPow B m) fun _ : Fin d => lbPow L m : Fin (d + 1) → LB X) <
      topSelfIntersection k (lbPow L m) (d + 1) := by
    rw [hI, hT, mul_left_comm]
    exact mul_lt_mul_of_pos_left hineq hpos

  obtain ⟨r, hr, hs⟩ :=
    T.algebraic_morse_exists_section_ample_sub_generated k X hX d hdim (lbPow L m) (lbPow B m) (lbPow M m) hLm hmB hMm hclsm hineqm
  refine ⟨m * r, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  refine hs.of_cls_eq (isLB_lbPow hM (m * r)) (isLB_lbPow hMm r) ?_
  rw [CechPic.cls_lbPow hM (m * r), CechPic.cls_lbPow hMm r, CechPic.cls_lbPow hM m, smul_smul,
    mul_comm]

end GlobalTheory

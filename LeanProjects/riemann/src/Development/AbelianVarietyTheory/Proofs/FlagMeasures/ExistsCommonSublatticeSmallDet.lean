import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLatticeDiscriminantModuleCardDetSq

namespace GlobalTheory.LoopC.CommonSub

section General

open NumberField

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V] [Module K V]

theorem span_eq_of_relIndex_ne_zero {P M : Submodule (𝓞 K) V} (hPM : P ≤ M)
    (h : P.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0) :
    Submodule.span K (P : Set V) = Submodule.span K (M : Set V) := by
  refine le_antisymm (Submodule.span_mono hPM) ?_
  rw [Submodule.span_le]
  intro m hm

  have hn : (P.toAddSubgroup.relIndex M.toAddSubgroup) • m ∈ P :=
    AddSubgroup.nsmul_relIndex_mem P.toAddSubgroup (K := M.toAddSubgroup) hm
  have hnK : ((P.toAddSubgroup.relIndex M.toAddSubgroup : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr h
  have hm' : m = ((P.toAddSubgroup.relIndex M.toAddSubgroup : ℕ) : K)⁻¹ •
      (P.toAddSubgroup.relIndex M.toAddSubgroup • m) := by
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hnK, one_smul]
  rw [SetLike.mem_coe, hm']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hn)

omit [NumberField K] [Module K V] in
theorem relIndex_inf_bound {M A' A'' B' B'' : Submodule (𝓞 K) V} (h1 : M ≤ A') (h2 : M ≤ A'')
    (n1 : B'.toAddSubgroup.relIndex A'.toAddSubgroup ≠ 0)
    (n2 : B''.toAddSubgroup.relIndex A''.toAddSubgroup ≠ 0) :
    ((B' ⊓ B'') ⊓ M).toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 ∧
    ((B' ⊓ B'') ⊓ M).toAddSubgroup.relIndex M.toAddSubgroup ≤
      B'.toAddSubgroup.relIndex A'.toAddSubgroup * B''.toAddSubgroup.relIndex A''.toAddSubgroup := by
  have e : ((B' ⊓ B'') ⊓ M).toAddSubgroup.relIndex M.toAddSubgroup =
      (B'.toAddSubgroup ⊓ B''.toAddSubgroup).relIndex M.toAddSubgroup :=
    AddSubgroup.inf_relIndex_right (B'.toAddSubgroup ⊓ B''.toAddSubgroup) M.toAddSubgroup
  have h1' : M.toAddSubgroup ≤ A'.toAddSubgroup := fun x hx => h1 hx
  have h2' : M.toAddSubgroup ≤ A''.toAddSubgroup := fun x hx => h2 hx

  have m1 : B'.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 :=
    mt (AddSubgroup.relIndex_eq_zero_of_le_right h1') n1
  have m2 : B''.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 :=
    mt (AddSubgroup.relIndex_eq_zero_of_le_right h2') n2
  rw [e]
  refine ⟨AddSubgroup.relIndex_inf_ne_zero m1 m2, ?_⟩
  calc (B'.toAddSubgroup ⊓ B''.toAddSubgroup).relIndex M.toAddSubgroup
      ≤ B'.toAddSubgroup.relIndex M.toAddSubgroup * B''.toAddSubgroup.relIndex M.toAddSubgroup :=
        AddSubgroup.relIndex_inf_le
    _ ≤ _ := Nat.mul_le_mul (AddSubgroup.relIndex_le_of_le_right h1' n1)
        (AddSubgroup.relIndex_le_of_le_right h2' n2)

end General

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem idxW_eq (D : D7) (A B : LatW D) : idxW D A B = B.toAddSubgroup.relIndex A.toAddSubgroup := rfl

theorem main : ∀ (D : D7) (L M A' A'' B' B'' : LatW D), IsPosDef (D.sp.X 0).hT → L.FG → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT L → M ≤ A' → M ≤ A'' → A' ≤ L → A'' ≤ L → B' ≤ A' → B'' ≤ A'' → rkW D B' = rkW D A' → rkW D B'' = rkW D A'' → ∃ P : LatW D, P ≤ M ∧ P ≤ B' ∧ P ≤ B'' ∧ rkW D P = rkW D M ∧ detW D P ≤ detW D M * (idxW D A' B' : ℝ) * (idxW D A'' B'' : ℝ) := by
  intro D L M A' A'' B' B'' hPD hL hI hMA' hMA'' hA'L hA''L hB' hB'' r1 r2
  have hfg : ∀ N : LatW D, N ≤ L → N.FG := fun N hN => Submodule.FG.of_le hL hN
  have hint : ∀ N : LatW D, N ≤ L → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT N :=
    fun N hN x hx y hy => hI x (hN hx) y (hN hy)

  have k1 := ((GlobalTheory.LoopC.DetCard.main D A' (hfg _ hA'L) hPD (hint _ hA'L)).2.2 B' hB' r1).1
  have k2 := ((GlobalTheory.LoopC.DetCard.main D A'' (hfg _ hA''L) hPD (hint _ hA''L)).2.2 B'' hB'' r2).1
  rw [idxW_eq] at k1 k2
  obtain ⟨n0, nle⟩ := relIndex_inf_bound (K := D.host.E) hMA' hMA''
    (Nat.one_le_iff_ne_zero.mp k1) (Nat.one_le_iff_ne_zero.mp k2)
  have hrk : rkW D ((B' ⊓ B'') ⊓ M) = rkW D M := by
    unfold rkW
    rw [span_eq_of_relIndex_ne_zero (K := D.host.E) inf_le_right n0]
  have hML : M ≤ L := hMA'.trans hA'L
  have k3 := (GlobalTheory.LoopC.DetCard.main D M (hfg _ hML) hPD (hint _ hML)).2.2 _ inf_le_right hrk
  refine ⟨(B' ⊓ B'') ⊓ M, inf_le_right, fun x hx => hx.1.1, fun x hx => hx.1.2, hrk, ?_⟩
  have hd : 0 ≤ detW D M := Real.sqrt_nonneg _
  rw [k3.2, mul_assoc, idxW_eq, idxW_eq, idxW_eq]
  gcongr
  exact_mod_cast nle

end GlobalTheory.LoopC.CommonSub

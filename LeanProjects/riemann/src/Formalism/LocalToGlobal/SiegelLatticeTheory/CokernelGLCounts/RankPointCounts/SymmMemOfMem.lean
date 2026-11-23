import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnitaryNormalVectorCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TauExists

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Grp

variable {D : D7} {T : D.host.E} (F : LFlag (VS D) D.R.rS T)

theorem symm_mem_of_mem (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Submodule D.host.E (VS D).V)
    (h : ∀ x ∈ U, s x ∈ U) : ∀ x ∈ U, s.symm x ∈ U := by
  intro x hx
  let f : U →ₗ[D.host.E] U :=
    (s : (VS D).V →ₗ[D.host.E] (VS D).V).restrict (p := U) (q := U) (fun y hy => h y hy)
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply s.injective
    exact congrArg Subtype.val hab
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨x, hx⟩
  have hyx : s y.1 = x := congrArg Subtype.val hy
  rw [← hyx, LinearEquiv.symm_apply_apply]
  exact y.2

theorem Xflag_mono (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  exact Formalism.L2.SG.Pf.xflag_mono_td F (Nat.le_succ j)

theorem Xflag_le_X (j : ℕ) : Xflag F j ≤ Xsp F := by
  exact PI.DCRelEquiv.UnitaryGroupMassFormula.Xflag_le_X F j

theorem X_eq_Xflag : Xsp F = Xflag F D.R.rS := by
  exact (Formalism.L2.SG.Pf.xflag_r F).symm

theorem flag_pres {s : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : ∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j)
    (j : ℕ) : ∀ x ∈ Xflag F j, s x ∈ Xflag F j := by
  intro x hx
  cases j with
  | zero =>
    rw [Formalism.L2.SG.Pf.xflag_zero_td F, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact Submodule.zero_mem _
  | succ j =>
    have h1 := Xflag_mono F j (hs j x hx)
    have h2 := Submodule.add_mem _ h1 hx
    rwa [sub_add_cancel] at h2

theorem flag_inv {s : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : ∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j) :
    ∀ j, ∀ x ∈ Xflag F (j + 1), s.symm x - x ∈ Xflag F j := by
  intro j x hx
  have hy : s.symm x ∈ Xflag F (j + 1) :=
    symm_mem_of_mem s (Xflag F (j + 1)) (flag_pres F hs (j + 1)) x hx
  have h1 := hs j (s.symm x) hy
  rw [LinearEquiv.apply_symm_apply] at h1
  have h2 := Submodule.neg_mem _ h1
  rwa [neg_sub] at h2

theorem flag_mul {s t : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hs : ∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j) (ht : ∀ j, ∀ x ∈ Xflag F (j + 1), t x - x ∈ Xflag F j) :
    ∀ j, ∀ x ∈ Xflag F (j + 1), (s * t) x - x ∈ Xflag F j := by
  intro j x hx
  have htx : t x ∈ Xflag F (j + 1) := flag_pres F ht (j + 1) x hx
  have h1 := Submodule.add_mem _ (hs j (t x) htx) (ht j x hx)
  show s (t x) - x ∈ Xflag F j
  rwa [sub_add_sub_cancel] at h1

theorem X_pres {s : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : ∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j) :
    ∀ x ∈ Xsp F, s x ∈ Xsp F := by
  intro x hx
  rw [X_eq_Xflag F] at hx ⊢
  exact flag_pres F hs _ x hx

theorem SRat_inv {s : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : s ∈ SRat F) : s.symm ∈ SRat F := by
  simp only [SRat, Set.mem_setOf_eq] at hs ⊢
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hs.1, flag_inv F hs.2.1, ?_⟩
  have h1 := symm_mem_of_mem s (Xsp F) (X_pres F hs.2.1) _ hs.2.2
  have h2 := Submodule.neg_mem _ h1
  rw [map_sub, LinearEquiv.symm_apply_apply, neg_sub] at h2
  exact h2

theorem SRat_mul {s t : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : s ∈ SRat F) (ht : t ∈ SRat F) : s * t ∈ SRat F := by
  simp only [SRat, Set.mem_setOf_eq] at hs ht ⊢
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hs.1 ht.1, flag_mul F hs.2.1 ht.2.1, ?_⟩
  have hw := ht.2.2
  have hsw := X_pres F hs.2.1 _ hw
  have key : (s * t) F.fl.z - F.fl.z = (s F.fl.z - F.fl.z) +
      (s (t F.fl.z - F.fl.z) - (t F.fl.z - F.fl.z)) + (t F.fl.z - F.fl.z) := by
    show s (t F.fl.z) - F.fl.z = _
    rw [map_sub]; abel
  rw [key]
  exact Submodule.add_mem _ (Submodule.add_mem _ hs.2.2 (Submodule.sub_mem _ hsw hw)) hw

theorem perp_pres {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hX : ∀ x ∈ Xsp F, n.symm x ∈ Xsp F) : ∀ y ∈ orth (VS D) (Xsp F), n y ∈ orth (VS D) (Xsp F) := by
  have hi' : ∀ a b, (VS D).hT (n a) (n b) = (VS D).hT a b := hi
  intro y hy
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
  intro x hx
  have h1 := hi' (n.symm x) y
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [h1]
  exact hy _ (hX x hx)

theorem NRat_inv {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) : n.symm ∈ NRat F := by
  simp only [NRat, Set.mem_setOf_eq] at hn ⊢
  have hX : ∀ x ∈ Xsp F, n.symm x ∈ Xsp F := symm_mem_of_mem n (Xsp F) (X_pres F hn.2.1)
  have hO := perp_pres F hn.1 hX
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hn.1, flag_inv F hn.2.1, ?_⟩
  intro x hx
  have hy := symm_mem_of_mem n (orth (VS D) (Xsp F)) hO x hx
  have h2 := Submodule.neg_mem _ (hn.2.2 _ hy)
  rw [LinearEquiv.apply_symm_apply, neg_sub] at h2
  exact h2

theorem NRat_mul {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) (hm : m ∈ NRat F) : n * m ∈ NRat F := by
  simp only [NRat, Set.mem_setOf_eq] at hn hm ⊢
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hn.1 hm.1, flag_mul F hn.2.1 hm.2.1, ?_⟩
  intro x hx
  have hw := hm.2.2 x hx
  have hnw := X_pres F hn.2.1 _ hw
  have key : (n * m) x - x = (n x - x) + (n (m x - x) - (m x - x)) + (m x - x) := by
    show n (m x) - x = _
    rw [map_sub]; abel
  rw [key]
  exact Submodule.add_mem _ (Submodule.add_mem _ (hn.2.2 x hx) (Submodule.sub_mem _ hnw hw)) hw

end Grp

end Formalism.L2.SG.NGCut.NormalVectorPairings

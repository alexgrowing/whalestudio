import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorEqPointMinor

noncomputable section

open Module
open Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem X_le_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') : F.fl.X ≤ UUE Λ F F' := by
  exact (Formalism.MainNotions.LatticeGluingRadicals.a_X_le (Formalism.MainNotions.LatticeGluingRadicals.a_HU Λ hΛ F F' hL.2 hL'.2)).1

theorem X'_le_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') : F'.fl.X ≤ UUE Λ F F' := by
  exact (Formalism.MainNotions.LatticeGluingRadicals.a_X_le (Formalism.MainNotions.LatticeGluingRadicals.a_HU Λ hΛ F F' hL.2 hL'.2)).2

theorem z_mem_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') : F.fl.z ∈ UUE Λ F F' := by
  rw [← hL.2]
  exact Submodule.subset_span (Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))))

theorem z'_mem_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') : F'.fl.z ∈ UUE Λ F F' := by
  rw [← hL'.2]
  exact Submodule.subset_span (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))

theorem yv_mem_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') :
    yv F.fl F'.fl ∈ UUE Λ F F' := by
  have hf : ∀ b, F'.fl.fvec b ∈ UUE Λ F F' := by
    intro b
    refine Fin.lastCases ?_ (fun i => ?_) b
    · rw [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
      exact z'_mem_UUE Λ hΛ F F' hL hL'
    · rw [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
      exact X'_le_UUE Λ hΛ F F' hL hL' (Submodule.subset_span ⟨i, rfl⟩)
  unfold yv omp
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (hf b))) (Submodule.smul_mem _ _ (z_mem_UUE Λ hΛ F F' hL hL'))

theorem hT_Hp_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (F : LFlag S r T) (F' : LFlag S r T')
    {h v : S.V} (hh : h ∈ Hp Λ F F') (hv : v ∈ UUE Λ F F') : S.hT h v = 0 := by
  rw [hT_swap v h, Formalism.L2.SG.NGCut.CorankRelation.hT_eq_zero_of_mem_Hp Λ F F' hh hv, star_zero]

theorem hT_UUE_Hp (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (F : LFlag S r T) (F' : LFlag S r T')
    {h v : S.V} (hh : h ∈ Hp Λ F F') (hv : v ∈ UUE Λ F F') : S.hT v h = 0 :=
  Formalism.L2.SG.NGCut.CorankRelation.hT_eq_zero_of_mem_Hp Λ F F' hh hv

theorem hT_X_yv (F : FlagG S r T) (F' : FlagG S r T') {x : S.V} (hx : x ∈ F.X) : S.hT x (yv F F') = 0 := by
  have hker : F.X ≤ LinearMap.ker (S.hT (yv F F')) := by
    rw [Formalism.MainNotions.S.FlagG.X, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hT_swap]
    have h := brS_yv_e (F := F) (F' := F') a
    rw [Formalism.MainNotions.S.brS] at h
    rw [h, star_zero]
  have h1 : S.hT (yv F F') x = 0 := hker hx
  rw [hT_swap, h1, star_zero]

theorem hT_z_yv (F : FlagG S r T) (F' : FlagG S r T') : S.hT F.z (yv F F') = 0 := by
  have h := pairing_yVector_z (F := F) (F' := F')
  rwa [Formalism.MainNotions.S.brS] at h

theorem UUE_symm (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    UUE Λ F' F = UUE Λ F F' := by
  unfold Formalism.MainNotions.S.Lat.UUE Formalism.MainNotions.S.Lat.UU
  congr 1
  ac_rfl

theorem Hp_symm (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    Hp Λ F' F = Hp Λ F F' := by
  unfold Formalism.MainNotions.S.Lat.Hp
  rw [UUE_symm]

theorem line_pair (k : ℕ) (hdim : finrank E S.V = k + 2 * r + 1) (Λ : Submodule (NumberField.RingOfIntegers E) S.V)
    (hΛ : Submodule.IsLattice E Λ) (Fl : LFlag S r T) (F1 F2 : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hL : IsLift Λ Fl) (hL1 : IsLift Λ F1) (hL2 : IsLift Λ F2) (hG1 : Gval Fl F1 ≠ 0) (hG12 : Gval Fl F2 = Gval Fl F1)
    (hT : T ≠ 0) (hTs : star T = T) (hTh : Th Λ Fl F1 F2 β = Hp Λ Fl F1) :
    yv Fl.fl F2.fl - (brS S (yv Fl.fl F2.fl) (yv Fl.fl F1.fl) / brS S (yv Fl.fl F1.fl) (yv Fl.fl F1.fl)) •
        yv Fl.fl F1.fl ∈ Fl.fl.X ∧
      (brS S (yv Fl.fl F2.fl) (yv Fl.fl F1.fl) / brS S (yv Fl.fl F1.fl) (yv Fl.fl F1.fl)) *
        star (brS S (yv Fl.fl F2.fl) (yv Fl.fl F1.fl) / brS S (yv Fl.fl F1.fl) (yv Fl.fl F1.fl)) = 1 := by
  set y1 := yv Fl.fl F1.fl with hy1
  set y2 := yv Fl.fl F2.fl with hy2
  set c := brS S y2 y1 / brS S y1 y1 with hc
  have hG1' : Formalism.MainNotions.S.Gflag Fl.fl F1.fl ≠ 0 := hG1
  have hb1 : brS S y1 y1 ≠ 0 := by
    rw [hy1, brS_yv_yv Fl.fl F1.fl hTs]
    exact mul_ne_zero hT hG1'
  have hb12 : brS S y2 y2 = brS S y1 y1 := by
    rw [hy1, hy2, brS_yv_yv Fl.fl F2.fl hTs, brS_yv_yv Fl.fl F1.fl hTs]
    exact congrArg (T * ·) hG12
  obtain ⟨hfin, hk1⟩ := Formalism.L2.SG.NGCut.CorankRelation.finrank_Hp k hdim Λ hΛ Fl F1 hL hL1 hG1

  have hy2H : ∀ h ∈ Hp Λ Fl F1, S.hT h y2 = 0 := by
    intro h hh
    rw [← hTh] at hh
    unfold Formalism.MainNotions.S.Lat.Th at hh
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hh
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_ThPairs] at hp
    obtain ⟨-, hp2, hpX, -⟩ := hp
    have e : p.1 = (p.1 - p.2) + p.2 := by abel
    simp only [LinearMap.fst_apply]
    rw [e, map_add, LinearMap.add_apply, hT_X_yv Fl.fl F2.fl hpX,
      hT_Hp_UUE Λ Fl F2 hp2 (yv_mem_UUE Λ hΛ Fl F2 hL hL2), add_zero]
  have hv : y2 - c • y1 ∈ Fl.fl.X := by
    refine Formalism.L2.SG.NGCut.NormalVectorPairings.line Fl.fl hT (Hp Λ Fl F1) ?_ ?_ ?_ ?_ ?_ hb1 ?_ ?_
    · intro x hx h hh
      exact hT_UUE_Hp Λ Fl F1 hh (X_le_UUE Λ hΛ Fl F1 hL hL1 hx)
    · intro h hh
      exact hT_UUE_Hp Λ Fl F1 hh (z_mem_UUE Λ hΛ Fl F1 hL hL1)
    · intro x hx hxH
      exact Formalism.L2.SG.NGCut.CorankRelation.Xsp_Hp_eq_zero Λ hΛ Fl F1 hL hL1 hG1 hx hxH
    · omega
    · rw [Formalism.L2.SG.NGCut.NormalVectorPairings.mem_Qsp]
      exact ⟨fun x hx => hT_X_yv Fl.fl F1.fl hx, hT_z_yv Fl.fl F1.fl,
        fun h hh => hT_Hp_UUE Λ Fl F1 hh (yv_mem_UUE Λ hΛ Fl F1 hL hL1)⟩
    · rw [Formalism.L2.SG.NGCut.NormalVectorPairings.mem_Qsp]
      refine ⟨fun x hx => ?_, ?_, fun h hh => ?_⟩
      · rw [map_sub, map_smul, hT_X_yv Fl.fl F2.fl hx, hT_X_yv Fl.fl F1.fl hx, smul_zero, sub_zero]
      · rw [map_sub, map_smul, hT_z_yv, hT_z_yv, smul_zero, sub_zero]
      · rw [map_sub, map_smul, hy2H h hh, hT_Hp_UUE Λ Fl F1 hh (yv_mem_UUE Λ hΛ Fl F1 hL hL1),
          smul_zero, sub_zero]
    · rw [sub_eq_add_neg, ← neg_smul, brS_add_left, brS_smul_left, hc]
      field_simp
      ring
  refine ⟨hv, ?_⟩

  set x := y2 - c • y1 with hx
  have hy2x : y2 = x + c • y1 := by
    rw [hx]
    abel
  have hxx : brS S x x = 0 := by
    rw [Formalism.MainNotions.S.brS]
    exact hT_X_X Fl.fl hv hv
  have hyx : brS S y1 x = 0 := by
    rw [Formalism.MainNotions.S.brS]
    exact hT_X_yv Fl.fl F1.fl hv
  have hxy : brS S x y1 = 0 := by
    rw [Formalism.MainNotions.S.brS, hT_swap, hT_X_yv Fl.fl F1.fl hv, star_zero]
  have hmod : brS S y2 y2 = c * star c * brS S y1 y1 := by
    rw [hy2x, brS_add_left, brS_add_right, brS_add_right, brS_smul_left, brS_smul_left,
      brS_smul_right, brS_smul_right, hxx, hxy, hyx]
    ring
  rw [hb12] at hmod
  have h1 : (1 : E) * brS S y1 y1 = c * star c * brS S y1 y1 := by rw [one_mul]; exact hmod
  exact (mul_right_cancel₀ hb1 h1).symm

end Formalism.L2.SG.NGCut.NormalVectorPairings

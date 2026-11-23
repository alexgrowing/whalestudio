import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.CompleteIntegralClosure

open Polynomial

theorem UpperTheory.isAdicComplete_adjoinRoot_of_monic :
    ∀ (O : Type) [CommRing O] (m : Ideal O) [IsAdicComplete m O] (f : O[X]), f.Monic → IsAdicComplete (m.map (AdjoinRoot.of f)) (AdjoinRoot f) := by
  intro O _ m _ f hf
  let pb := AdjoinRoot.powerBasis' hf
  have key : ∀ (n : ℕ) (x : AdjoinRoot f),
      x ∈ ((m.map (AdjoinRoot.of f)) ^ n • (⊤ : Submodule (AdjoinRoot f) (AdjoinRoot f))) ↔
        x ∈ (m ^ n • (⊤ : Submodule O (AdjoinRoot f))) := by
    intro n x
    rw [GroundTheory.Arith.Abelian.mem_ideal_smul_top_self_iff, ← Ideal.map_pow, Ideal.smul_top_eq_map,
      Submodule.restrictScalars_mem, AdjoinRoot.algebraMap_eq]
  have hs : ∀ n (x y : AdjoinRoot f),
      x ≡ y [SMOD ((m.map (AdjoinRoot.of f)) ^ n • (⊤ : Submodule (AdjoinRoot f) (AdjoinRoot f)))] ↔
        x ≡ y [SMOD (m ^ n • (⊤ : Submodule O (AdjoinRoot f)))] := by
    intro n x y
    rw [SModEq.sub_mem, SModEq.sub_mem, key]
  have hH : ∀ x : AdjoinRoot f, (∀ n : ℕ, x ∈ (m ^ n • (⊤ : Submodule O (AdjoinRoot f)))) → x = 0 := by
    intro x hx
    apply pb.basis.repr.injective
    ext i
    rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    refine IsHausdorff.haus' (I := m) _ (fun n => SModEq.zero.2 ?_)
    rw [GroundTheory.Arith.Abelian.mem_ideal_smul_top_self_iff]
    exact (GroundTheory.Arith.Abelian.mem_ideal_smul_top_iff_repr pb.basis (m ^ n) x).1 (hx n) i
  have hP : IsPrecomplete m (AdjoinRoot f) := GroundTheory.Arith.Abelian.isPrecomplete_of_basis m pb.basis
  haveI : IsHausdorff (m.map (AdjoinRoot.of f)) (AdjoinRoot f) :=
    ⟨fun x hx => hH x (fun n => SModEq.zero.1 ((hs n x 0).1 (hx n)))⟩
  haveI : IsPrecomplete (m.map (AdjoinRoot.of f)) (AdjoinRoot f) := by
    refine ⟨fun g hg => ?_⟩
    obtain ⟨L, hL⟩ := hP.prec' g (fun hmn => (hs _ _ _).1 (hg hmn))
    exact ⟨L, fun n => (hs n _ _).2 (hL n)⟩
  exact IsAdicComplete.mk

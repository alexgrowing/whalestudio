import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.IsotropicDual

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type}
  [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem h_sum_left {ι : Type} (s : Finset ι) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, v i) y = ∑ i ∈ s, H.h (v i) y := by
  let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)
  exact map_sum φ v s

theorem h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm y x, ← H.h_herm y' x]

theorem h_smul_right (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

theorem h_sum_right {ι : Type} (s : Finset ι) (x : V) (v : ι → V) :
    H.h x (∑ i ∈ s, v i) = ∑ i ∈ s, H.h x (v i) := by
  rw [H.h_herm (∑ i ∈ s, v i) x, h_sum_left, map_sum]
  exact Finset.sum_congr rfl fun i _ => (H.h_herm (v i) x).symm

end Herm

theorem isotropic_dual : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∀ y : Fin r → V, (∀ a, y a ∈ Λ) → (∀ a b, H.h (y a) (Fr.f b) = if b = a.castSucc then 1 else 0) → ∃ y' : Fin r → V, (∀ a, y' a ∈ Λ) ∧ (∀ a b, H.h (y' a) (Fr.f b) = if b = a.castSucc then 1 else 0) ∧ ∀ a b, H.h (y' a) (y' b) = 0 := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r Fr Λ hSD hFr y hy hyf
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨htr, -, -, -, hmem, -⟩ := GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ
  have hint : ∀ a b, H.h (y a) (y b) ∈ M.L.O := fun a b => (hSD.2.2 (y a)).1 (hy a) (y b) (hy b)
  have hdiag : ∀ a, ∃ x ∈ M.L.O, x + M.L.cj x = -H.h (y a) (y a) := by
    intro a
    obtain ⟨c, hc⟩ := (M.L.cj_fix (H.h (y a) (y a))).1 (H.h_herm (y a) (y a)).symm
    have hc' : c ∈ 𝒪[F] := (hmem c).1 (hc ▸ hint a a)
    obtain ⟨x, hx, hxe⟩ := htr (-⟨c, hc'⟩)
    refine ⟨x, hx, ?_⟩
    rw [hxe, ← hc]
    simp
  choose x hxO hxe using hdiag
  obtain ⟨m, hmO, hm⟩ : ∃ m : Fin r → Fin r → E, (∀ a k, m a k ∈ M.L.O) ∧
      ∀ a b, m a b + M.L.cj (m b a) = -H.h (y a) (y b) := by
    refine ⟨fun a k => if a < k then -H.h (y a) (y k) else if a = k then x a else 0, ?_, ?_⟩
    · intro a k
      dsimp only
      split_ifs
      · exact M.L.O.neg_mem (hint a k)
      · exact hxO a
      · exact M.L.O.zero_mem
    · intro a b
      dsimp only
      rcases lt_trichotomy a b with h | rfl | h
      · rw [if_pos h, if_neg (not_lt.2 h.le), if_neg h.ne', map_zero, add_zero]
      · rw [if_neg (lt_irrefl a), if_pos rfl]
        exact hxe a
      · rw [if_neg (not_lt.2 h.le), if_neg h.ne', if_pos h, map_neg, ← H.h_herm (y b) (y a),
          zero_add]
  have he : ∀ k : Fin r, Fr.f k.castSucc ∈ Λ := fun k => hFr.1.1 k.castSucc
  have hEf : ∀ (k : Fin r) b, H.h (Fr.f k.castSucc) (Fr.f b) = 0 := fun k b =>
    hFr.2.1 _ _ (Or.inl (Fin.castSucc_lt_last k).ne)
  have hyE : ∀ a k : Fin r, H.h (y a) (Fr.f k.castSucc) = if k = a then 1 else 0 := by
    intro a k
    rw [hyf a k.castSucc]
    simp only [Fin.castSucc_inj]
  have hEy : ∀ k b : Fin r, H.h (Fr.f k.castSucc) (y b) = if k = b then 1 else 0 := by
    intro k b
    rw [H.h_herm (y b) (Fr.f k.castSucc), hyE]
    split_ifs <;> simp
  refine ⟨fun a => y a + ∑ k, m a k • Fr.f k.castSucc, fun a => ?_, fun a b => ?_, fun a b => ?_⟩
  · refine Λ.add_mem (hy a) (Λ.sum_mem fun k _ => ?_)
    exact Λ.smul_mem ⟨m a k, hmO a k⟩ (he k)
  · simp only [H.h_add_left, h_sum_left, H.h_smul_left, hEf, mul_zero, Finset.sum_const_zero,
      add_zero, hyf]
  · simp only [H.h_add_left, h_add_right, h_sum_left, h_sum_right, H.h_smul_left, h_smul_right,
      hyE, hEy, hEf, mul_zero, mul_ite, mul_one, Finset.sum_const_zero, add_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linear_combination hm a b

end GlobalTheory.IsotropicDual

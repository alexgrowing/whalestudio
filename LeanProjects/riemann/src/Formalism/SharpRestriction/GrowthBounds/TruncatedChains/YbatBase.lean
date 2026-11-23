import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestPairOf
import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestTruncOfNil

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def resOps {m : ℕ} (E : GLOps n K V) (φ : Fin m → Fin n) : GLOps m K V := fun i j => E (φ i) (φ j)

theorem res_mem {m : ℕ} (E : GLOps n K V) (φ : Fin m → Fin n) (ν : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ν) :
    x ∈ weightSp (resOps E φ) (ν ∘ φ) := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro i
  exact hx (φ i)

theorem res_rep {m : ℕ} {E : GLOps n K V} (hE : IsGLRep E) (φ : Fin m → Fin n) (hφ : Function.Injective φ) :
    IsGLRep (resOps E φ) := by
  refine ⟨fun a b c d => ?_, fun x => ?_, ?_⟩
  · have h := hE.1 (φ a) (φ b) (φ c) (φ d)
    simpa only [resOps, hφ.eq_iff] using h
  · obtain ⟨W, hW, hx, hst⟩ := hE.2.1 x
    exact ⟨W, hW, hx, fun a b y hy => hst (φ a) (φ b) y hy⟩
  · rw [eq_top_iff, ← hE.2.2]
    exact iSup_le fun mu => le_iSup_of_le (mu ∘ φ) fun x hx => res_mem E φ mu x hx

end

theorem ybat_base (D : Formalism.BasicNotions.D7) (hK : RestKill) (hP : RestPair) (hP' : RestPair') : YBat 0 0 := by
  intro K V _ _ _ _ _ n E hE a b c hab hac hbc ν s t hs ht T hT x hx
  have hs' : (s : ℤ) = ν a - ν b + 1 := by push_cast at hs; linarith
  have ht' : (t : ℤ) = ν b - ν c + 1 := by push_cast at ht; linarith
  have hu1 : ((s + t : ℕ) : ℤ) - (ν a - ν c) - 1 = (s : ℤ) - (ν a - ν b) := by push_cast; linarith
  have hu2 : ((s + t : ℕ) : ℤ) - (ν a - ν c) - 1 = (t : ℤ) - (ν b - ν c) := by push_cast; linarith
  have hsh := gl_rep_shifts_weights hE
  have hx1 : pf E b c t T x ∈ weightSp E ν := pf_wt hsh ν b c t T x hx
  have hx2 : pf E a c (s + t) T (pf E b c t T x) ∈ weightSp E ν := pf_wt hsh ν a c (s + t) T _ hx1
  have hz1 : pf E a b s T x ∈ weightSp E ν := pf_wt hsh ν a b s T x hx
  have hz2 : pf E a c (s + t) T (pf E a b s T x) ∈ weightSp E ν := pf_wt hsh ν a c (s + t) T _ hz1
  have hLw : pf E a b s T (pf E a c (s + t) T (pf E b c t T x)) ∈ weightSp E ν := pf_wt hsh ν a b s T _ hx2
  have hRw : pf E b c t T (pf E a c (s + t) T (pf E a b s T x)) ∈ weightSp E ν := pf_wt hsh ν b c t T _ hz2
  have hL_ab : E a b (pf E a b s T (pf E a c (s + t) T (pf E b c t T x))) = 0 :=
    hK K V n E hE a b hab ν s hs' T hT _ hx2
  have hL_bc : E b c (pf E a b s T (pf E a c (s + t) T (pf E b c t T x))) = 0 := by
    rw [hP K V n E hE a b c hab hac hbc ν s (s + t) hu1 T hT _ hx1, hK K V n E hE b c hbc ν t ht' T hT x hx,
      map_zero, map_zero]
  have hR_bc : E b c (pf E b c t T (pf E a c (s + t) T (pf E a b s T x))) = 0 :=
    hK K V n E hE b c hbc ν t ht' T hT _ hz2
  have hR_ab : E a b (pf E b c t T (pf E a c (s + t) T (pf E a b s T x))) = 0 := by
    rw [hP' K V n E hE a b c hab hac hbc ν t (s + t) hu2 T hT _ hz1, hK K V n E hE a b hab ν s hs' T hT x hx,
      map_zero, map_zero]
  set Lv := pf E a b s T (pf E a c (s + t) T (pf E b c t T x)) with hLv
  set Rv := pf E b c t T (pf E a c (s + t) T (pf E a b s T x)) with hRv
  have hφ : Function.Injective ![a, b, c] := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  have hE' := res_rep hE ![a, b, c] hφ
  have hv' : Lv - Rv ∈ weightSp (resOps E ![a, b, c]) (ν ∘ ![a, b, c]) :=
    res_mem E ![a, b, c] ν _ (Submodule.sub_mem _ hLw hRw)
  have hvab : E a b (Lv - Rv) = 0 := by rw [map_sub, hL_ab, hR_ab, sub_zero]
  have hvbc : E b c (Lv - Rv) = 0 := by rw [map_sub, hL_bc, hR_bc, sub_zero]
  have hvac : E a c (Lv - Rv) = 0 := by
    have h := hE.1 a b b c
    rw [if_pos rfl, if_neg hac.symm, sub_zero] at h
    rw [← h, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hvbc, hvab, map_zero, map_zero,
      sub_zero]
  have hraise : ∀ i j : Fin 3, i < j → resOps E ![a, b, c] i j (Lv - Rv) = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd hij (by decide)
      | exact hvab
      | exact hvac
      | exact hvbc
  have hlow : ∀ (i j : Fin 3), j < i → ∀ (cc : ℕ) (y : V),
      pf E (![a, b, c] j) (![a, b, c] i) cc T y - y ∈ nMinus (resOps E ![a, b, c]) := by
    intro i j hji cc y
    obtain ⟨w, hw⟩ := pf_sub E (![a, b, c] j) (![a, b, c] i) cc T y
    rw [← hw]
    exact lowering_operator_mem_nMinus (resOps E ![a, b, c]) hji w
  have hLx : Lv - x ∈ nMinus (resOps E ![a, b, c]) := by
    have e : Lv - x = (pf E a b s T (pf E a c (s + t) T (pf E b c t T x)) - pf E a c (s + t) T (pf E b c t T x)) +
        (pf E a c (s + t) T (pf E b c t T x) - pf E b c t T x) + (pf E b c t T x - x) := by
      rw [hLv]; abel
    rw [e]
    exact add_mem (add_mem (hlow 1 0 (by decide) s _) (hlow 2 0 (by decide) (s + t) _)) (hlow 2 1 (by decide) t x)
  have hRx : Rv - x ∈ nMinus (resOps E ![a, b, c]) := by
    have e : Rv - x = (pf E b c t T (pf E a c (s + t) T (pf E a b s T x)) - pf E a c (s + t) T (pf E a b s T x)) +
        (pf E a c (s + t) T (pf E a b s T x) - pf E a b s T x) + (pf E a b s T x - x) := by
      rw [hRv]; abel
    rw [e]
    exact add_mem (add_mem (hlow 2 1 (by decide) t _) (hlow 2 0 (by decide) (s + t) _)) (hlow 1 0 (by decide) s x)
  have hvn : Lv - Rv ∈ nMinus (resOps E ![a, b, c]) := by
    have h := Submodule.sub_mem _ hLx hRx
    rwa [sub_sub_sub_cancel_right] at h
  exact sub_eq_zero.mp (hwv_mem_nMinus_eq_zero D (resOps E ![a, b, c]) hE' (ν ∘ ![a, b, c]) (Lv - Rv) hv' hraise hvn)

end Formalism.MainNotions.G.ExtremalProjector

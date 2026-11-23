import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem envExt_sub_mem {S A C : Type} [CommRing S] [CommRing A] [CommRing C] (G G' : A →+* C) (s : S →+* A)
    (J : Ideal S) (x a : A) (hs : G.comp s = G'.comp s) (ha : G a = G' a) (hx : x - a ∈ J.map s) :
    G x - G' x ∈ J.map (G.comp s) := by
  have e : G x - G' x = G (x - a) - G' (x - a) := by rw [map_sub, map_sub, ha]; ring
  rw [e]
  refine Ideal.sub_mem _ ?_ ?_
  · rw [← Ideal.map_map]; exact Ideal.mem_map_of_mem G hx
  · rw [hs, ← Ideal.map_map]; exact Ideal.mem_map_of_mem G' hx

theorem envExt_haus {C : Type} [CommRing C] (I : Ideal C) (h : IsHausdorff I C) (z : C) (hz : ∀ n : ℕ, z ∈ I ^ n) :
    z = 0 :=
  h.haus z fun n => by
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    exact hz n

set_option maxHeartbeats 1600000 in

theorem envExt_agree : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (d p : B.A) (En : Env bk B d p) (C : Type) [CommRing C] (φ : C →+* C) (F F' : En.Q.A →+* C), (∀ c : C, ((l : ℕ) : C) * c = 0 → c = 0) → (∀ a, F (En.Q.D.φ a) = φ (F a)) → (∀ a, F' (En.Q.D.φ a) = φ (F' a)) → (∀ b, F (En.inl.f b) = F' (En.inl.f b)) → F (BK.hf En.inr X) = F' (BK.hf En.inr X) → F (En.inl.f d) ∈ nonZeroDivisors C → IsHausdorff ((Ideal.span {((l : ℕ) : B.A)} ⊔ B.I).map (F.comp En.inl.f)) C → F = F' := by
  intro l _ K bk B d p En C _ φ F F' hl hF hF' hb hX hd hH

  have hw : F En.w = F' En.w := by
    have h1 := congrArg F En.w_eq
    have h2 := congrArg F' En.w_eq
    rw [map_add, map_mul] at h1 h2
    have h3 : F (En.inl.f d) * F En.w = F (En.inl.f d) * F' En.w := by
      rw [hb d] at h1 ⊢
      rw [hb p] at h1
      rw [hX] at h1
      rw [h2] at h1
      linear_combination -h1
    exact (mul_cancel_left_mem_nonZeroDivisors hd).1 h3

  have hδ : ∀ a, F a = F' a → F (En.Q.D.δ a) = F' (En.Q.D.δ a) := by
    intro a ha
    have e1 := hF a
    have e2 := hF' a
    rw [En.Q.D.φ_eq, map_add, map_mul, map_pow, map_natCast] at e1 e2
    rw [← ha] at e2
    have : ((l : ℕ) : C) * (F (En.Q.D.δ a) - F' (En.Q.D.δ a)) = 0 := by
      linear_combination e1 - e2
    exact sub_eq_zero.1 (hl _ this)
  have hit : ∀ i : ℕ, F (En.Q.D.δ^[i] En.w) = F' (En.Q.D.δ^[i] En.w) := by
    intro i
    induction i with
    | zero => exact hw
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact hδ _ ih
  have hbasis : ∀ α, F (En.tb.b α) = F' (En.tb.b α) := by
    intro α
    rw [En.tb_b, map_finsuppProd, map_finsuppProd]
    refine Finsupp.prod_congr fun i _ => ?_
    rw [map_pow, map_pow, hit i]
  have hcomp : F.comp En.inl.f = F'.comp En.inl.f := RingHom.ext hb
  have key : ∀ x (n : ℕ), F x - F' x ∈ ((Ideal.span {((l : ℕ) : B.A)} ⊔ B.I) ^ n).map (F.comp En.inl.f) := by
    intro x n
    have hfin := En.tb.fin x n
    have happ := En.tb.approx x n hfin.toFinset (fun i hi => by
      by_contra h
      exact hi (hfin.mem_toFinset.2 h))
    have hsum : F (∑ i ∈ hfin.toFinset, En.inl.f (En.tb.c i x) * En.tb.b i) =
        F' (∑ i ∈ hfin.toFinset, En.inl.f (En.tb.c i x) * En.tb.b i) := by
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, hb, hbasis]
    exact envExt_sub_mem F F' En.inl.f _ _ _ hcomp hsum happ
  ext x
  exact sub_eq_zero.1 (envExt_haus _ hH _ fun n => by rw [← Ideal.map_pow]; exact key x n)

end GlobalTheory.BSP

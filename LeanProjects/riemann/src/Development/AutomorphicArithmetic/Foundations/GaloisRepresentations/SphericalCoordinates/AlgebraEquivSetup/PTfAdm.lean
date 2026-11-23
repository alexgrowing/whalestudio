import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

namespace UpperTheory.Gal.W2.Seed

private lemma tyFn_mul_right {M : Type} [Group M] (J : Subgroup M) (ψ : J →* ℂˣ) (a j : M) (hj : j ∈ J) :
    tyFn J ψ (a * j) = tyFn J ψ a * (((ψ ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) := by
  unfold tyFn
  by_cases ha : a ∈ J
  · have haj : a * j ∈ J := J.mul_mem ha hj
    rw [dif_pos ha, dif_pos haj]
    have e : (⟨a * j, haj⟩ : J) = ⟨a, ha⟩ * ⟨j, hj⟩ := rfl
    rw [e, map_mul, mul_inv, Units.val_mul]
  · have haj : a * j ∉ J := fun h => ha ((J.mul_mem_cancel_right hj).1 h)
    rw [dif_neg ha, dif_neg haj, zero_mul]

private lemma tyFn_mul_left {M : Type} [Group M] (J : Subgroup M) (ψ : J →* ℂˣ) (a j : M) (hj : j ∈ J) :
    tyFn J ψ (j * a) = (((ψ ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) * tyFn J ψ a := by
  unfold tyFn
  by_cases ha : a ∈ J
  · have haj : j * a ∈ J := J.mul_mem hj ha
    rw [dif_pos ha, dif_pos haj]
    have e : (⟨j * a, haj⟩ : J) = ⟨j, hj⟩ * ⟨a, ha⟩ := rfl
    rw [e, map_mul, mul_inv, Units.val_mul]
  · have haj : j * a ∉ J := fun h => ha ((J.mul_mem_cancel_left hj).1 h)
    rw [dif_neg ha, dif_neg haj, mul_zero]

private lemma doset_left {X : Type} [Group X] (K : Subgroup X) (h k g : X) (hk : k ∈ K) :
    dosetInd ℂ K h (k * g) = dosetInd ℂ K h g := by
  have hiff : k * g ∈ DoubleCoset.doubleCoset h (K : Set X) (K : Set X) ↔
      g ∈ DoubleCoset.doubleCoset h (K : Set X) (K : Set X) := by
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, y, hy, e⟩
      exact ⟨k⁻¹ * x, K.mul_mem (K.inv_mem hk) hx, y, hy, by
        rw [mul_assoc, mul_assoc, ← mul_assoc x, ← e, inv_mul_cancel_left]⟩
    · rintro ⟨x, hx, y, hy, e⟩
      exact ⟨k * x, K.mul_mem hk hx, y, hy, by rw [e]; group⟩
  unfold dosetInd
  simp only [Set.indicator_apply, hiff, Pi.one_apply]

private lemma doset_right {X : Type} [Group X] (K : Subgroup X) (h k g : X) (hk : k ∈ K) :
    dosetInd ℂ K h (g * k) = dosetInd ℂ K h g := by
  have hiff : g * k ∈ DoubleCoset.doubleCoset h (K : Set X) (K : Set X) ↔
      g ∈ DoubleCoset.doubleCoset h (K : Set X) (K : Set X) := by
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, y, hy, e⟩
      exact ⟨x, hx, y * k⁻¹, K.mul_mem hy (K.inv_mem hk), by
        rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩
    · rintro ⟨x, hx, y, hy, e⟩
      exact ⟨x, hx, y * k, K.mul_mem hy hk, by rw [e]; group⟩
  unfold dosetInd
  simp only [Set.indicator_apply, hiff, Pi.one_apply]

private lemma fin_reps {X : Type} [Group X] (A B : Subgroup X) (hAB : B.relIndex A ≠ 0) :
    ∃ R : Finset X, (∀ r ∈ R, r ∈ A) ∧ ∀ k ∈ A, ∃ r ∈ R, ∃ u ∈ B, k = r * u := by
  have hfin : Finite (A ⧸ B.subgroupOf A) := Subgroup.index_ne_zero_iff_finite.mp hAB
  haveI := Fintype.ofFinite (A ⧸ B.subgroupOf A)
  refine ⟨Finset.univ.image (fun q : A ⧸ B.subgroupOf A => ((q.out : A) : X)), ?_, ?_⟩
  · intro r hr
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
    exact (q.out).2
  · intro k hk
    set q : A ⧸ B.subgroupOf A := ((⟨k, hk⟩ : A) : A ⧸ B.subgroupOf A) with hq
    refine ⟨((q.out : A) : X), Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩,
      ((q.out : A) : X)⁻¹ * k, ?_, by group⟩
    have h1 : ((q.out : A) : A ⧸ B.subgroupOf A) = ((⟨k, hk⟩ : A) : A ⧸ B.subgroupOf A) := by
      rw [QuotientGroup.out_eq']
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    simpa using h1

private lemma fin_doset {X M : Type} [Group X] [Group M] (T : TyLev X M) (h : X) :
    ∃ S : Finset X, ∀ g ∈ DoubleCoset.doubleCoset h (T.K : Set X) (T.K : Set X),
      ∃ s ∈ S, ∃ a b : T.K₀, g = (a : X) * s * b := by
  obtain ⟨R, -, hR⟩ := fin_reps T.K T.K₀ T.idx
  have hs := fun s : X => fin_reps T.K (T.K₀.map (MulAut.conj s).toMonoidHom)
    (Subgroup.relIndex_ne_zero_trans (T.cms s) T.idx)
  choose Rs _ hRs using hs
  refine ⟨R.biUnion (fun a => (Rs (h * a)).image (fun c => c * (h * a))), ?_⟩
  intro g hg
  obtain ⟨k, hk, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
  obtain ⟨a, ha, v, hv, rfl⟩ := hR k' hk'
  obtain ⟨c, hc, u, hu, rfl⟩ := hRs (h * a) k hk
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hu
  refine ⟨c * (h * a), Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩,
    1, ⟨t * v, T.K₀.mul_mem ht hv⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, OneMemClass.coe_one, one_mul,
    Subgroup.coe_mul]
  group

theorem pTfAdm : TfAdm := by
  intro X M _ _ T h _
  have hlr : ∀ k (hk : k ∈ T.K) g, T.tf h (k * g) = (((T.ψ ⟨T.L.pr k, T.fact.2 k hk⟩)⁻¹ : ℂˣ) : ℂ) * T.tf h g ∧
      T.tf h (g * k) = (((T.ψ ⟨T.L.pr k, T.fact.2 k hk⟩)⁻¹ : ℂˣ) : ℂ) * T.tf h g := by
    intro k hk g
    constructor
    · unfold TyLev.tf
      rw [map_mul, tyFn_mul_left _ _ _ _ (T.fact.2 k hk), doset_left _ _ _ _ hk]
      ring
    · unfold TyLev.tf
      rw [map_mul, tyFn_mul_right _ _ _ _ (T.fact.2 k hk), doset_right _ _ _ _ hk]
      ring
  refine ⟨⟨?_, ?_, ?_⟩, hlr⟩
  · show IsBiInv T.K₀ (T.tf h) ∧ FinDosetSupp T.K₀ (T.tf h)
    constructor
    · intro a b g
      rw [(hlr b (T.le b.2) (a * g)).2, (hlr a (T.le a.2) g).1, T.ker a a.2, T.ker b b.2]
      simp
    · obtain ⟨S, hS⟩ := fin_doset T h
      refine ⟨S, fun g hg => hS g ?_⟩
      by_contra hn
      apply hg
      unfold TyLev.tf dosetInd
      rw [Set.indicator_of_notMem hn, mul_zero]
  · intro g hg
    by_contra hn
    apply hg
    unfold TyLev.tf tyFn
    rw [dif_neg hn]
    simp
  · intro j g
    have e : (⟨T.L.pr (T.L.loc j), T.fact.2 _ (T.fact.1 j j.2)⟩ : T.J) = j := Subtype.ext (T.L.pr_loc j)
    rw [(hlr _ (T.fact.1 j j.2) g).2, e]

end UpperTheory.Gal.W2.Seed

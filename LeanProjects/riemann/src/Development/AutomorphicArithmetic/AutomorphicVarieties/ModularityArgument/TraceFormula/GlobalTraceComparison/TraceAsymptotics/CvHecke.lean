import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintSph

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open GlobalTheory.BCT
open scoped Pointwise

private theorem cv_eq_sum {G : Type} [Group G] (K : Subgroup G) (f g : G → ℂ)
    (hf : ∀ k ∈ K, ∀ x, f (x * k) = f x) (hg : ∀ k ∈ K, ∀ x, g (k * x) = g x) (y : G) :
    cv K f g y = ∑ᶠ q : G ⧸ K, f q.out * g (q.out⁻¹ * y) := by
  refine hintSph G K (fun z => f z * g (z⁻¹ * y)) ?_
  intro k hk x
  have e : (x * k)⁻¹ * y = k⁻¹ * (x⁻¹ * y) := by group
  simp only [e, hf k hk x, hg k⁻¹ (K.inv_mem hk)]

theorem cvHecke : CvHecke := by
  intro G _ _ _ K _ _ f g hf hg
  have hfl : ∀ k ∈ K, ∀ x, f (k * x) = f x := fun k hk x => (hf.2 k hk x).1
  have hfr : ∀ k ∈ K, ∀ x, f (x * k) = f x := fun k hk x => (hf.2 k hk x).2
  have hgl : ∀ k ∈ K, ∀ x, g (k * x) = g x := fun k hk x => (hg.2 k hk x).1
  have hgr : ∀ k ∈ K, ∀ x, g (x * k) = g x := fun k hk x => (hg.2 k hk x).2
  have hcv := cv_eq_sum K f g hfr hgl
  refine ⟨?_, fun k hk x => ⟨?_, ?_⟩⟩
  · have hS : IsCompact (tsupport f * tsupport g) := hf.1.isCompact.mul hg.1.isCompact
    refine hS.closure_of_subset ?_
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyS
    apply hy
    rw [hcv]
    have h0 : ∀ q : G ⧸ K, f q.out * g (q.out⁻¹ * y) = 0 := by
      intro q
      by_contra h
      have h1 : f q.out ≠ 0 := left_ne_zero_of_mul h
      have h2 : g (q.out⁻¹ * y) ≠ 0 := right_ne_zero_of_mul h
      exact hyS ⟨q.out, subset_tsupport _ h1, q.out⁻¹ * y, subset_tsupport _ h2, by group⟩
    simp [h0]
  · rw [hcv, hcv]
    have hF : ∀ z : G, f (z : G ⧸ K).out * g ((z : G ⧸ K).out⁻¹ * x) = f z * g (z⁻¹ * x) := by
      intro z
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K z
      have e : (z * (h : G))⁻¹ * x = (h : G)⁻¹ * (z⁻¹ * x) := by group
      rw [hh, hfr _ h.2, e, hgl _ (K.inv_mem h.2)]
    have hterm : ∀ q : G ⧸ K, f q.out * g (q.out⁻¹ * (k * x)) =
        (fun p : G ⧸ K => f p.out * g (p.out⁻¹ * x)) (MulAction.toPerm (k⁻¹ : G) q) := by
      intro q
      have e1 : MulAction.toPerm (k⁻¹ : G) q = ((k⁻¹ * q.out : G) : G ⧸ K) := by
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have e2 : (k⁻¹ * q.out)⁻¹ * x = q.out⁻¹ * (k * x) := by group
      simp only [e1]
      rw [hF, hfl _ (K.inv_mem hk), e2]
    rw [finsum_congr hterm]
    exact finsum_comp_equiv (f := fun p : G ⧸ K => f p.out * g (p.out⁻¹ * x))
      (MulAction.toPerm (k⁻¹ : G) : Equiv.Perm (G ⧸ K))
  · rw [hcv, hcv]
    refine finsum_congr fun q => ?_
    rw [← mul_assoc, hgr k hk]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

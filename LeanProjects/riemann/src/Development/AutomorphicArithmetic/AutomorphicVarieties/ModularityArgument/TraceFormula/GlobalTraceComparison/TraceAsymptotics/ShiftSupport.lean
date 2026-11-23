import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportOutFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpMemFixed

noncomputable section

open GlobalTheory.PRep GlobalTheory.BCT GlobalTheory.LFun
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section

variable {G : Type} [Group G]

private theorem cv_eq (K : Subgroup G) (f g : G → ℂ) (hf : ∀ k ∈ K, ∀ x, f (x * k) = f x)
    (hg : ∀ k ∈ K, ∀ x, g (k * x) = g x) (y : G) :
    cv K f g y = ∑ᶠ q : G ⧸ K, f q.out * g (q.out⁻¹ * y) := by
  have hle : K ≤ rStab (fun z => f z * g (z⁻¹ * y)) := by
    intro k hk x
    have e : (x * k)⁻¹ * y = k⁻¹ * (x⁻¹ * y) := by group
    show f (x * k) * g ((x * k)⁻¹ * y) = f x * g (x⁻¹ * y)
    rw [hf k hk, e, hg _ (K.inv_mem hk)]
  simp only [cv, hint]
  rw [inf_eq_right.2 hle]
  simp

private theorem smul_mk (K : Subgroup G) (a : G) (r : G ⧸ K) :
    (a • r : G ⧸ K) = QuotientGroup.mk (a * r.out) := by
  conv_lhs => rw [← QuotientGroup.out_eq' r]
  rfl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem shift_eval (ρ : Representation ℂ G V) (K : Subgroup G) (g : G → ℂ)
    (hg : ∀ k ∈ K, ∀ x, g (x * k) = g x) (x : V) (hx : ∀ k ∈ K, ρ k x = x) (a : G) (r : G ⧸ K) :
    g (a⁻¹ * (a • r : G ⧸ K).out) • ρ (a • r : G ⧸ K).out x = ρ a (g r.out • ρ r.out x) := by
  have hinv : ∀ y, ∀ h ∈ K, (fun y => g (a⁻¹ * y) • ρ y x) (y * h) = (fun y => g (a⁻¹ * y) • ρ y x) y := by
    intro y h hh
    simp only [map_mul, Module.End.mul_apply, hx h hh, ← mul_assoc, hg h hh]
  have := GlobalTheory.TwTrLevel.out_eq_of_inv K (fun y => g (a⁻¹ * y) • ρ y x) hinv (a * r.out)
  rw [smul_mk]
  refine this.trans ?_
  simp [map_mul, Module.End.mul_apply]

private theorem shift_support (ρ : Representation ℂ G V) (K : Subgroup G) (g : G → ℂ)
    (hg : ∀ k ∈ K, ∀ x, g (x * k) = g x) (hs : {q : G ⧸ K | g q.out ≠ 0}.Finite) (x : V)
    (hx : ∀ k ∈ K, ρ k x = x) (a : G) :
    (Function.support fun p : G ⧸ K => g (a⁻¹ * p.out) • ρ p.out x).Finite := by
  refine (hs.image (fun r : G ⧸ K => (a • r : G ⧸ K))).subset ?_
  intro p hp
  refine ⟨a⁻¹ • p, ?_, by simp⟩
  intro h0
  apply hp
  have := shift_eval ρ K g hg x hx a (a⁻¹ • p)
  rw [smul_inv_smul] at this
  simpa [show g (a⁻¹ • p : G ⧸ K).out = 0 from h0] using this

private theorem shift_sum (ρ : Representation ℂ G V) (K : Subgroup G) (g : G → ℂ)
    (hg : ∀ k ∈ K, ∀ x, g (x * k) = g x) (hs : {q : G ⧸ K | g q.out ≠ 0}.Finite) (x : V)
    (hx : ∀ k ∈ K, ρ k x = x) (a : G) :
    ∑ᶠ p : G ⧸ K, g (a⁻¹ * p.out) • ρ p.out x = ρ a (∑ᶠ r : G ⧸ K, g r.out • ρ r.out x) := by
  have hfin : (Function.support fun r : G ⧸ K => g r.out • ρ r.out x).Finite :=
    hs.subset fun q hq h0 => hq (by simp [h0])
  rw [map_finsum (ρ a) hfin,
    ← finsum_comp_equiv (MulAction.toPerm a : Equiv.Perm (G ⧸ K))]
  exact finsum_congr fun r => shift_eval ρ K g hg x hx a r

end

private theorem lev_eval {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (F : G → ℂ)
    (hfin : (Function.support fun q : G ⧸ K => F q.out).Finite) (v : V) :
    levOp ρ K K F LinearMap.id v = ∑ᶠ q : G ⧸ K, F q.out • ρ q.out v := by
  rw [GlobalTheory.TraceLevel.levOp_id_apply ρ K K F hfin]
  simp

theorem cvOp : CvOp := by
  intro G _ _ _ K hKo hKc V _ _ ρ f g hf hg x hx
  have hSf := GlobalTheory.TwTrLevel.finite_supp K hKo f hf.1
  have hSg := GlobalTheory.TwTrLevel.finite_supp K hKo g hg.1
  have hx' := (GlobalTheory.TwTrLevel.mem_fixed_iff ρ K x).1 hx
  have hfr : ∀ k ∈ K, ∀ y, f (y * k) = f y := fun k hk y => (hf.2 k hk y).2
  have hgr : ∀ k ∈ K, ∀ y, g (y * k) = g y := fun k hk y => (hg.2 k hk y).2
  have hgl : ∀ k ∈ K, ∀ y, g (k * y) = g y := fun k hk y => (hg.2 k hk y).1
  have hlg := lev_eval ρ K g hSg x
  refine ⟨?_, GlobalTheory.TraceLevel.levOp_mem_fixed ρ K K K g hg hKo le_rfl x hx, hlg⟩
  set S := hSf.toFinset with hS
  have hC : ∀ y, cv K f g y = ∑ q ∈ S, f q.out * g (q.out⁻¹ * y) := by
    intro y
    rw [cv_eq K f g hfr hgl y]
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    simp only [hS, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hq (by simp [h0])
  have hCfin : (Function.support fun p : G ⧸ K => cv K f g p.out).Finite := by
    refine (S.finite_toSet.biUnion fun q _ =>
      hSg.image (fun r : G ⧸ K => (q.out • r : G ⧸ K))).subset ?_
    intro p hp
    have hp' : ∑ q ∈ S, f q.out * g (q.out⁻¹ * p.out) ≠ 0 := by
      rw [← hC]; exact hp
    obtain ⟨q, hq, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp'
    refine Set.mem_biUnion (Finset.mem_coe.2 hq) ⟨q.out⁻¹ • p, ?_, by simp⟩
    have e := GlobalTheory.TwTrLevel.out_eq_of_inv K g (fun y h hh => hgr h hh y) (q.out⁻¹ * p.out)
    have e2 : (q.out⁻¹ • p : G ⧸ K) = QuotientGroup.mk (q.out⁻¹ * p.out) := smul_mk K _ _
    show g (q.out⁻¹ • p : G ⧸ K).out ≠ 0
    rw [e2, e]
    exact right_ne_zero_of_mul hne
  rw [lev_eval ρ K _ hCfin x, lev_eval ρ K f hSf, hlg]
  have hsupp := fun a => shift_support ρ K g hgr hSg x hx' a
  calc ∑ᶠ p : G ⧸ K, cv K f g p.out • ρ p.out x
      = ∑ᶠ p : G ⧸ K, ∑ q ∈ S, f q.out • (g (q.out⁻¹ * p.out) • ρ p.out x) := by
        refine finsum_congr fun p => ?_
        rw [hC, Finset.sum_smul]
        exact Finset.sum_congr rfl fun q _ => mul_smul _ _ _
    _ = ∑ q ∈ S, ∑ᶠ p : G ⧸ K, f q.out • (g (q.out⁻¹ * p.out) • ρ p.out x) := by
        refine finsum_sum_comm _ _ fun q _ => (hsupp q.out).subset fun p hp h0 => hp (by simp [h0])
    _ = ∑ q ∈ S, f q.out • ρ q.out (∑ᶠ r : G ⧸ K, g r.out • ρ r.out x) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← smul_finsum' _ (hsupp q.out), shift_sum ρ K g hgr hSg x hx' q.out]
    _ = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out (∑ᶠ r : G ⧸ K, g r.out • ρ r.out x) := by
        symm
        refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
        simp only [hS, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
        intro h0
        exact hq (by simp [h0])

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

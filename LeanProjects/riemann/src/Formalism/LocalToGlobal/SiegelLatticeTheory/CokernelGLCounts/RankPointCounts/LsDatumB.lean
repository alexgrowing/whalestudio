import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SupportProposition

noncomputable section

namespace Formalism.L2.SG.LsDatumB

open scoped BigOperators
open Classical

section Abstract

theorem hasSum_of_fiber {P G : Type*} [Finite P] (c : P → ℂ) (cls : P → G) (F : G → ℂ)
    (hF : ∀ g, HasSum (fun x : {x : P // cls x = g} => c x.1) (F g)) {s : ℂ} (hs : HasSum F s) :
    HasSum c s := by
  haveI := Fintype.ofFinite P
  have h1 : HasSum c (∑ x, c x) := hasSum_fintype c
  have h2 := h1.tsum_fiberwise cls
  have e : F = fun g => ∑' x : ↑(cls ⁻¹' {g}), c x := funext fun g => ((hF g).tsum_eq).symm
  have h4 : HasSum F (∑ x, c x) := by
    rw [e]
    exact h2
  rw [hs.unique h4]
  exact h1

variable {ι : Type*} {X : ι → Type*}

def Rst (x0 : ∀ p, X p) : Type _ := {x : ∀ p, X p // {p | x p ≠ x0 p}.Finite}

theorem hasSum_rst (x0 : ∀ p, X p) (f : ∀ p, X p → ℂ) (a : ι → ℂ) (S : Finset ι)
    (hoff : ∀ p ∉ S, ∀ x, f p x = if x = x0 p then 1 else 0)
    (hf : ∀ p ∈ S, HasSum (f p) (a p)) (hn : ∀ p ∈ S, Summable fun x => ‖f p x‖) :
    HasSum (fun x : Rst x0 => ∏ᶠ p, f p (x.1 p)) (∏ p ∈ S, a p) := by
  have h0 := (Formalism.L2.SG.Pf.hasSum_prod_offS x0 f a S hf hn).1
  let j : Formalism.L2.SG.Pf.OffS x0 S → Rst x0 := fun θ =>
    ⟨θ.1, (S.finite_toSet).subset fun p hp => by
      by_contra h
      exact hp (θ.2 p h)⟩
  have hj : Function.Injective j := fun a b h => Subtype.ext (congrArg (fun x : Rst x0 => x.1) h)
  have hsupp : ∀ x : Rst x0, (Function.mulSupport fun p => f p (x.1 p)) ⊆ (S : Set ι) ∪ {p | x.1 p ≠ x0 p} := by
    intro x p hp
    by_contra hc
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hc
    exact (Function.mem_mulSupport.1 hp) (by rw [hoff p hc.1, if_pos hc.2])
  have hfin : ∀ x : Rst x0, (Function.mulSupport fun p => f p (x.1 p)).Finite := fun x =>
    ((S.finite_toSet).union x.2).subset (hsupp x)
  have hzero : ∀ x ∉ Set.range j, (∏ᶠ p, f p (x.1 p)) = 0 := by
    intro x hx
    have : ∃ p ∉ S, x.1 p ≠ x0 p := by
      by_contra h
      push_neg at h
      exact hx ⟨⟨x.1, h⟩, rfl⟩
    obtain ⟨p, hpS, hp⟩ := this
    exact finprod_eq_zero _ p (by rw [hoff p hpS, if_neg hp]) (hfin x)
  rw [← hj.hasSum_iff hzero]
  convert h0 using 1
  funext θ
  simp only [Function.comp_apply]
  apply finprod_eq_prod_of_mulSupport_subset
  intro p hp
  by_contra hS
  exact (Function.mem_mulSupport.1 hp) (by rw [hoff p hS, if_pos (θ.2 p hS)])

theorem hasSum_passage {P G : Type*} [Finite P] (c : P → ℂ) (cls : P → G) (F : G → ℂ)
    (hF : ∀ g, HasSum (fun x : {x : P // cls x = g} => c x.1) (F g))
    (x0 : ∀ p, X p) (loc : G ≃ Rst x0) (f : ∀ p, X p → ℂ) (a : ι → ℂ) (S : Finset ι)
    (hFp : ∀ g, F g = ∏ᶠ p, f p ((loc g).1 p))
    (hoff : ∀ p ∉ S, ∀ x, f p x = if x = x0 p then 1 else 0)
    (hf : ∀ p ∈ S, HasSum (f p) (a p)) (hn : ∀ p ∈ S, Summable fun x => ‖f p x‖) :
    HasSum c (∏ p ∈ S, a p) := by
  have h1 := hasSum_rst x0 f a S hoff hf hn
  have h2 : HasSum F (∏ p ∈ S, a p) := by
    have e : F = (fun x : Rst x0 => ∏ᶠ p, f p (x.1 p)) ∘ loc := funext fun g => hFp g
    rw [e]
    exact (loc.hasSum_iff).2 h1
  exact hasSum_of_fiber c cls F hF h2

end Abstract

end Formalism.L2.SG.LsDatumB

import Formalism.LocalToGlobal.GlobalTheory.GL4.PLinks

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

section Frames

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def mulDual (S : HSpace E) (M : ℕ) (L : Submodule (𝓞 E) S.V) : AddSubgroup S.V :=
  (dualSub S L).map (DistribSMul.toAddMonoidHom S.V (M : E))

def IsoLat (S : HSpace E) (L L' : Submodule (𝓞 E) S.V) : Prop :=
  ∃ γ : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (γ x) (γ y) = S.hT x y) ∧ ∀ x, x ∈ L ↔ γ x ∈ L'

theorem mem_dualSub (S : HSpace E) (L : Submodule (𝓞 E) S.V) (x : S.V) :
    x ∈ dualSub S L ↔ ∀ y ∈ L, S.hT y x ∈ (algebraMap (𝓞 E) E).range := Iff.rfl

theorem dual_map_of_isom (S : HSpace E) {L L' : Submodule (𝓞 E) S.V} (γ : S.V ≃ₗ[E] S.V)
    (hγ : ∀ x y, S.hT (γ x) (γ y) = S.hT x y) (hL : ∀ x, x ∈ L ↔ γ x ∈ L') {x : S.V}
    (hx : x ∈ dualSub S L) : γ x ∈ dualSub S L' := by
  rw [mem_dualSub] at hx ⊢
  intro y hy
  have h1 : γ.symm y ∈ L := (hL _).2 (by simpa using hy)
  have h2 := hx _ h1
  rwa [← hγ, LinearEquiv.apply_symm_apply] at h2

theorem isom_symm (S : HSpace E) (γ : S.V ≃ₗ[E] S.V) (hγ : ∀ x y, S.hT (γ x) (γ y) = S.hT x y) :
    ∀ x y, S.hT (γ.symm x) (γ.symm y) = S.hT x y := by
  intro x y
  rw [← hγ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem card_le_of_frames (S : HSpace E) (M n : ℕ) {ι : Type} [Fintype ι]
    (L : ι → Submodule (𝓞 E) S.V) (e : ι → Fin n → S.V)
    (he : ∀ c a, e c a ∈ dualSub S (L c))
    (hsep : ∀ c c', SameCls S M (L c) (L c') (e c) (e c') → c = c')
    (R : Finset ι) (hR : ∀ c, ∃ r ∈ R, IsoLat S (L c) (L r)) (Q : ℕ)
    (hQ : ∀ r ∈ R, (mulDual S M (L r)).relIndex (dualSub S (L r)) ≠ 0 ∧
      (mulDual S M (L r)).relIndex (dualSub S (L r)) ≤ Q) :
    Fintype.card ι ≤ R.card * Q ^ n := by
  classical
  choose ρ hρR hρ using hR
  choose γ hγi hγL using hρ
  have hfib : ∀ r ∈ R, (Finset.univ.filter (fun c => ρ c = r)).card ≤ Q ^ n := by
    intro r hr
    obtain ⟨h0, hle⟩ := hQ r hr
    set K := dualSub S (L r) with hK
    set H := (mulDual S M (L r)).addSubgroupOf K with hH
    have : H.FiniteIndex := ⟨h0⟩
    have : Finite (K ⧸ H) := AddSubgroup.finite_quotient_of_finiteIndex
    have hm : ∀ (c : {c // ρ c = r}) (a : Fin n), γ c.1 (e c.1 a) ∈ K := fun c a => by
      have := dual_map_of_isom S (γ c.1) (hγi c.1) (hγL c.1) (he c.1 a)
      rw [c.2] at this
      exact this
    let g : {c // ρ c = r} → (Fin n → K ⧸ H) := fun c a => ((⟨γ c.1 (e c.1 a), hm c a⟩ : K) : K ⧸ H)
    have hg : Function.Injective g := by
      intro c c' hcc
      apply Subtype.ext
      apply hsep c.1 c'.1
      refine ⟨(γ c.1).trans (γ c'.1).symm, fun x y => ?_, fun x => ?_, fun a => ?_⟩
      · simp only [LinearEquiv.trans_apply]
        rw [isom_symm S _ (hγi c'.1), hγi c.1]
      · rw [hγL c.1 x, hγL c'.1 (((γ c.1).trans (γ c'.1).symm) x), LinearEquiv.trans_apply,
          LinearEquiv.apply_symm_apply, c.2, c'.2]
      · have h1 := congrFun hcc a
        simp only [g] at h1
        rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
        obtain ⟨z0, hz0, hz⟩ := AddSubgroup.mem_map.1 h1
        simp only [DistribSMul.toAddMonoidHom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg] at hz
        have hLs : ∀ x, x ∈ L r ↔ (γ c'.1).symm x ∈ L c'.1 := fun x => by
          rw [hγL c'.1 ((γ c'.1).symm x), LinearEquiv.apply_symm_apply, c'.2]
        refine ⟨(γ c'.1).symm (-z0), dual_map_of_isom S (γ c'.1).symm (isom_symm S _ (hγi c'.1)) hLs
          (neg_mem hz0), ?_⟩
        have h2 : (M : E) • (-z0) = γ c.1 (e c.1 a) - γ c'.1 (e c'.1 a) := by
          rw [smul_neg, hz]
          abel
        rw [← LinearEquiv.map_smul, h2, map_sub, LinearEquiv.symm_apply_apply,
          LinearEquiv.trans_apply]
    have hc := Nat.card_le_card_of_injective g hg
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at hc
    have hKH : Nat.card (K ⧸ H) ≤ Q := hle
    have hpow : Nat.card (K ⧸ H) ^ n ≤ Q ^ n := Nat.pow_le_pow_left hKH n
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
    exact hc.trans hpow
  calc Fintype.card ι = (Finset.univ : Finset ι).card := Finset.card_univ.symm
    _ = ∑ r ∈ R, (Finset.univ.filter (fun c => ρ c = r)).card :=
        Finset.card_eq_sum_card_fiberwise (fun c _ => hρR c)
    _ ≤ ∑ _r ∈ R, Q ^ n := Finset.sum_le_sum hfib
    _ = R.card * Q ^ n := by rw [Finset.sum_const, smul_eq_mul]

end Frames

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end

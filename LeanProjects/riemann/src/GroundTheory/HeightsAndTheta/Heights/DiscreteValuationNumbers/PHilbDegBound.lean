import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace HilbDegBound

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isHomogeneous_of_isMultiHomogIdeal {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) :
    I.IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) := by
  classical
  have e : I = Ideal.span
      {g | ∃ f ∈ I, ∃ b, g = weightedHomogeneousComponent (blockWeight ι) b f} := by
    apply le_antisymm
    · intro f hf
      rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨f, hf, b, rfl⟩
    · rw [Ideal.span_le]
      rintro g ⟨f, hf, b, rfl⟩
      exact hI f hf b
  rw [e]
  refine Ideal.homogeneous_span _ _ fun x hx => ?_
  obtain ⟨f, -, b, rfl⟩ := hx
  exact ⟨b, weightedHomogeneousComponent_isWeightedHomogeneous b f⟩

theorem isMultiHomogIdeal_sup_span {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {s : MRing ι F} {c : K → ℕ} (hs : IsMultiHomog s c) :
    IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by
  classical
  have h2 : (Ideal.span {s}).IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) :=
    Ideal.homogeneous_span _ _ fun x hx => ⟨c, (Set.mem_singleton_iff.mp hx) ▸ hs⟩
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem
    (h := (isHomogeneous_of_isMultiHomogIdeal hI).sup h2) (hp := hf) (m := b)

theorem lt_of_add_one_le_natCast {x : WithBot ℕ∞} {N : ℕ} (h : x + 1 ≤ N) : x < N := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have e : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [e, ← WithBot.coe_natCast, WithBot.coe_le_coe] at h
      exact absurd h (not_le.mpr (ENat.natCast_lt_top N))
    | coe a =>
      have : a + 1 ≤ N := by exact_mod_cast h
      exact_mod_cast (show a < N by omega)

theorem le_natCast_of_lt_natCast_succ {x : WithBot ℕ∞} {N : ℕ}
    (h : x < ((N + 1 : ℕ) : WithBot ℕ∞)) : x ≤ N := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      rw [← WithBot.coe_natCast, WithBot.coe_lt_coe] at h
      exact absurd h (not_lt.mpr le_top)
    | coe a =>
      have : a < N + 1 := by exact_mod_cast h
      exact_mod_cast (show a ≤ N by omega)

omit [Fintype K] [DecidableEq K] in

theorem degLT_listSum (h6 : DegLTClosure.Statement) {α : Type*} (n : ℕ)
    (g : α → (K → ℤ) → ℤ) (l : List α) (hl : ∀ a ∈ l, DegLT (g a) n) :
    DegLT (fun m => (l.map fun a => g a m).sum) n := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact degLT_zero n
  | cons a l ih =>
    have e : (fun m => ((a :: l).map fun a => g a m).sum) =
        g a + fun m => (l.map fun a => g a m).sum := by
      funext m
      simp
    rw [e]
    exact (h6 K n _ _ 0 0).1 (hl a (by simp)) (ih fun b hb => hl b (by simp [hb]))

end Lemmas

end HilbDegBound

open HilbDegBound in

theorem HilbDegBound.proof (h1 : HilbFnVanishBlock.Statement.{u}) (h2 : HilbFnCut.Statement.{u})
    (h3 : PrimeFiltration.Statement.{u}) (h4 : DimStrictDrop.Statement.{u})
    (h5 : RelevantDimGe.Statement.{u}) (h6 : DegLTClosure.Statement)
    (h7 : DegLTOfUnitSteps.Statement) : HilbDegBound.Statement.{u} := by
  intro F _ K _ _ ι _ n

  have irr : ∀ (n : ℕ) (Q : Ideal (MRing ι F)), ¬ IsRelevant Q → DegLT (hilbFn Q) n := by
    intro n Q hrel
    unfold IsRelevant at hrel
    push Not at hrel
    obtain ⟨k, hk⟩ := hrel
    have hev : (0 : (K → ℤ) → ℤ) =ᶠ[Filter.atTop] hilbFn Q := by
      filter_upwards [Filter.eventually_ge_atTop (1 : K → ℤ)] with m hm
      exact (h1 F K ι Q k hk m (hm k)).symm
    exact (h6 K n 0 _ 0 0).2.2.2.2 hev (degLT_zero n)
  induction n with
  | zero =>
    intro Q hQ hQh hdim
    by_cases hrel : IsRelevant Q
    · exfalso
      have hge := h5 F K ι Q ⟨hQ, hQh, hrel⟩
      rw [Nat.zero_add] at hdim
      exact absurd hge (not_le.mpr hdim)
    · exact irr 0 Q hrel
  | succ n ih =>
    intro Q hQ hQh hdim
    by_cases hrel : IsRelevant Q
    swap
    · exact irr _ Q hrel
    have hdimle : ringKrullDim (MRing ι F ⧸ Q) ≤ ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      have e : n + 1 + Fintype.card K = n + Fintype.card K + 1 := by omega
      rw [e] at hdim
      exact le_natCast_of_lt_natCast_succ hdim
    apply h7 K n
    intro k
    obtain ⟨i, hi⟩ := hrel k
    have hx : IsMultiHomog (X ⟨k, i⟩ : MRing ι F) (Pi.single k 1) := isWeightedHomogeneous_X _ _ _
    have hnzd : ∀ y, (X ⟨k, i⟩ : MRing ι F) * y ∈ Q → y ∈ Q :=
      fun y hy => (hQ.mem_or_mem hy).resolve_left hi
    have hcut := h2 F K ι Q (X ⟨k, i⟩) (Pi.single k 1) hQh hx hnzd
    have hJ : IsMultiHomogIdeal (Q ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)}) :=
      isMultiHomogIdeal_sup_span hQh hx
    have hs : (fun j => ((Pi.single k 1 : K → ℕ) j : ℤ)) = (Pi.single k 1 : K → ℤ) := by
      funext j
      by_cases h : j = k <;> simp [h]
    have heq : diffStep (Pi.single k 1) (hilbFn Q) =
        hilbFn (Q ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)}) := by
      funext m
      rw [hcut m, hs]
      rfl
    rw [heq]
    obtain ⟨l, hl1, hl2, -⟩ := h3 F K ι _ hJ
    obtain ⟨G, hG⟩ : ∃ G : Ideal (MRing ι F) × (K → ℕ) → (K → ℤ) → ℤ,
        G = fun p => shiftFn (fun j => (p.2 j : ℤ)) (hilbFn p.1) := ⟨_, rfl⟩
    have hfun : hilbFn (Q ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)}) = fun m =>
        (l.map fun p => G p m).sum := by
      funext m
      rw [hl2 m, hG]
      rfl
    rw [hfun]
    apply degLT_listSum h6 n G l
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := hl1 p hp
    rw [hG]
    refine (h6 K n (hilbFn p.1) 0 0 _).2.2.1 ?_
    refine ih p.1 hp1 hp2 ?_
    have hlt : Q < p.1 := by
      refine lt_of_le_of_ne (le_sup_left.trans hp3) fun h => hi ?_
      rw [h]
      exact hp3 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have := hQ
    have := hp1
    have hd := h4 (MRing ι F) Q p.1 hlt
    exact lt_of_add_one_le_natCast (hd.trans hdimle)

end

end GroundTheory.Heights₂.Heights.NumbersDVR

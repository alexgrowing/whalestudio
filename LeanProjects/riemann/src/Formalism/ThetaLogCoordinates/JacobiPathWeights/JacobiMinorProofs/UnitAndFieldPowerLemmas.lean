import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.CorA3primeB
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ValuationProductsComponents
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ExistsSuppOfEvalNe
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LeIffLtColHeight
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.NormIndexCountBound

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace ExponentSetCounting

variable {n : ℕ}

def GP (n i : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ) (M : WithTop ℤ) : Type :=
  {μ : ℕ → Fin n → ℤ // IsPath n isVec B μ i ∧ (∀ j, i < j → μ j = 0) ∧ GoodW θ M (μ i)}

def ContP (i N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ₀ : Fin n → ℤ)
    (x : (ℕ → Fin n → ℤ) × (ℤ → Finset (Fin n))) : Prop :=
  x.1 i = μ₀ ∧ (∀ j, j < i ∨ N < j → x.1 j = 0) ∧
    (∀ j, i ≤ j → j < N →
      if isVec j then HStrip (x.1 (j + 1)) (x.1 j) (B j) else HStrip (x.1 j) (x.1 (j + 1)) (B j)) ∧
    IsStd (x.1 N) x.2

def splitEquiv {i N : ℕ} (hi : i ≤ N) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ) (M : WithTop ℤ) :
    {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)} ≃
      Σ P : GP n i isVec B θ M, {x // ContP i N isVec B (P.1 i) x} where
  toFun x := ⟨⟨fun j => if j ≤ i then x.1.1.1 j else 0, by
      obtain ⟨⟨⟨μ, I⟩, ⟨h0, h1, h2⟩, h3, h4⟩, hg⟩ := x
      refine ⟨⟨by simpa using h0, ?_, ?_⟩, ?_, by simpa using hg⟩
      · intro j hj
        simpa [hj] using h1 j (hj.trans hi)
      · intro j hj
        have e1 : j ≤ i := by omega
        have e2 : j + 1 ≤ i := by omega
        simpa [e1, e2] using h2 j (by omega)
      · intro j hj
        have e1 : ¬ j ≤ i := by omega
        simp [e1]⟩,
    ⟨(fun j => if i ≤ j then x.1.1.1 j else 0, x.1.1.2), by
      obtain ⟨⟨⟨μ, I⟩, ⟨h0, h1, h2⟩, h3, h4⟩, hg⟩ := x
      refine ⟨by simp, ?_, ?_, by simpa [hi] using h4⟩
      · intro j hj
        by_cases e1 : i ≤ j
        · simpa [e1] using h3 j (by omega)
        · simp [e1]
      · intro j e1 hj
        have e2 : i ≤ j + 1 := by omega
        simpa [e1, e2] using h2 j hj⟩⟩
  invFun y := ⟨⟨(fun j => if j ≤ i then y.1.1 j else y.2.1.1 j, y.2.1.2), by
      obtain ⟨⟨μ, ⟨h0, h1, h2⟩, h3, hg⟩, ⟨⟨ν, I⟩, c0, c1, c2, c3⟩⟩ := y
      simp only at c0 c1 c2 c3 ⊢
      have key : ∀ j, i ≤ j → (if j ≤ i then μ j else ν j) = ν j := by
        intro j hj
        by_cases e : j ≤ i
        · obtain rfl : j = i := by omega
          simp [c0]
        · simp [e]
      have hr : ∀ j < N, if isVec j then
            HStrip (if j + 1 ≤ i then μ (j + 1) else ν (j + 1)) (if j ≤ i then μ j else ν j) (B j)
          else HStrip (if j ≤ i then μ j else ν j) (if j + 1 ≤ i then μ (j + 1) else ν (j + 1)) (B j) := by
        intro j hj
        by_cases e : j < i
        · have e1 : j ≤ i := by omega
          have e2 : j + 1 ≤ i := by omega
          simpa [e1, e2] using h2 j e
        · rw [key j (by omega), key (j + 1) (by omega)]
          exact c2 j (by omega) hj
      have h00 : (if 0 ≤ i then μ 0 else ν 0) = 0 := by simpa using h0
      refine ⟨⟨h00, ?_, hr⟩, ?_, ?_⟩
      · exact Count.antitone_of_rules (μ := fun j => if j ≤ i then μ j else ν j)
          (by rw [h00]; exact fun _ _ _ => le_rfl) hr
      · intro j hj
        rw [key j (by omega)]
        exact c1 j (Or.inr hj)
      · rw [key N hi]
        exact c3⟩, by
      simpa using y.1.2.2.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · funext j
      by_cases e : j ≤ i
      · simp [e]
      · have e' : i ≤ j := by omega
        simp [e, e']
    · rfl
  right_inv y := by
    obtain ⟨⟨μ, ⟨h0, h1, h2⟩, h3, hg⟩, ⟨⟨ν, I⟩, c0, c1, c2, c3⟩⟩ := y
    simp only at c0 c1 c2 c3
    apply Sigma.subtype_ext
    · apply Subtype.ext
      funext j
      by_cases e : j ≤ i
      · simp [e]
      · simp [e, h3 j (by omega)]
    · apply Prod.ext
      · funext j
        by_cases e : i ≤ j
        · by_cases e' : j ≤ i
          · obtain rfl : j = i := by omega
            simp [c0]
          · simp [e, e']
        · simp [e, c1 j (Or.inl (by omega))]
      · rfl

theorem card_good (hC : CountCont) {i N : ℕ} (hi : i ≤ N) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ)
    (M : WithTop ℤ) :
    Nat.card {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)} =
      Nat.card {x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} *
        ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) := by
  set K := ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) with hK
  have hanti : ∀ P : GP n i isVec B θ M, Antitone (P.1 i) := fun P => P.2.1.2.1 i le_rfl
  have hF : ∀ P : GP n i isVec B θ M, Finite {x // ContP i N isVec B (P.1 i) x} ∧
      Nat.card {x // ContP i N isVec B (P.1 i) x} = dGT n (P.1 i) * K :=
    fun P => hC n i N isVec B (P.1 i) hi (hanti P)
  have hG : ∀ P : GP n i isVec B θ M, Finite {x // ContP i i isVec B (P.1 i) x} ∧
      Nat.card {x // ContP i i isVec B (P.1 i) x} = dGT n (P.1 i) := by
    intro P
    have h := hC n i i isVec B (P.1 i) le_rfl (hanti P)
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [Finset.Ico_self, Finset.prod_empty, mul_one] at h2
    exact h2
  have he : ∀ P : GP n i isVec B θ M, Nonempty ({x // ContP i N isVec B (P.1 i) x} ≃
      {x // ContP i i isVec B (P.1 i) x} × Fin K) := by
    intro P
    haveI := (hF P).1
    haveI := (hG P).1
    haveI := Fintype.ofFinite {x // ContP i N isVec B (P.1 i) x}
    haveI := Fintype.ofFinite {x // ContP i i isVec B (P.1 i) x}
    refine ⟨Fintype.equivOfCardEq ?_⟩
    rw [Fintype.card_prod, Fintype.card_fin, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      (hF P).2, (hG P).2]
  let e : ∀ P : GP n i isVec B θ M,
      {x // ContP i N isVec B (P.1 i) x} ≃ {x // ContP i i isVec B (P.1 i) x} × Fin K :=
    fun P => Classical.choice (he P)
  let d : (Σ P : GP n i isVec B θ M, {x // ContP i i isVec B (P.1 i) x} × Fin K) ≃
      (Σ P : GP n i isVec B θ M, {x // ContP i i isVec B (P.1 i) x}) × Fin K :=
    { toFun := fun y => (⟨y.1, y.2.1⟩, y.2.2)
      invFun := fun z => ⟨z.1.1, (z.1.2, z.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc Nat.card {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)}
      = Nat.card ((Σ P : GP n i isVec B θ M, {x // ContP i i isVec B (P.1 i) x}) × Fin K) :=
        Nat.card_congr (((splitEquiv hi isVec B θ M).trans (Equiv.sigmaCongrRight e)).trans d)
    _ = Nat.card {x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} * K := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin K), Fintype.card_fin,
          ← Nat.card_congr (splitEquiv (le_refl i) isVec B θ M)]

def expSet (n i N : ℕ) (B : ℕ → ℕ) : Set (ℕ × Fin n →₀ ℕ) :=
  {β | ∀ j, ∑ a, β (j, a) = if i ≤ j ∧ j < N then B j else 0}

theorem shift_inj (n i : ℕ) : Function.Injective (fun x : ℕ × Fin n => (i + x.1, x.2)) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (by omega) h.2

theorem expSet_subset (n i N : ℕ) (B : ℕ → ℕ) :
    expSet n i N B ⊆ Finsupp.mapDomain (fun x : ℕ × Fin n => (i + x.1, x.2)) ''
      {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0} := by
  intro β hβ
  have hβ' : ∀ j, ∑ a, β (j, a) = if i ≤ j ∧ j < N then B j else 0 := hβ
  have hsupp : ↑β.support ⊆ Set.range (fun x : ℕ × Fin n => (i + x.1, x.2)) := by
    intro p hp
    obtain ⟨j, a⟩ := p
    have hpa : β (j, a) ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hij : i ≤ j := by
      by_contra hlt
      have h0 := hβ' j
      rw [if_neg (fun h => hlt h.1)] at h0
      exact hpa ((Finset.sum_eq_zero_iff.mp h0) a (Finset.mem_univ a))
    exact ⟨(j - i, a), Prod.ext (show i + (j - i) = j by omega) rfl⟩
  refine ⟨Finsupp.comapDomain _ β (fun _ _ _ _ h => shift_inj n i h), ?_, ?_⟩
  · simp only [Set.mem_setOf_eq]
    intro j
    show ∑ a, β (i + j, a) = _
    rw [hβ' (i + j)]
    by_cases h : j < N - i
    · rw [if_pos ⟨by omega, by omega⟩, if_pos h]
    · rw [if_neg (by omega), if_neg h]
  · apply Finsupp.mapDomain_comapDomain
    · exact shift_inj n i
    · exact hsupp

theorem expSet_finite (hR : PolBRank) (n i N : ℕ) (B : ℕ → ℕ) : (expSet n i N B).Finite :=
  ((hR n (N - i) (fun j => B (i + j))).2.1.image _).subset (expSet_subset n i N B)

theorem expSet_card (hR : PolBRank) (n i N : ℕ) (B : ℕ → ℕ) :
    (expSet n i N B).ncard ≤ ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) := by
  have hfin : {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.Finite :=
    (hR n (N - i) (fun j => B (i + j))).2.1
  have hcard : {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.ncard =
      ∏ j ∈ Finset.range (N - i), (n + B (i + j) - 1).choose (B (i + j)) :=
    (hR n (N - i) (fun j => B (i + j))).1
  calc (expSet n i N B).ncard
      ≤ ((Finsupp.mapDomain (fun x : ℕ × Fin n => (i + x.1, x.2))) ''
          {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}).ncard :=
        Set.ncard_le_ncard (expSet_subset n i N B) (hfin.image _)
    _ ≤ {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.ncard :=
        Set.ncard_image_le hfin
    _ = ∏ j ∈ Finset.range (N - i), (n + B (i + j) - 1).choose (B (i + j)) := hcard
    _ = ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) :=
        (Finset.prod_Ico_eq_prod_range (fun l => (n + B l - 1).choose (B l)) i N).symm

theorem psiFam_mem (k : Type) [Field k] (N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (x : PathIdx n N isVec B) :
    psiFam k n N isVec B x ∈ polB k n N B := by
  rw [polB, Submodule.mem_iInf]
  intro j
  exact (pathProductDegrees k n N isVec B x.1.1 x.1.2 x.2.1 x.2.2.2.1).2 j

theorem psiFam_good (k : Type) [Field k] (hn : 1 ≤ n) {i N : ℕ} (hi : i ≤ N) (isVec : ℕ → Bool) (B : ℕ → ℕ)
    (θ : WithBot ℤ) (M : WithTop ℤ) (x : PathIdx n N isVec B) (hx : GoodW θ M (x.1.1 i)) :
    GoodG isVec i θ M (psiFam k n N isVec B x) := by
  obtain ⟨h1, h2⟩ := valuation_products_components k n N i isVec B x.1.1 x.1.2 x.2.1 x.2.2.2.1 hi
  constructor
  · intro t ht
    have a1 := hx.1 ⟨n - 1, by omega⟩ (by simp only; omega)
    have a2 := h1 ⟨n - 1, by omega⟩ (by simp only; omega)
    rw [ht, WithBot.coe_le_coe] at a1
    exact (WithTop.coe_le_coe.2 a1).trans a2
  · intro t ht
    have a1 := hx.2 ⟨0, by omega⟩ rfl
    have a2 := h2 ⟨0, by omega⟩ rfl
    rw [ht, WithTop.coe_le_coe] at a1
    exact a2.trans (WithBot.coe_le_coe.2 a1)

def prodFam (k : Type) [Field k] (n i N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ) (M : WithTop ℤ)
    (p : {x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} × expSet n i N B) : MvPolynomial (ℕ × Fin n) k :=
  psiFam k n i isVec B p.1.1 * monomial p.2.1 1

theorem mem_spanProd (hT : LemmaA3top) (hF : FactSplit) (k : Type) [Field k] (hn : 1 ≤ n) {i N : ℕ} (hi : i ≤ N)
    (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ) (M : WithTop ℤ) (G : MvPolynomial (ℕ × Fin n) k)
    (hG : G ∈ polB k n N B) (hg : GoodG isVec i θ M G) :
    G ∈ Submodule.span k (Set.range (prodFam k n i N isVec B θ M)) := by
  obtain ⟨T, Gc, hTβ, hGc, hsum, hgood⟩ := hF k n N i isVec B θ M G hi hG
  rw [hsum]
  refine Submodule.sum_mem _ fun β hβ => ?_
  have hβe : β ∈ expSet n i N B := hTβ β hβ
  have hsp := hT k n i isVec B θ M (Gc β) hn (hGc β hβ) (hgood hg β hβ)
  have key : ∀ P ∈ Submodule.span k (psiFam k n i isVec B '' {x | GoodW θ M (x.1.1 i)}),
      P * monomial β 1 ∈ Submodule.span k (Set.range (prodFam k n i N isVec B θ M)) := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact Submodule.subset_span ⟨(⟨y, hy⟩, ⟨β, hβe⟩), rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [add_mul]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ a hx
  exact key _ hsp

theorem a3one_of_factSplit_of_countCont (hI : LemmaA2indep) (hfin : PathIdxFinite) (hR : PolBRank) (hT : LemmaA3top) (hF : FactSplit)
    (hC : CountCont) : LemmaA3one := by
  intro k _ n N i isVec B θ M G hn hi hG hg
  classical
  set S : Set (PathIdx n N isVec B) := {x | GoodW θ M (x.1.1 i)} with hS
  have hli : LinearIndependent k (psiFam k n N isVec B) := hI k n N isVec B
  haveI : Finite (PathIdx n N isVec B) := hfin n N isVec B
  haveI : Finite (PathIdx n i isVec B) := hfin n i isVec B
  haveI : Finite (expSet n i N B) := (expSet_finite hR n i N B).to_subtype
  haveI : Fintype S := Fintype.ofFinite _
  haveI : Fintype ({x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} × expSet n i N B) :=
    Fintype.ofFinite _
  have hle : Submodule.span k (psiFam k n N isVec B '' S) ≤
      Submodule.span k (Set.range (prodFam k n i N isVec B θ M)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact mem_spanProd hT hF k hn hi isVec B θ M _ (psiFam_mem k N isVec B x)
      (psiFam_good k hn hi isVec B θ M x hx)
  haveI hfd : FiniteDimensional k (Submodule.span k (Set.range (prodFam k n i N isVec B θ M))) := by
    first
      | exact FiniteDimensional.span_of_finite k (Set.finite_range _)
      | exact FiniteDimensional.span_of_finite (Set.finite_range _)
      | exact Module.Finite.span_of_finite k (Set.finite_range _)
      | infer_instance
  have hr1 : Module.finrank k (Submodule.span k (Set.range (prodFam k n i N isVec B θ M))) ≤
      Nat.card {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)} := by
    calc Module.finrank k (Submodule.span k (Set.range (prodFam k n i N isVec B θ M)))
        ≤ Fintype.card ({x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} × expSet n i N B) :=
          finrank_range_le_card (b := prodFam k n i N isVec B θ M)
      _ = Nat.card {x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} * Nat.card (expSet n i N B) := by
          rw [← Nat.card_eq_fintype_card, Nat.card_prod]
      _ ≤ Nat.card {x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} *
            ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) :=
          Nat.mul_le_mul le_rfl (by
            first
              | (rw [Nat.card_coe_set_eq]; exact expSet_card hR n i N B)
              | exact expSet_card hR n i N B)
      _ = Nat.card {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)} :=
          (card_good hC hi isVec B θ M).symm
  have hr2 : Module.finrank k (Submodule.span k (psiFam k n N isVec B '' S)) =
      Nat.card {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)} := by
    have h := finrank_span_eq_card
      (hli.comp (Subtype.val : S → PathIdx n N isVec B) Subtype.val_injective)
    rw [Set.range_comp, Subtype.range_coe, ← Nat.card_eq_fintype_card] at h
    exact h
  have heq := Submodule.eq_of_le_of_finrank_le hle (by rw [hr2]; exact hr1)
  rw [heq]
  exact mem_spanProd hT hF k hn hi isVec B θ M G hG hg

theorem good_zero (k : Type) [Field k] (isVec : ℕ → Bool) (i : ℕ) (θ : WithBot ℤ) (M : WithTop ℤ) :
    GoodG isVec i θ M (0 : MvPolynomial (ℕ × Fin n) k) := by
  refine ⟨fun t _ => ?_, fun t _ => ?_⟩
  · simp [valP, valS]
  · simp [lamP, lam1S]

theorem good_smul_add (k : Type) [Field k] (isVec : ℕ → Bool) (i : ℕ) (θ : WithBot ℤ) (M : WithTop ℤ) (c : k)
    (G H : MvPolynomial (ℕ × Fin n) k) (hG : GoodG isVec i θ M G) (hH : GoodG isVec i θ M H) :
    GoodG isVec i θ M (c • G + H) := by
  constructor
  · intro t ht
    have h := (cornerValSubmodule k ℕ Empty n isVec {j : ℕ | j < i} (t : WithTop ℤ) ⊥ c (rename Sum.inl G)
      (rename Sum.inl H)).1 (hG.1 t ht) (hH.1 t ht)
    rw [valP, map_add, map_smul]
    exact h
  · intro t ht
    have h := (cornerValSubmodule k ℕ Empty n isVec {j : ℕ | j < i} ⊤ (t : WithBot ℤ) c (rename Sum.inl G)
      (rename Sum.inl H)).2 (hG.2 t ht) (hH.2 t ht)
    rw [lamP, map_add, map_smul]
    exact h

theorem mem_span_inter {k V ι κ : Type*} [Field k] [AddCommGroup V] [Module k V] {v : ι → V}
    (hv : LinearIndependent k v) (A : κ → Set ι) (i₀ : κ) (G : V)
    (h : ∀ i, G ∈ Submodule.span k (v '' A i)) : G ∈ Submodule.span k (v '' {x | ∀ i, x ∈ A i}) := by
  have h' : ∀ i, ∃ l ∈ Finsupp.supported k k (A i), Finsupp.linearCombination k v l = G := by
    intro i
    have hi := h i
    rw [Finsupp.mem_span_image_iff_linearCombination] at hi
    exact hi
  choose l hl hlG using h'
  rw [Finsupp.mem_span_image_iff_linearCombination]
  refine ⟨l i₀, ?_, hlG i₀⟩
  rw [Finsupp.mem_supported]
  intro x hx i
  have e : l i = l i₀ := hv ((hlG i).trans (hlG i₀).symm)
  have hs := (Finsupp.mem_supported k (l i)).mp (hl i)
  exact hs (by rw [e]; exact hx)

theorem a3field_of_a2indep_of_a3one (hI : LemmaA2indep) (h1 : LemmaA3one) : LemmaA3field := by
  intro k _ n N isVec B θ M G hn
  have hli : LinearIndependent k (psiFam k n N isVec B) := hI k n N isVec B
  constructor
  · rintro ⟨hG, hg⟩
    have hsp : ∀ i : {i : ℕ // i ≤ N}, G ∈ Submodule.span k
        (psiFam k n N isVec B '' {x | GoodW (θ i.1) (M i.1) (x.1.1 i.1)}) :=
      fun i => h1 k n N i.1 isVec B (θ i.1) (M i.1) G hn i.2 hG (hg i.1 i.2)
    have hint : G ∈ Submodule.span k (psiFam k n N isVec B ''
        {x | ∀ i : {i : ℕ // i ≤ N}, GoodW (θ i.1) (M i.1) (x.1.1 i.1)}) :=
      mem_span_inter hli (fun i : {i : ℕ // i ≤ N} => {x | GoodW (θ i.1) (M i.1) (x.1.1 i.1)})
        ⟨0, Nat.zero_le _⟩ G hsp
    have hset : {x : PathIdx n N isVec B | ∀ i ≤ N, GoodW (θ i) (M i) (x.1.1 i)} =
        {x | ∀ i : {i : ℕ // i ≤ N}, GoodW (θ i.1) (M i.1) (x.1.1 i.1)} := by
      ext x
      simp only [Set.mem_setOf_eq, Subtype.forall]
    rw [hset]
    exact hint
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨psiFam_mem k N isVec B y, fun i hi => psiFam_good k hn hi isVec B (θ i) (M i) y (hy i hi)⟩
    | zero => exact ⟨Submodule.zero_mem _, fun i _ => good_zero k isVec i (θ i) (M i)⟩
    | add x y _ _ hx hy =>
      refine ⟨Submodule.add_mem _ hx.1 hy.1, fun i hi => ?_⟩
      have hxy := good_smul_add k isVec i (θ i) (M i) 1 x y (hx.2 i hi) (hy.2 i hi)
      rwa [one_smul] at hxy
    | smul a x _ hx =>
      refine ⟨Submodule.smul_mem _ a hx.1, fun i hi => ?_⟩
      have hax := good_smul_add k isVec i (θ i) (M i) a x 0 (hx.2 i hi) (good_zero k isVec i (θ i) (M i))
      rwa [add_zero] at hax

end ExponentSetCounting

theorem lemmaA3one_of : LemmaA2indep → PathIdxFinite → PolBRank → LemmaA3top → FactSplit → CountCont →
    StdCountGT → LemmaA3one :=
  fun hI hfin hR hT hF hC _ => ExponentSetCounting.a3one_of_factSplit_of_countCont hI hfin hR hT hF hC

theorem lemmaA3field_of : LemmaA2indep → LemmaA3one → LemmaA3field :=
  ExponentSetCounting.a3field_of_a2indep_of_a3one

end Formalism.InvariantFactorPaths.GelfandTsetlinBases

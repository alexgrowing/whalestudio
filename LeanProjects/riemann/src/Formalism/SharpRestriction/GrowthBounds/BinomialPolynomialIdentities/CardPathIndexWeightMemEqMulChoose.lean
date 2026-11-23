import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.RestSplit

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.InvariantFactorPaths.GelfandTsetlinBases

variable {n : ℕ}

def PathsWithInitialLettersEndingIn (n i : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (pi : Set (Fin n → ℤ)) : Type :=
  {μ : ℕ → Fin n → ℤ // IsPath n isVec B μ i ∧ (∀ j, i < j → μ j = 0) ∧ (μ i) ∈ pi}

def pathIndexSplitEquiv {i N : ℕ} (hi : i ≤ N) (isVec : ℕ → Bool) (B : ℕ → ℕ) (pi : Set (Fin n → ℤ)) :
    {x : PathIdx n N isVec B // (x.1.1 i) ∈ pi} ≃
      Σ P : PathsWithInitialLettersEndingIn n i isVec B pi, {x // ExponentSetCounting.ContP i N isVec B (P.1 i) x} where
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
            Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip (if j + 1 ≤ i then μ (j + 1) else ν (j + 1)) (if j ≤ i then μ j else ν j) (B j)
          else Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip (if j ≤ i then μ j else ν j) (if j + 1 ≤ i then μ (j + 1) else ν (j + 1)) (B j) := by
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

theorem card_pathIndex_weight_mem_eq_mul_choose (hC : CountCont) {i N : ℕ} (hi : i ≤ N) (isVec : ℕ → Bool) (B : ℕ → ℕ) (pi : Set (Fin n → ℤ)) :
    Nat.card {x : PathIdx n N isVec B // (x.1.1 i) ∈ pi} =
      Nat.card {x : PathIdx n i isVec B // (x.1.1 i) ∈ pi} *
        ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) := by
  set c : ℕ := ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) with hc
  have e : ∀ P : PathsWithInitialLettersEndingIn n i isVec B pi,
      Nonempty ({x // ExponentSetCounting.ContP i N isVec B (P.1 i) x} ≃ {x // ExponentSetCounting.ContP i i isVec B (P.1 i) x} × Fin c) := by
    intro P
    have hP : Antitone (P.1 i) := P.2.1.2.1 i le_rfl
    obtain ⟨f1, c1⟩ := hC n i N isVec B (P.1 i) hi hP
    obtain ⟨f2, c2⟩ := hC n i i isVec B (P.1 i) le_rfl hP
    have f1' : Finite {x // ExponentSetCounting.ContP i N isVec B (P.1 i) x} := f1
    have f2' : Finite {x // ExponentSetCounting.ContP i i isVec B (P.1 i) x} := f2
    have c1' : Nat.card {x // ExponentSetCounting.ContP i N isVec B (P.1 i) x} = dGT n (P.1 i) * c := c1
    have c2' : Nat.card {x // ExponentSetCounting.ContP i i isVec B (P.1 i) x} = dGT n (P.1 i) := by
      have : Nat.card {x // ExponentSetCounting.ContP i i isVec B (P.1 i) x} = _ := c2
      simpa using this
    apply Finite.card_eq.1
    rw [Nat.card_prod, c1', c2', Nat.card_fin]
  rw [Nat.card_congr (pathIndexSplitEquiv hi isVec B pi),
    Nat.card_congr (Equiv.sigmaCongrRight fun P => (e P).some),
    ← Nat.card_congr (Equiv.sigmaProdDistrib _ _), Nat.card_prod, Nat.card_fin,
    ← Nat.card_congr (pathIndexSplitEquiv le_rfl isVec B pi)]

theorem standardWordFamily_satisfies_condition (hW : RestWord) (k : Type) [Field k] {i N : ℕ} (hi : i ≤ N) (isVec : ℕ → Bool) (B : ℕ → ℕ)
    (pi : Set (Fin n → ℤ)) (hpi : LowerC pi) (x : PathIdx n N isVec B) (hx : x.1.1 i ∈ pi) :
    GoodC k isVec i pi (psiFam k n N isVec B x) := by
  intro e he ha
  rw [psiFam, A3ev.map_psi (algebraMap k (GenField k n)) x.2.1 x.2.2.2.1] at he
  exact hpi _ hx _ ha (hW (GenField k n) n N i isVec B x.1.1 x.1.2 _ _
    (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (A3ev.genMat_det_ne k n))) x.2.1 x.2.2.2.1 hi e he)

def pathExponentMonomial (k : Type) [Field k] (n i N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (pi : Set (Fin n → ℤ))
    (p : {x : PathIdx n i isVec B // x.1.1 i ∈ pi} × ExponentSetCounting.expSet n i N B) : MvPolynomial (ℕ × Fin n) k :=
  psiFam k n i isVec B p.1.1 * monomial p.2.1 1

theorem mem_span_wordMonomialProducts (hT : RestTop) (hF : RestSplit) (k : Type) [Field k] {i N : ℕ} (hi : i ≤ N)
    (isVec : ℕ → Bool) (B : ℕ → ℕ) (pi : Set (Fin n → ℤ)) (hpi : LowerC pi) (G : MvPolynomial (ℕ × Fin n) k)
    (hG : G ∈ polB k n N B) (hg : GoodC k isVec i pi G) :
    G ∈ Submodule.span k (Set.range (pathExponentMonomial k n i N isVec B pi)) := by
  obtain ⟨T, Gc, h1, h2, h3, h4⟩ := hF k n N i isVec B pi G hi hG
  rw [h3]
  refine Submodule.sum_mem _ fun β hβ => ?_
  have hm := hT k n i isVec B pi (Gc β) hpi (h2 β hβ) (h4 hg β hβ)
  have hle : Submodule.map (LinearMap.mulRight k (monomial β (1 : k)))
      (Submodule.span k (psiFam k n i isVec B '' {x | x.1.1 i ∈ pi})) ≤
      Submodule.span k (Set.range (pathExponentMonomial k n i N isVec B pi)) := by
    rw [Submodule.map_span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨(⟨x, hx⟩, ⟨β, h1 β hβ⟩), rfl⟩
  exact hle (Submodule.mem_map_of_mem (f := LinearMap.mulRight k (monomial β (1 : k))) hm)

theorem restOne_of (hW : RestWord) (hT : RestTop) (hF : RestSplit) : RestOne := by
  intro k _ n N i isVec B pi G hpi hi hG hg
  have hI : LemmaA2indep := Top.lemmaA2indep
  have hR : PolBRank := Top.polBRank
  have hC : CountCont := Top.countCont
  have : Finite (PathIdx n N isVec B) := Top.pathIdxFinite n N isVec B
  have : Finite (PathIdx n i isVec B) := Top.pathIdxFinite n i isVec B
  have : Finite (ExponentSetCounting.expSet n i N B) := (ExponentSetCounting.expSet_finite hR n i N B).to_subtype
  let _ := Fintype.ofFinite {x : PathIdx n N isVec B // x.1.1 i ∈ pi}
  let _ := Fintype.ofFinite ({x : PathIdx n i isVec B // x.1.1 i ∈ pi} × ExponentSetCounting.expSet n i N B)
  set U := Submodule.span k (Set.range fun x : {x : PathIdx n N isVec B // x.1.1 i ∈ pi} =>
    psiFam k n N isVec B x.1) with hU
  set W := Submodule.span k (Set.range (pathExponentMonomial k n i N isVec B pi)) with hWd
  have hUW : U ≤ W := by
    rw [hU, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact mem_span_wordMonomialProducts hT hF k hi isVec B pi hpi _ (ExponentSetCounting.psiFam_mem k N isVec B x.1)
      (standardWordFamily_satisfies_condition hW k hi isVec B pi hpi x.1 x.2)
  have hli : LinearIndependent k (fun x : {x : PathIdx n N isVec B // x.1.1 i ∈ pi} =>
      psiFam k n N isVec B x.1) := (hI k n N isVec B).comp Subtype.val Subtype.val_injective
  have dU : Module.finrank k U = Fintype.card {x : PathIdx n N isVec B // x.1.1 i ∈ pi} :=
    finrank_span_eq_card hli
  have dW : Module.finrank k W ≤
      Fintype.card ({x : PathIdx n i isVec B // x.1.1 i ∈ pi} × ExponentSetCounting.expSet n i N B) :=
    finrank_range_le_card _
  have : FiniteDimensional k W := FiniteDimensional.span_of_finite k (Set.finite_range _)
  have hEq : U = W := Submodule.eq_of_le_of_finrank_le hUW (by
    rw [dU]
    refine dW.trans ?_
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_prod, card_pathIndex_weight_mem_eq_mul_choose hC hi]
    exact Nat.mul_le_mul_left _ (by rw [Nat.card_coe_set_eq]; exact ExponentSetCounting.expSet_card hR n i N B))
  have hGW : G ∈ W := mem_span_wordMonomialProducts hT hF k hi isVec B pi hpi G hG hg
  rw [← hEq, hU] at hGW
  rw [Set.image_eq_range]
  exact hGW

theorem partialAction_X {L : Type*} [CommRing L] (isVec : ℕ → Bool) (i : ℕ) (g gi : Matrix (Fin n) (Fin n) L)
    (x : ℕ × Fin n) :
    actI isVec i g gi (X x) = if x.1 < i then
      (if isVec x.1 then ∑ b, X (x.1, b) * C (g b x.2) else ∑ b, X (x.1, b) * C (gi x.2 b)) else X x := by
  unfold actI
  rw [aeval_X]

theorem partialAction_eq_fullAction_of_vars_lt {L : Type*} [CommRing L] (isVec : ℕ → Bool) (i : ℕ) (g gi : Matrix (Fin n) (Fin n) L)
    {P : MvPolynomial (ℕ × Fin n) L} (hv : ∀ x ∈ P.vars, x.1 < i) :
    actI isVec i g gi P = actAll isVec g gi P := by
  have h : (actI isVec i g gi).toRingHom P = (actAll isVec g gi).toRingHom P := by
    refine hom_congr_vars ?_ ?_ rfl
    · ext c
      simp
    · rintro ⟨j, a⟩ hx -
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [partialAction_X, DominanceOrderLemmas.actAll_X, if_pos (hv _ hx)]
  exact h

theorem partialAction_monomial_later_letters {L : Type*} [CommRing L] (isVec : ℕ → Bool) (i : ℕ) (g gi : Matrix (Fin n) (Fin n) L)
    (β : ℕ × Fin n →₀ ℕ) (hβ : ∀ x : ℕ × Fin n, x.1 < i → β x = 0) :
    actI isVec i g gi (monomial β 1) = monomial β 1 := by
  unfold actI
  rw [aeval_monomial, monomial_eq, MvPolynomial.algebraMap_eq]
  congr 1
  refine Finsupp.prod_congr fun x hx => ?_
  have : ¬ x.1 < i := fun h => (Finsupp.mem_support_iff.1 hx) (hβ x h)
  rw [if_neg this]

theorem restSplit : RestSplit := by
  classical
  intro k _ n N i isVec B pi G hi hG
  obtain ⟨T, Gc, h1, h2, h3, -⟩ := Top.factSplit k n N i isVec B ⊥ ⊤ G hi hG
  refine ⟨T, Gc, h1, h2, h3, ?_⟩
  intro hg β₀ hβ₀ e he ha
  have hlow : ∀ β ∈ T, ∀ x : ℕ × Fin n, x.1 < i → β x = 0 := by
    intro β hβ x hx
    have h0 := h1 β hβ x.1
    rw [if_neg (by omega)] at h0
    exact (Finset.sum_eq_zero_iff.1 h0) x.2 (Finset.mem_univ _)
  have hexp : actI isVec i (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
        (map (algebraMap k (GenField k n)) G) =
      ∑ β ∈ T, actI isVec i (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
        (map (algebraMap k (GenField k n)) (Gc β)) * monomial β 1 := by
    conv_lhs => rw [h3]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [map_mul, map_mul, map_monomial, map_one, partialAction_monomial_later_letters _ _ _ _ β (hlow β hβ)]
  have hvars : ∀ β ∈ T, ∀ d ∈ (actI isVec i (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
        (map (algebraMap k (GenField k n)) (Gc β))).support, ∀ x : ℕ × Fin n, i ≤ x.1 → d x = 0 := by
    intro β hβ d hd x hx
    by_contra hne
    have hv0 : ∀ y ∈ (map (algebraMap k (GenField k n)) (Gc β)).vars, y.1 < i :=
      fun y hy => DominanceOrderLemmas.vars_of_polB (h2 β hβ) y (vars_map (Gc β) (algebraMap k (GenField k n)) hy)
    rw [partialAction_eq_fullAction_of_vars_lt _ _ _ _ hv0] at hd
    have := DominanceOrderLemmas.vars_act isVec (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹ hv0 x
      ((mem_vars_iff_mem_support (i := x)).2 ⟨d, hd, Finsupp.mem_support_iff.2 hne⟩)
    omega
  have hcoef : coeff (e + β₀) (actI isVec i (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
        (map (algebraMap k (GenField k n)) G)) =
      coeff e (actI isVec i (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
        (map (algebraMap k (GenField k n)) (Gc β₀))) := by
    rw [hexp, coeff_sum, Finset.sum_eq_single β₀]
    · rw [coeff_mul_monomial, mul_one]
    · intro β hβ hne
      rw [coeff_mul_monomial']
      split_ifs with hle
      · rw [mul_one]
        by_contra hc
        apply hne
        have hz := hvars β hβ (e + β₀ - β) (mem_support_iff.2 hc)
        ext x
        by_cases hx : x.1 < i
        · rw [hlow β hβ x hx, hlow β₀ hβ₀ x hx]
        · have e0 := hvars β₀ hβ₀ e he x (by omega)
          have a1 := hz x (by omega)
          have a2 := hle x
          simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply] at a1 a2
          omega
      · rfl
    · intro h
      exact absurd hβ₀ h
  have hmem : e + β₀ ∈ (actI isVec i (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
        (map (algebraMap k (GenField k n)) G)).support := by
    rw [mem_support_iff, hcoef]
    exact mem_support_iff.1 he
  have hw : Finsupp.weight (wtI isVec i) (e + β₀) = Finsupp.weight (wtI isVec i) e := by
    have h0 : Finsupp.weight (wtI (n := n) isVec i) β₀ = 0 := by
      rw [Finsupp.weight_apply, Finsupp.sum]
      refine Finset.sum_eq_zero fun x hx => ?_
      have : ¬ x.1 < i := fun h => (Finsupp.mem_support_iff.1 hx) (hlow β₀ hβ₀ x h)
      simp [wtI, this]
    rw [map_add, h0, add_zero]
  have hfin := hg (e + β₀) hmem (by rw [hw]; exact ha)
  rwa [hw] at hfin

theorem restOne_of' (hW : RestWord) (hT : RestTop) : RestOne := restOne_of hW hT restSplit

end Formalism.MainNotions.G.ColumnFamilies

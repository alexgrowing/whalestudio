import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInductionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicInductionDetCharactersRankOneEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTensorEquivLeviCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfSStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CountBindWordShuffleByPositionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonBorelJacquetOfCuspidalSegmentJacquetStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUnStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnramifiedExponentOfIwahoriFixedVectorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedCharSumsStrictConeVanishEachStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShuffleCountLinearIndependentClassesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetWordMultiplicityAdditiveJordanHolderStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityLeviCharGeometricLemmaCeStatement

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

noncomputable section

namespace GlobalTheory.SmGL.Exponents

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_strictMono_blk {n : ℕ} (c : Fin n → ℕ) (hc : ∀ j, c j ≤ 1) {r : ℕ} (h : ∑ j, c j = r) :
    ∃ f : (Σ j, Fin (c j)) ≃ Fin r, StrictMono (blk f) := by
  have hS : (Finset.univ.filter fun j => c j = 1).card = r := by
    rw [← h, Finset.card_filter]
    exact Finset.sum_congr rfl fun j _ => by have := hc j; split_ifs <;> omega
  let φ : Fin r → Σ j, Fin (c j) := fun i => ⟨Finset.orderEmbOfFin _ hS i, 0, by
    have := (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem _ hS i)).2
    omega⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun i j e => (Finset.orderEmbOfFin _ hS).injective (congrArg Sigma.fst e), ?_⟩
    rintro ⟨j, x⟩
    have hj : j ∈ Set.range (Finset.orderEmbOfFin _ hS) := by
      rw [Finset.range_orderEmbOfFin]
      have := hc j
      have := x.2
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      omega
    obtain ⟨i, rfl⟩ := hj
    refine ⟨i, congrArg (Sigma.mk _) (Fin.ext ?_)⟩
    have := hc (Finset.orderEmbOfFin _ hS i)
    have := x.2
    simp only
    omega
  exact ⟨(Equiv.ofBijective φ hφ).symm, (Finset.orderEmbOfFin _ hS).strictMono⟩

theorem ofFn_blk {n r : ℕ} {c : Fin n → ℕ} (f : (Σ j, Fin (c j)) ≃ Fin r) (hf : StrictMono (blk f))
    (p : Fin n → Bool) (hp : ∀ j, p j = true ↔ c j ≠ 0) :
    List.ofFn (blk f) = (List.finRange n).filter p := by
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) (List.pairwise_ofFn.2 fun i j h => hf h)
    ((List.pairwise_lt_finRange n).filter _) fun j => ?_
  simp only [List.mem_ofFn, List.mem_filter, List.mem_finRange, true_and, hp]
  constructor
  · rintro ⟨i, rfl⟩
    exact (f.symm i).2.pos.ne'
  · exact fun h => ⟨f ⟨j, 0, Nat.pos_of_ne_zero h⟩, blk_apply _ _ _⟩

theorem length_filter_finRange {n : ℕ} (p : Fin n → Bool) :
    ((List.finRange n).filter p).length = ∑ j, if p j = true then 1 else 0 := by
  rw [Fin.sum_univ_def]
  induction List.finRange n with
  | nil => rfl
  | cons a l ih => by_cases h : p a = true <;> simp [h, ih, add_comm]

theorem wordMult_prod₂ (hG : JacquetOfInducedFiltration k) (hC : CellSemisimplification k) {r t : ℕ}
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π₁ : Representation ℂ (GL (Fin r) k) V} {π₂ : Representation ℂ (GL (Fin t) k) W}
    (s₁ : IsSmooth π₁) (s₂ : IsSmooth π₂) (h₁ : HasFiniteLength π₁) (h₂ : HasFiniteLength π₂)
    (w : Fin (r + t) → ℂˣ) :
    wordMult (prod₂ π₁ π₂) (List.ofFn w) = ∑ ε : Fin (r + t) → Bool,
      wordMult π₁ (((List.finRange (r + t)).filter fun j => !ε j).map w) *
        wordMult π₂ (((List.finRange (r + t)).filter ε).map w) := by
  classical
  let B := SizeMatrix (Two (Fin r) (Fin t)) fun _ : Fin (r + t) => Unit
  letI : Fintype B := Fintype.ofFinite _
  have hcol : ∀ (b : B) j, b.1 true j + b.1 false j = 1 := fun b j => by simpa using b.2.2 j
  have hf : ∀ b : B, ∃ f : (Σ j, Fin (b.1 false j)) ≃ Fin r, StrictMono (blk f) := fun b =>
    exists_strictMono_blk _ (fun j => by have := hcol b j; omega)
      ((b.2.1 false).trans (Fintype.card_fin r))
  have ht : ∀ b : B, ∃ f : (Σ j, Fin (b.1 true j)) ≃ Fin t, StrictMono (blk f) := fun b =>
    exists_strictMono_blk _ (fun j => by have := hcol b j; omega)
      ((b.2.1 true).trans (Fintype.card_fin t))
  choose f₁ hf₁ using hf
  choose f₂ hf₂ using ht
  let f : ∀ (b : B) i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin r) (Fin t) i := fun b i =>
    match i with
    | false => f₁ b
    | true => f₂ b
  have hs : ∀ i, IsSmooth (twoRep π₁ π₂ i) := by
    rintro (_ | _)
    exacts [s₁, s₂]
  have hl : ∀ i, HasFiniteLength (twoRep π₁ π₂ i) := by
    rintro (_ | _)
    exacts [h₁, h₂]
  obtain ⟨φ⟩ := T.parabolicProductTwoReps_equiv_two_block_induction k r t V W π₁ π₂
  have e1 := T.jordanHolderMultiplicity_jacquet_eq_borelJacquet_of_small k (Fin (r + t)) (Fin (r + t)) (fun _ => Unit) (points _) (fun _ _ h => h) _
    (prod₂ π₁ π₂) fun j => unrChar k (w j)
  rw [wordMult_ofFn]
  refine e1.symm.trans ((jhMult_congr_right _ (jacEquiv _ φ)).trans
    ((hG.jhMult_eq _ _ (isSmooth_piTensor hs) f (fun b => b.nonempty_cols.some)
      (isIrreducible_ofChar _)).trans ?_))
  refine Fintype.sum_of_injective (fun (b : B) j => decide (b.1 true j = 1)) ?_ _ _ ?_ fun b => ?_
  · intro b b' e
    refine Subtype.ext (funext fun i => funext fun j => ?_)
    have h1 := hcol b j
    have h2 := hcol b' j
    have h3 : b.1 true j = 1 ↔ b'.1 true j = 1 := by simpa using congrFun e j
    cases i <;> omega
  · intro ε hε
    by_contra h0
    have h1 := left_ne_zero_of_mul h0
    have h2 := right_ne_zero_of_mul h0
    replace h1 := not_not.1 fun h => h1 (wordMult_of_ne _ h)
    replace h2 := not_not.1 fun h => h2 (wordMult_of_ne _ h)
    rw [List.length_map, length_filter_finRange] at h1 h2
    refine hε ⟨⟨fun i j => if ε j = i then 1 else 0, ?_, fun j => ?_⟩, ?_⟩
    · rintro (_ | _)
      · exact Eq.trans (by simp) (h1.trans (Fintype.card_fin r).symm)
      · exact h2.trans (Fintype.card_fin t).symm
    · cases ε j <;> simp
    · funext j
      simp
  · rw [T.jordanHolderMultiplicity_leviChar_geometricLemmaCell k hC Bool (Fin (r + t)) _ (fun i j => Fin (b.1 i j)) (f b) _ _ _ hs hl _
      fun j => isSmoothChar_of_isUnram (isUnram_unrChar k _), Fintype.prod_bool, mul_comm,
      ← ofFn_blk (f₁ b) (hf₁ b) _ fun j => by have := hcol b j; simp; omega,
      ← ofFn_blk (f₂ b) (hf₂ b) _ fun j => by have := hcol b j; simp; omega,
      List.map_ofFn, List.map_ofFn, wordMult_ofFn, wordMult_ofFn]
    exact congrArg₂ (· * ·) (T.jordanHolderMultiplicity_jacquet_eq_borelJacquet_of_small k _ _ _ (f₁ b) (hf₁ b) _ π₁ _)
      (T.jordanHolderMultiplicity_jacquet_eq_borelJacquet_of_small k _ _ _ (f₂ b) (hf₂ b) _ π₂ _)

end GlobalTheory.SmGL.Exponents

namespace GlobalTheory.SmGL.Exponents

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nonempty_jacB_detRep (N : ℕ) (ψ : kˣ →* ℂˣ) :
    Nonempty ((jacB (detRep (Fin N) ψ)).Equiv (ofChar (torusChar fun i : Fin N =>
      ψ * absPow k (((i : ℕ) : ℂ) - ((N : ℂ) - 1) / 2)))) := by
  refine ⟨.mk (Submodule.quotEquivOfEqBot _ (twKer_detRep (points (Fin N)) ψ)) fun t => ?_⟩
  refine LinearMap.ext fun x => ?_
  have h : jacB (detRep (Fin N) ψ) t x =
      (detLevi (points (Fin N)) ψ (leviTorus k (Fin N) t) : ℂ) • x :=
    Model.jac_detRep (points (Fin N)) ψ _ x
  have hd : ∀ i, Matrix.GeneralLinearGroup.det (leviTorus k (Fin N) t i) = t i :=
    congrFun ((leviTorus k (Fin N)).left_inv t)
  simp only [LinearMap.comp_apply]
  rw [h, map_smul, ofChar_apply, detLevi_apply, torusChar_apply, smul_eq_mul]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hd, modExp_fin _ (fun _ => by simp)]
  congr 3
  push_cast
  ring

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem torusChar_mulSingle {n : Type} [Fintype n] [DecidableEq n] (χ : n → kˣ →* ℂˣ) (i : n)
    (x : kˣ) : torusChar χ (Pi.mulSingle i x) = χ i x := by
  rw [torusChar_apply, Finset.prod_eq_single i, Pi.mulSingle_eq_same]
  · intro j _ hj
    rw [Pi.mulSingle_eq_of_ne hj, map_one]
  · simp

open Classical in

theorem wordMult_detRep (N : ℕ) (ψ : kˣ →* ℂˣ) (w : List ℂˣ) :
    wordMult (detRep (Fin N) ψ) w = if w.length = N ∧ ∀ i < N, unrChar k (w.getD i 1) =
      ψ * absPow k ((i : ℂ) - ((N : ℂ) - 1) / 2) then 1 else 0 := by
  obtain ⟨φ⟩ := nonempty_jacB_detRep N ψ
  by_cases hw : w.length = N
  swap
  · rw [wordMult_of_ne _ hw, if_neg fun h => hw h.1]
  rw [wordMult, if_pos hw, jhMult_congr_right _ φ]
  split_ifs with h
  · rw [show (fun i : Fin N => unrChar k (w.getD i 1)) = _ from funext fun i => h.2 i i.2]
    exact jhMult_self (isIrreducible_ofChar _)
  · refine Model.jhMult_ofChar_ne fun h' => h ⟨hw, fun i hi => MonoidHom.ext fun x => ?_⟩
    have := DFunLike.congr_fun h' (Pi.mulSingle ⟨i, hi⟩ x)
    rwa [torusChar_mulSingle, torusChar_mulSingle] at this

def segWord (q z : ℂˣ) (l : ℕ) : List ℂˣ := (List.range l).map fun a => z * q ^ a

theorem segWord_inj {q z z' : ℂˣ} {l l' : ℕ} (hl : 0 < l) (h : segWord q z l = segWord q z' l') :
    z = z' ∧ l = l' := by
  obtain rfl : l = l' := by simpa [segWord] using congrArg List.length h
  exact ⟨by simpa using List.map_inj_left.1 h 0 (by simpa using hl), rfl⟩

theorem wordMult_segment {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z)
    [DecidableEq ℂˣ] (Δ : Segment k) :
    (∃ (z : ℂˣ) (l : ℕ) (hl : 0 < l),
      Δ = Segment.ofChar (unrChar k z) (isSmoothChar_of_isUnram (isUnram_unrChar k z)) l hl ∧
      ∀ w, wordMult (Z Δ).rep.ρ w =
        (({segWord (absPow k 1 ϖ) z l} : Multiset (List ℂˣ)).count w : ℕ∞)) ∨
    ∀ w, wordMult (Z Δ).rep.ρ w = 0 := by
  obtain ⟨d, hd, _, ⟨σ, rfl, hσ⟩, l, hl⟩ := Δ
  rcases (show 1 < d ∨ d = 1 by omega) with h1 | rfl
  · refine Or.inr fun w => ?_
    have := T.subsingleton_borelJacquet_of_cuspidal_segment_jacquet k l d hl h1 _ _ σ.ρ (Z ⟨d, hd, _, ⟨σ, rfl, hσ⟩, l, hl⟩).rep.ρ hσ fun e =>
      (hZ ⟨d, hd, _, ⟨σ, rfl, hσ⟩, l, hl⟩ σ rfl e _).2.1 (IrrCl.cl_rep _)
    unfold wordMult
    split_ifs
    · exact jhMult_of_subsingleton (isIrreducible_ofChar _) _
    · rfl
  obtain ⟨χ, hχ, ⟨φ⟩⟩ := T.exists_equiv_detCharacter_of_irreducible_rank_le_one k (Fin 1) _ σ.ρ σ.smooth σ.irr
  have e : (⟨1, hd, _, ⟨σ, rfl, hσ⟩, l, hl⟩ : Segment k) = Segment.ofChar χ hχ l hl := by
    have : σ.cl = (IrrRep.det (Fin 1) χ hχ).cl := IrrRep.cl_eq_iff.2 ⟨φ⟩
    unfold Segment.ofChar
    congr 1
  rw [e]
  have key : ∀ w, wordMult (Z (Segment.ofChar χ hχ l hl)).rep.ρ w =
      open Classical in if w.length = l ∧ ∀ i < l, unrChar k (w.getD i 1) = χ * absPow k (i : ℂ)
        then 1 else 0 := fun w => by
    rw [hZ.ofChar hχ hl]
    refine (wordMult_congr (IrrRep.nonempty_equiv_rep _).some w).trans
      ((wordMult_detRep (l * 1) _ w).trans ?_)
    have : ∀ i : ℕ, χ * absPow k (((l : ℂ) - 1) / 2) * absPow k ((i : ℂ) - ((l : ℂ) - 1) / 2) =
        χ * absPow k (i : ℂ) := fun i => by
      rw [mul_assoc, ← absPow_add]; congr 2; ring
    refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ rfl rfl
    rw [mul_one]
    simp only [this]
  by_cases hu : IsUnram χ
  swap
  · refine Or.inr fun w => (key w).trans (if_neg fun h => hu ?_)
    have := h.2 0 hl
    rw [Nat.cast_zero, absPow_zero, mul_one] at this
    exact this ▸ isUnram_unrChar k _
  refine Or.inl ⟨χ ϖ, l, hl, by congr 1; exact eq_unrChar hu hϖ, fun w => (key w).trans ?_⟩
  have hp : ∀ i : ℕ, χ * absPow k (i : ℂ) = unrChar k (χ ϖ * absPow k 1 ϖ ^ i) := fun i => by
    have h1 : IsUnram (χ * absPow k (i : ℂ)) := fun x hx => by
      rw [MonoidHom.mul_apply, hu x hx, isUnram_absPow k _ x hx, one_mul]
    rw [eq_unrChar h1 hϖ, MonoidHom.mul_apply]
    congr 2
    ext
    simp [val_absPow]
  have hi : ∀ a b : ℂˣ, unrChar k a = unrChar k b ↔ a = b := fun a b =>
    ⟨fun h => by rw [← unrChar_uniformizer k a hϖ, h, unrChar_uniformizer k b hϖ], congrArg _⟩
  simp only [hp, hi, Multiset.count_singleton]
  have : (w.length = l ∧ ∀ i < l, w.getD i 1 = χ ϖ * absPow k 1 ϖ ^ i) ↔
      w = segWord (absPow k 1 ϖ) (χ ϖ) l := by
    constructor
    · rintro ⟨rfl, h⟩
      refine List.ext_getElem (by simp [segWord]) fun i h1 h2 => ?_
      have := h i h1
      rw [List.getD_eq_getElem _ _ h1] at this
      simp [segWord, this]
    · rintro rfl
      exact ⟨by simp [segWord], fun i hi => by simp [segWord, hi]⟩
  by_cases h : w = segWord (absPow k 1 ϖ) (χ ϖ) l
  · rw [if_pos (this.2 h), if_pos h, Nat.cast_one]
  · rw [if_neg fun h' => h (this.1 h'), if_neg h, Nat.cast_zero]

def Realised [DecidableEq ℂˣ] (Ψ : GrothGL k ≃+ MvPolynomial (Segment k) ℤ)
    (P : MvPolynomial (Segment k) ℤ) (y : ShuffleAlgebra ℚ ℂˣ) : Prop :=
  ∃ (n : ℕ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (π : Representation ℂ (GL (Fin n) k) V)
    (h : HasFiniteLength π), IsSmooth π ∧ Ψ (clsGL π h) = P ∧ ∃ s : Multiset (List ℂˣ),
      (∀ w, wordMult π w = (s.count w : ℕ∞)) ∧ (s.map (ShuffleAlgebra.word ℚ)).sum = y

variable [DecidableEq ℂˣ] {Ψ : GrothGL k ≃+ MvPolynomial (Segment k) ℤ}

theorem Realised.one (hΨ : IsProductIso k Ψ) : Realised Ψ 1 1 := by
  let σ : IrrRep (GL (Fin 0) k) := IrrRep.det (Fin 0) 1 isSmoothChar_one
  refine ⟨0, _, _, _, σ.ρ, σ.hasFiniteLength, σ.smooth, by rw [clsGL_irr]; exact hΨ.1, {[]},
    fun w => (wordMult_detRep 0 1 w).trans ?_, by simp [ShuffleAlgebra.word_nil]⟩
  cases w <;> simp

theorem Realised.mul (hG : JacquetOfInducedFiltration k) (hC : CellSemisimplification k)
    (hΨ : IsProductIso k Ψ) {P Q : MvPolynomial (Segment k) ℤ} {x y : ShuffleAlgebra ℚ ℂˣ}
    (hP : Realised Ψ P x) (hQ : Realised Ψ Q y) : Realised Ψ (P * Q) (x * y) := by
  obtain ⟨r, V, _, _, π₁, h₁, s₁, rfl, a, ha, rfl⟩ := hP
  obtain ⟨t, W, _, _, π₂, h₂, s₂, rfl, b, hb, rfl⟩ := hQ
  obtain ⟨h, e⟩ := hΨ.2 r t V W π₁ π₂ h₁ h₂ s₁ s₂
  refine ⟨r + t, _, _, _, prod₂ π₁ π₂, h, isSmooth_prod₂ _ _, e,
    a.bind fun u => b.bind fun v => Shuffle.shuffle u v, fun w => ?_, ?_⟩
  · by_cases hw : w.length = r + t
    · obtain ⟨z, rfl⟩ : ∃ z : Fin (r + t) → ℂˣ, w = List.ofFn z :=
        ⟨fun i => w.get (i.cast hw.symm), List.ext_getElem (by simp [hw]) fun i h1 h2 => by simp⟩
      rw [wordMult_prod₂ hG hC s₁ s₂ h₁ h₂, T.count_bind_wordShuffle_by_positions]
      simp [ha, hb]
    · rw [wordMult_of_ne _ hw, Multiset.count_eq_zero.2, Nat.cast_zero]
      simp only [Multiset.mem_bind]
      rintro ⟨u, hu, v, hv, h⟩
      have hu' : u.length = r := by
        by_contra hn
        have := (ha u).symm.trans (wordMult_of_ne _ hn)
        exact Multiset.count_eq_zero.1 (Nat.cast_eq_zero.1 this) hu
      have hv' : v.length = t := by
        by_contra hn
        have := (hb v).symm.trans (wordMult_of_ne _ hn)
        exact Multiset.count_eq_zero.1 (Nat.cast_eq_zero.1 this) hv
      exact hw (by simpa [hu', hv'] using (Shuffle.perm_of_mem_shuffle u v w h).length_eq)
  · simp only [Multiset.map_bind, Multiset.sum_bind, ← ShuffleAlgebra.word_mul_word,
      Multiset.sum_map_mul_left, Multiset.sum_map_mul_right]

theorem Realised.monomial (hG : JacquetOfInducedFiltration k) (hC : CellSemisimplification k)
    (hΨ : IsProductIso k Ψ) {φ : Segment k → ShuffleAlgebra ℚ ℂˣ}
    (hX : ∀ Δ, Realised Ψ (MvPolynomial.X Δ) (φ Δ)) (m : Segment k →₀ ℕ) :
    Realised Ψ (MvPolynomial.monomial m 1) (m.prod fun Δ e => φ Δ ^ e) := by
  have hp : ∀ Δ e, Realised Ψ (MvPolynomial.X Δ ^ e) (φ Δ ^ e) := fun Δ e => by
    induction e with
    | zero => simpa using Realised.one hΨ
    | succ e ih => rw [pow_succ, pow_succ]; exact ih.mul hG hC hΨ (hX Δ)
  induction m using Finsupp.induction_linear with
  | zero => simpa using Realised.one hΨ
  | add a b ha hb =>
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _]
    simpa using ha.mul hG hC hΨ hb
  | single Δ e =>
    rw [Finsupp.prod_single_index (h := fun Δ e => φ Δ ^ e) (pow_zero _), ← MvPolynomial.X_pow_eq_monomial]
    exact hp Δ e

theorem Realised.effective {P : MvPolynomial (Segment k) ℤ} {y : ShuffleAlgebra ℚ ℂˣ}
    (h : Realised Ψ P y) : 0 ≤ Ψ.symm P ∧ ∃ s : Multiset (List ℂˣ),
      (∀ w, ((Ψ.symm P).sum fun x a => (a.toNat : ℕ∞) * wordMult x.2.rep.ρ w) = (s.count w : ℕ∞)) ∧
        (s.map (ShuffleAlgebra.word ℚ)).sum = y := by
  obtain ⟨n, V, _, _, π, h, hs, rfl, s, h1, h2⟩ := h
  rw [Ψ.symm_apply_apply]
  refine ⟨Finsupp.mapDomain_nonneg fun c => ?_, s, fun w => ?_, h2⟩
  · rw [cls_apply]; exact Int.natCast_nonneg _
  · rw [clsGL, Finsupp.sum_mapDomain_index_inj sigma_mk_injective, ← h1, T.jacquetWordMultiplicity_additive_jordanHolder k n V π h hs w]

end GlobalTheory.SmGL.Exponents

namespace GlobalTheory.SmGL.Exponents

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

@[reducible] def modArgOrder : LinearOrder ℂˣ :=
  LinearOrder.lift' (fun z => toLex (-‖(z : ℂ)‖, (z : ℂ).arg)) fun z z' h => by
    have h' := Prod.ext_iff.1 (toLex.injective h)
    exact Units.ext (Complex.ext_norm_arg (neg_injective h'.1) h'.2)

theorem isLyndon_segWord {q : ℂˣ} (hq : ‖(q : ℂ)‖ < 1) (z : ℂˣ) {l : ℕ} (hl : 0 < l) :
    @IsLyndon _ modArgOrder (segWord q z l) := by
  letI := modArgOrder
  refine isLyndon_of_pairwise_lt (by simp [segWord, hl.ne']) ?_
  rw [segWord, List.pairwise_map]
  refine List.pairwise_lt_range.imp fun {a b} hab => ?_
  refine Prod.Lex.toLex_lt_toLex.2 (Or.inl (neg_lt_neg ?_))
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow]
  exact mul_lt_mul_of_pos_left (pow_lt_pow_right_of_lt_one₀ (by simp) hq hab) (by simp)

theorem norm_absPow_one_lt {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) :
    ‖(absPow k 1 ϖ : ℂ)‖ < 1 := by
  borelize k
  have h1 : nabs k ϖ ≤ 1 := SplitWeil.Model.nabs_le_one ϖ (hϖ ▸ uniformizer_lt_one.le)
  rw [val_absPow, Complex.cpow_one, Complex.norm_real, Real.norm_of_nonneg (nabs_pos' k ϖ).le]
  refine lt_of_le_of_ne h1 fun h => ?_
  have h2 : absPow k ((1 : ℝ) : ℂ) = 1 := by
    rw [eq_unrChar (isUnram_absPow k _) hϖ, show absPow k ((1 : ℝ) : ℂ) ϖ = 1 from by
      ext; simp [val_absPow, h]]
    ext x; simp [unrChar_apply]
  exact one_ne_zero (LocGL.absPow_ofReal_eq_one.1 h2)

theorem exists_eq_torusChar {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {n : ℕ}
    {θ : (Fin n → kˣ) →* ℂˣ} (h : ∀ t ∈ torusO k (Fin n), θ t = 1) :
    ∃ z : Fin n → ℂˣ, θ = torusChar fun i => unrChar k (z i) := by
  refine ⟨fun i => θ (Pi.mulSingle i ϖ), MonoidHom.pi_ext fun i x => ?_⟩
  rw [torusChar_mulSingle]
  have : IsUnram (θ.comp (MonoidHom.mulSingle (fun _ => kˣ) i)) := fun x hx => h _ fun j => by
    rcases eq_or_ne j i with rfl | hj
    · simpa using hx
    · simp [Pi.mulSingle_eq_of_ne hj]
  exact DFunLike.congr_fun (eq_unrChar this hϖ) x

theorem exponentsSeparate (hG : Published.GeometricLemma) (hZ : Published.ZelevinskyPolynomialRing) :
    IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.ExponentsSeparate := by
  intro k _ _ _ _ ϖ hϖ r n V _ _ π hi ha hne hI E hE c hc
  classical
  obtain ⟨Z, Ψ, hZ, hΨ, hX⟩ := hZ k
  let δ := (deltaHalf k fun _ : Fin r => Unit).comp (leviTorus k (Fin r)).toMonoidHom
  have hδ : ∀ t ∈ torusO k (Fin r), δ t = 1 := fun t ht => by
    show deltaHalf k _ (leviTorus k (Fin r) t) = 1
    rw [deltaHalf_apply]
    refine Finset.prod_eq_one fun i _ => isUnram_absPow k _ _ ?_
    rw [show Matrix.GeneralLinearGroup.det (leviTorus k (Fin r) t i) = t i from
      congrFun ((leviTorus k (Fin r)).left_inv t) i]
    exact ht i
  let σ : Fin n → IrrRep (GL (Fin r) k) := fun i => ⟨V i, π i, (ha i).1, hi i⟩
  have hM : ∀ i (z : Fin r → ℂˣ), wordMult (σ i).cl.rep.ρ (List.ofFn z) =
      ((E i).count ((torusChar fun j => unrChar k (z j)) * δ) : ℕ∞) := fun i z => by
    rw [wordMult_congr (σ i).nonempty_equiv_rep.some, wordMult_ofFn,
      T.jordanHolderMultiplicity_normalizedBorelJacquet_unramified k r _ _ (σ i).smooth _ fun t ht => by
        rw [torusChar_apply]
        exact Finset.prod_eq_one fun j _ => isUnram_unrChar k _ _ (ht j)]
    exact hE i _
  let U : Set (Segment k) := {Δ | ∃ (z : ℂˣ) (l : ℕ) (hl : 0 < l),
      Δ = Segment.ofChar (unrChar k z) (isSmoothChar_of_isUnram (isUnram_unrChar k z)) l hl ∧
      ∀ w, wordMult (Z Δ).rep.ρ w =
        (({segWord (absPow k 1 ϖ) z l} : Multiset (List ℂˣ)).count w : ℕ∞)}
  have hU : ∀ Δ, ∃ w : List ℂˣ, Δ ∈ U → ∃ (z : ℂˣ) (l : ℕ) (hl : 0 < l),
      Δ = Segment.ofChar (unrChar k z) (isSmoothChar_of_isUnram (isUnram_unrChar k z)) l hl ∧
      w = segWord (absPow k 1 ϖ) z l ∧
      ∀ v, wordMult (Z Δ).rep.ρ v = (({w} : Multiset (List ℂˣ)).count v : ℕ∞) := fun Δ => by
    by_cases h : Δ ∈ U
    · obtain ⟨z, l, hl, h1, h2⟩ := h
      exact ⟨_, fun _ => ⟨z, l, hl, h1, rfl, h2⟩⟩
    · exact ⟨[], fun h' => absurd h' h⟩
  choose ℓ hℓ using hU
  let φ : Segment k → ShuffleAlgebra ℚ ℂˣ := fun Δ =>
    if Δ ∈ U then ShuffleAlgebra.word ℚ (ℓ Δ) else 0
  have hR : ∀ Δ, Realised Ψ (MvPolynomial.X Δ) (φ Δ) := fun Δ => by
    refine ⟨_, _, _, _, (Z Δ).rep.ρ, (Z Δ).rep.hasFiniteLength, (Z Δ).rep.smooth,
      by rw [clsGL_irr, IrrCl.cl_rep, hX], ?_⟩
    by_cases h : Δ ∈ U
    · obtain ⟨z, l, hl, -, -, h2⟩ := hℓ Δ h
      exact ⟨{ℓ Δ}, h2, by simp [φ, h]⟩
    · exact ⟨0, by simpa using (wordMult_segment hϖ hZ Δ).resolve_left h, by simp [φ, h]⟩
  refine @T.shuffle_count_linearIndependent_classes _ _ ℂˣ _ modArgOrder Ψ (fun x w => wordMult x.2.rep.ρ w) U ℓ φ ?_ ?_
    (fun Δ h => if_neg h) (fun m => (Realised.monomial (hG k).1 (hG k).2 hΨ hR m).effective)
    n (fun i => ⟨r, (σ i).cl⟩) c ?_ ?_ ?_
  · intro Δ h Δ' h' e
    obtain ⟨z, l, hl, h1, h2, -⟩ := hℓ Δ h
    obtain ⟨z', l', hl', h1', h2', -⟩ := hℓ Δ' h'
    obtain ⟨rfl, rfl⟩ := segWord_inj hl (h2.symm.trans (e.trans h2'))
    exact h1.trans h1'.symm
  · intro Δ h
    obtain ⟨z, l, hl, -, h2, -⟩ := hℓ Δ h
    exact ⟨h2 ▸ isLyndon_segWord (norm_absPow_one_lt hϖ) z hl, if_pos h⟩
  · intro i j h
    by_contra hij
    exact (hne i j hij).false (IrrRep.cl_eq_iff.1
      (sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) k)) h)).some
  · intro i
    obtain ⟨χ, hχ⟩ := T.exists_exponent_of_iwahori_fixed_vector k r _ (π i) (ha i) (hI i)
    rw [hE i] at hχ
    have hm : χ ∈ E i := Multiset.count_ne_zero.1 (Nat.cast_ne_zero.1 hχ)
    obtain ⟨z, hz⟩ := exists_eq_torusChar hϖ (θ := χ * δ⁻¹) fun t ht => by
      simp [(hE i).unramified hm ht, hδ t ht]
    refine ⟨List.ofFn z, ?_⟩
    beta_reduce
    rwa [hM, ← hz, inv_mul_cancel_right]
  · intro w
    by_cases hw : w.length = r
    · obtain ⟨z, rfl⟩ : ∃ z : Fin r → ℂˣ, w = List.ofFn z :=
        ⟨fun i => w.get (i.cast hw.symm), List.ext_getElem (by simp [hw]) fun i h1 h2 => by simp⟩
      simp only [hM, ENat.toNat_coe]
      exact T.unramified_char_sums_strict_cone_vanish_each k ϖ hϖ r n E c (fun i χ hχ t ht => (hE i).unramified hχ ht) hc _
    · simp [wordMult_of_ne _ hw]

end GlobalTheory.SmGL.Exponents

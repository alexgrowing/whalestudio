import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem relDim_bot {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {F : Type*} [Field F] :
    relDim (⊥ : Ideal (MRing ι F)) =
      (((Fintype.card (Σ k, ι k) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) := by
  unfold relDim
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card]
  rfl

abbrev ProjIdx (N : ℕ) : Unit → Type := fun _ => Fin (N + 1)

theorem relDim_projectiveSpace {F : Type*} [Field F] (N : ℕ) :
    relDim (⊥ : Ideal (MRing (ProjIdx N) F)) = (N : WithBot (WithTop ℤ)) := by
  rw [relDim_bot]
  simp [Fintype.card_sigma]
  rfl

def binomFn (N : ℕ) (t : ℤ) : ℤ := if 0 ≤ t then ((t.toNat + N).choose N : ℤ) else 0

theorem binomFn_sub (N : ℕ) (t : ℤ) :
    binomFn (N + 1) t - binomFn (N + 1) (t - 1) = binomFn N t := by
  unfold binomFn
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp
  · simp
  · obtain ⟨u, rfl⟩ : ∃ u : ℕ, t = u + 1 := ⟨(t - 1).toNat, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    have h1 : ((u : ℤ) + 1).toNat = u + 1 := by omega
    have h2 : ((u : ℤ) + 1 - 1).toNat = u := by omega
    have h3 := Nat.choose_succ_succ (u + N + 1) N
    rw [h1, h2, show u + 1 + (N + 1) = u + N + 1 + 1 by omega, h3,
      show u + (N + 1) = u + N + 1 by omega, show u + 1 + N = u + N + 1 by omega]
    push_cast
    ring

theorem weight_projIdx (N : ℕ) (d : (Σ _ : Unit, ProjIdx N ()) →₀ ℕ) :
    Finsupp.weight (blockWeight (ProjIdx N)) d () = ∑ x, d x := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply]
  simp [blockWeight]

theorem finrank_gradedPiece_projectiveSpace (F : Type*) [Field F] (N a : ℕ) :
    Module.finrank F (gradedPiece (⊥ : Ideal (MRing (ProjIdx N) F)) (fun _ => a)) =
      (a + N).choose N := by
  have hinj : Function.Injective
      (Ideal.Quotient.mkₐ F (⊥ : Ideal (MRing (ProjIdx N) F))).toLinearMap := by
    intro x y h
    simpa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, sub_eq_zero] using h
  unfold gradedPiece
  rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _),
    weightedHomogeneousSubmodule_eq_finsupp_supported]
  let s : Set ((Σ _ : Unit, ProjIdx N ()) →₀ ℕ) :=
    {d | Finsupp.weight (blockWeight (ProjIdx N)) d = fun _ => a}
  let e : s ≃ (Finset.univ.finsuppAntidiag a : Finset ((Σ _ : Unit, ProjIdx N ()) →₀ ℕ)) :=
    Equiv.subtypeEquivRight fun d => by
      rw [Finset.mem_finsuppAntidiag]
      simp only [s, Set.mem_ofPred_eq, Finset.subset_univ, and_true]
      constructor
      · intro h
        rw [← weight_projIdx]
        exact congrFun h ()
      · intro h
        funext u
        rw [weight_projIdx]
        exact h
  have : Fintype s := Fintype.ofEquiv _ e.symm
  rw [LinearEquiv.finrank_eq (AddMonoidAlgebra.supportedEquivFinsupp (R := F) (S := F) s), Module.finrank_finsupp_self,
    Fintype.card_congr e, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose]
  simp [Fintype.card_sigma]
  rw [add_comm, Nat.choose_symm_add]

theorem hilbFn_projectiveSpace (F : Type*) [Field F] (N : ℕ) (m : Unit → ℤ) :
    hilbFn (⊥ : Ideal (MRing (ProjIdx N) F)) m = binomFn N (m ()) := by
  unfold hilbFn binomFn
  by_cases hm : 0 ≤ m ()
  · rw [if_pos (fun k => hm), if_pos hm]
    have : (fun k => (m k).toNat) = fun _ : Unit => (m ()).toNat := rfl
    rw [this, finrank_gradedPiece_projectiveSpace]
  · rw [if_neg (fun h => hm (h ())), if_neg hm]

theorem foldr_diffStep_binomFn (j N : ℕ) :
    (List.replicate j (1 : Unit → ℤ)).foldr diffStep (fun m => binomFn (N + j) (m ())) =
      fun m => binomFn N (m ()) := by
  induction j generalizing N with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, List.foldr_cons, show N + (j + 1) = (N + 1) + j by omega, ih]
    funext m
    simp only [diffStep, Pi.sub_apply, Pi.one_apply]
    exact binomFn_sub N (m ())

theorem intNum_projectiveSpace (F : Type*) [Field F] (N : ℕ) :
    intNum F (⊥ : Ideal (MRing (ProjIdx N) F)) (fun _ : Fin N => (1 : Unit → ℤ)) = 1 := by
  have hh : hilbFn (⊥ : Ideal (MRing (ProjIdx N) F)) = fun m => binomFn (0 + N) (m ()) := by
    funext m
    rw [zero_add, hilbFn_projectiveSpace]
  unfold intNum mixedDiff
  rw [List.ofFn_const, hh, foldr_diffStep_binomFn]
  have hev : ∀ᶠ m : Unit → ℤ in Filter.atTop, binomFn 0 (m ()) = 1 :=
    (Filter.eventually_ge_atTop 0).mono fun m hm => by
      have : (0 : ℤ) ≤ m () := hm ()
      simp [binomFn, this]
  have hex : ∃ c, ∀ᶠ m : Unit → ℤ in Filter.atTop, binomFn 0 (m ()) = c := ⟨1, hev⟩
  unfold eventualValue
  rw [dif_pos hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and hev).exists
  exact h1.symm.trans h2

theorem blockIncl_injective {K K' : Type*} (j : K ↪ K') (ι' : K' → Type*) :
    Function.Injective (blockIncl j ι') := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  simp only [blockIncl, Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  cases j.injective h1
  rw [eq_of_heq h2]

theorem contractPrime_bot {K K' : Type*} {F : Type*} [Field F] (j : K ↪ K') (ι' : K' → Type*) :
    contractPrime j (⊥ : Ideal (MRing ι' F)) = ⊥ :=
  Ideal.comap_bot_of_injective _ (rename_injective _ (blockIncl_injective j ι'))

theorem addBlockPrime_bot {K : Type*} {F : Type*} [Field F] (ι : K → Type) (N : ℕ) :
    addBlockPrime N (⊥ : Ideal (MRing ι F)) = ⊥ :=
  Ideal.map_bot

theorem isMultiHomogIdeal_bot_projectiveSpace (N : ℕ) :
    IsMultiHomogIdeal (⊥ : Ideal (MRing (ProjIdx N) ℚ)) :=
  isMultiProjPrime_bot.multiHomog

theorem coordinate_isMultiHomog (N : ℕ) (i : Fin (N + 1)) :
    IsMultiHomog (X ⟨(), i⟩ : MRing (ProjIdx N) ℚ) (blockWeight (ProjIdx N) ⟨(), 0⟩) :=
  isWeightedHomogeneous_X _ _ _

theorem coordinate_not_mem_bot (N : ℕ) (i : Fin (N + 1)) :
    (X ⟨(), i⟩ : MRing (ProjIdx N) ℚ) ∉ (⊥ : Ideal (MRing (ProjIdx N) ℚ)) := by
  rw [Ideal.mem_bot]
  exact X_ne_zero _

theorem HilbExactDivide.hypotheses_example :
    IsMultiHomogIdeal (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      IsMultiHomog (X ⟨(), 0⟩ : MRing (ProjIdx 1) ℚ) (blockWeight (ProjIdx 1) ⟨(), 0⟩) :=
  ⟨isMultiHomogIdeal_bot_projectiveSpace 1, coordinate_isMultiHomog 1 0⟩

theorem PolyOfDiffs.hypotheses_example :
    ∀ k : Unit, ∃ q : MvPolynomial Unit ℚ, (q = 0 ∨ q.totalDegree < 1) ∧
      EventuallyPoly (diffStep (Pi.single k 1) (fun m : Unit → ℤ => m ())) q := by
  rintro ⟨⟩
  refine ⟨1, Or.inr (by simp), Filter.Eventually.of_forall fun m => ?_⟩
  simp [diffStep]

theorem eventuallyPoly_projectiveLine :
    EventuallyPoly (hilbFn (⊥ : Ideal (MRing (ProjIdx 1) ℚ))) (X () + 1) :=
  (Filter.eventually_ge_atTop 0).mono fun m hm => by
    have ht : (0 : ℤ) ≤ m () := hm ()
    rw [hilbFn_projectiveSpace, binomFn, if_pos ht, Nat.choose_one_right]
    have e : (((m ()).toNat : ℕ) : ℤ) = m () := Int.toNat_of_nonneg ht
    have e' : (((m ()).toNat : ℕ) : ℚ) = (m () : ℚ) := by exact_mod_cast e
    simp only [map_add, eval_X, map_one]
    push_cast
    rw [e']

theorem HilbDegreeBound.hypotheses_example :
    IsMultiHomogIdeal (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      IsRelevant (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      EventuallyPoly (hilbFn (⊥ : Ideal (MRing (ProjIdx 1) ℚ))) (X () + 1) ∧
      (X () + 1 : MvPolynomial Unit ℚ) ≠ 0 := by
  refine ⟨isMultiHomogIdeal_bot_projectiveSpace 1, isMultiProjPrime_bot.relevant,
    eventuallyPoly_projectiveLine, fun h => ?_⟩
  simpa using congrArg (MvPolynomial.eval fun _ => (0 : ℚ)) h

theorem MixedDiffConst.hypotheses_example :
    IsMultiHomogIdeal (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      IsRelevant (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) = (1 : ℕ) :=
  ⟨isMultiHomogIdeal_bot_projectiveSpace 1, isMultiProjPrime_bot.relevant,
    relDim_projectiveSpace 1⟩

theorem IntNumZeroSlot.hypotheses_example :
    IsMultiHomogIdeal (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) < (2 : ℕ) := by
  refine ⟨isMultiHomogIdeal_bot_projectiveSpace 1, ?_⟩
  rw [relDim_projectiveSpace]
  show (((1 : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) < (((2 : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by norm_num))

theorem IntNumBase.hypotheses_example :
    IsMultiProjPrime (⊥ : Ideal (MRing (ProjIdx 0) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 0) ℚ)) = 0 := by
  refine ⟨isMultiProjPrime_bot, ?_⟩
  rw [relDim_projectiveSpace]
  rfl

theorem CutRegular.hypotheses_example :
    IsMultiProjPrime (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) = ((0 + 1 : ℕ)) ∧
      IsMultiHomog (X ⟨(), 0⟩ : MRing (ProjIdx 1) ℚ) (blockWeight (ProjIdx 1) ⟨(), 0⟩) ∧
      (X ⟨(), 0⟩ : MRing (ProjIdx 1) ℚ) ∉ (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) :=
  ⟨isMultiProjPrime_bot, relDim_projectiveSpace 1, coordinate_isMultiHomog 1 0,
    coordinate_not_mem_bot 1 0⟩

theorem CutRational.hypotheses_example :
    IsMultiProjPrime (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) = 1 ∧
      IsMultiHomog (X ⟨(), 0⟩ : MRing (ProjIdx 1) ℚ) (blockWeight (ProjIdx 1) ⟨(), 0⟩) ∧
      IsMultiHomog (X ⟨(), 1⟩ : MRing (ProjIdx 1) ℚ) (blockWeight (ProjIdx 1) ⟨(), 0⟩) ∧
      (X ⟨(), 0⟩ : MRing (ProjIdx 1) ℚ) ∉ (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      (X ⟨(), 1⟩ : MRing (ProjIdx 1) ℚ) ∉ (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) := by
  refine ⟨isMultiProjPrime_bot, ?_, coordinate_isMultiHomog 1 0, coordinate_isMultiHomog 1 1,
    coordinate_not_mem_bot 1 0, coordinate_not_mem_bot 1 1⟩
  rw [relDim_projectiveSpace]
  rfl

theorem IntNumBaseChange.hypotheses_example :
    IsMultiProjPrime (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      (algebraMap ℚ (RatFunc ℚ)) 1 = 1 :=
  ⟨isMultiProjPrime_bot, map_one _⟩

theorem ProjectionFormulaContracted.hypotheses_example :
    IsMultiProjPrime (⊥ : Ideal (MRing (addBlock (ProjIdx 0) 1) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (addBlock (ProjIdx 0) 1) ℚ)) = (1 : ℕ) ∧
      relDim (contractPrime Function.Embedding.some
        (⊥ : Ideal (MRing (addBlock (ProjIdx 0) 1) ℚ))) < (1 : ℕ) := by
  refine ⟨isMultiProjPrime_bot, ?_, ?_⟩
  · rw [relDim_bot]
    rfl
  · rw [contractPrime_bot, relDim_bot]
    show (((0 : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) < (((1 : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by norm_num))

theorem ProjectionFormulaDegree.hypotheses_example :
    IsMultiProjPrime (⊥ : Ideal (MRing (addBlock (ProjIdx 1) 0) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (addBlock (ProjIdx 1) 0) ℚ)) = (1 : ℕ) ∧
      relDim (contractPrime Function.Embedding.some
        (⊥ : Ideal (MRing (addBlock (ProjIdx 1) 0) ℚ))) = (1 : ℕ) := by
  refine ⟨isMultiProjPrime_bot, ?_, ?_⟩
  · rw [relDim_bot]
    rfl
  · rw [contractPrime_bot, relDim_bot]
    rfl

theorem ProductWithProjectiveSpace.hypotheses_example :
    IsMultiProjPrime (⊥ : Ideal (MRing (ProjIdx 0) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 0) ℚ)) = (0 : ℕ) ∧ 0 + 1 = 0 + 1 :=
  ⟨isMultiProjPrime_bot, relDim_projectiveSpace 0, rfl⟩

theorem eq_monomial_of_isMultiHomog_point {F : Type*} [Field F] (f : MRing (ProjIdx 0) F)
    (b : Unit → ℕ) (hf : IsMultiHomog f b) :
    f = monomial (Finsupp.single ⟨(), 0⟩ (b ())) (coeff (Finsupp.single ⟨(), 0⟩ (b ())) f) := by
  ext d
  rw [coeff_monomial]
  split_ifs with h
  · rw [h]
  · by_contra hne
    have hw := hf hne
    have hd : d = Finsupp.single ⟨(), 0⟩ (b ()) := by
      ext i
      obtain ⟨⟨⟩, i⟩ := i
      have hi : i = 0 := Fin.fin_one_eq_zero i
      subst hi
      rw [Finsupp.single_eq_same, ← congrFun hw (), weight_projIdx,
        Fintype.sum_eq_single ⟨(), 0⟩]
      rintro ⟨⟨⟩, j⟩ hj
      exact absurd (by rw [Fin.fin_one_eq_zero j]) hj
    exact h hd.symm

theorem resDeg_point (F : Type*) [Field F] : resDeg (⊥ : Ideal (MRing (ProjIdx 0) F)) = 1 := by
  unfold resDeg
  rw [dif_pos Ideal.isPrime_bot]
  have hle : homFracDegZero (⊥ : Ideal (MRing (ProjIdx 0) F)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    unfold homFracDegZero
    rw [IntermediateField.adjoin_le_iff]
    rintro x ⟨b, f, g, hf, hg, hgP, rfl⟩
    rw [SetLike.mem_coe, IntermediateField.mem_bot]
    have ef := eq_monomial_of_isMultiHomog_point f b hf
    have eg := eq_monomial_of_isMultiHomog_point g b hg
    rw [← C_mul_X_pow_eq_monomial] at ef eg
    generalize coeff (Finsupp.single ⟨(), 0⟩ (b ())) f = a at ef
    generalize coeff (Finsupp.single ⟨(), 0⟩ (b ())) g = c at eg
    generalize b () = n at ef eg
    set v : (Σ _ : Unit, ProjIdx 0 ()) := ⟨(), 0⟩
    have hc : c ≠ 0 := by
      rintro rfl
      apply hgP
      rw [eg, C_0, zero_mul]
      exact Ideal.zero_mem _
    have hY : algebraMap (MRing (ProjIdx 0) F ⧸ (⊥ : Ideal (MRing (ProjIdx 0) F)))
        (FractionRing (MRing (ProjIdx 0) F ⧸ (⊥ : Ideal (MRing (ProjIdx 0) F))))
        (Ideal.Quotient.mk _ (X v ^ n)) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_bot]
      exact pow_ne_zero _ (X_ne_zero _)
    refine ⟨a / c, ?_⟩
    rw [ef, eg, map_mul, map_mul, map_mul, map_mul, ← MvPolynomial.algebraMap_eq,
      Ideal.Quotient.mk_algebraMap, Ideal.Quotient.mk_algebraMap,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      mul_div_mul_right _ _ hY, map_div₀]
  rw [hle, IntermediateField.finrank_bot]

end

end GroundTheory.Heights₂.Heights.FieldNumbers

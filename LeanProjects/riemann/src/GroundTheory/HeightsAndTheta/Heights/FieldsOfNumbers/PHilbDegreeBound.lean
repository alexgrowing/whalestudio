import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegreeBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

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

omit [Fintype K] [DecidableEq K] in

theorem colon_span_eq_of_isPrime {P : Ideal (MRing ι F)} (hP : P.IsPrime) {s : MRing ι F}
    (hs : s ∉ P) : P.colon (Ideal.span {s}) = P := by
  ext x
  rw [Ideal.mem_colon_span_singleton]
  exact ⟨fun h => (hP.mem_or_mem h).resolve_right hs, fun h => P.mul_mem_right s h⟩

omit [Fintype K] [DecidableEq K] in

theorem ringKrullDim_sup_span_add_one_le {P : Ideal (MRing ι F)} [P.IsPrime] {s : MRing ι F}
    (hs : s ∉ P) :
    ringKrullDim (MRing ι F ⧸ (P ⊔ Ideal.span {s})) + 1 ≤ ringKrullDim (MRing ι F ⧸ P) := by
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor le_sup_left)
    (Ideal.Quotient.factor_surjective le_sup_left) (r := Ideal.Quotient.mk P s) ?_ ?_
  · exact mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)

theorem lt_of_add_one_le_natCast {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ n) : x < n := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have e : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [e, ← WithBot.coe_natCast, WithBot.coe_le_coe] at h
      exact absurd h (not_le.mpr (ENat.natCast_lt_top n))
    | coe a =>
      have : a + 1 ≤ n := by exact_mod_cast h
      exact_mod_cast (show a < n by omega)

end Lemmas

theorem totalDegree_add_card_le_ringKrullDim (h1 : HilbEventuallyPoly.Statement.{u})
    (h2 : HilbExactDivide.Statement.{u}) (h3 : PolyOfDiffs.Statement)
    (h4 : PrimeFiltration.Statement.{u}) (hU : EventuallyPolyUnique.Statement)
    (hS : EventuallyPolyShift.Statement) (hZ : HilbIrrelevantZero.Statement.{u})
    (hD : RelevantPrimeDimGe.Statement.{u})
    (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) :
    ∀ I : Ideal (MRing ι F), IsMultiHomogIdeal I → ringKrullDim (MRing ι F ⧸ I) < n →
      ∀ p : MvPolynomial K ℚ, EventuallyPoly (hilbFn I) p → p ≠ 0 →
      ((p.totalDegree + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ I) := by
  induction n with
  | zero =>
    intro I _ hlt p hp hp0
    exfalso
    have hsub : Subsingleton (MRing ι F ⧸ I) := by
      by_contra hn
      rw [not_subsingleton_iff_nontrivial] at hn
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MRing ι F ⧸ I)
      exact absurd hlt (not_lt.mpr (by simpa using h0))
    have hz : ∀ m, hilbFn I m = 0 := by
      intro m
      unfold hilbFn
      split_ifs
      · rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero]
      · rfl
    have : EventuallyPoly (hilbFn I) 0 := Filter.Eventually.of_forall fun m => by simp [hz]
    exact hp0 (hU K _ p 0 hp this)
  | succ n ih =>
    have prime : ∀ P : Ideal (MRing ι F), P.IsPrime → IsMultiHomogIdeal P →
        ringKrullDim (MRing ι F ⧸ P) < (n + 1 : ℕ) → ∀ p : MvPolynomial K ℚ,
        EventuallyPoly (hilbFn P) p → p ≠ 0 →
        ((p.totalDegree + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ P) := by
      intro P hPp hPh hlt p hp hp0
      by_cases hrel : IsRelevant P
      swap
      · exfalso
        have : EventuallyPoly (hilbFn P) 0 := (hZ F K ι P hrel).mono fun m hm => by simp [hm]
        exact hp0 (hU K _ p 0 hp this)
      have hge := hD F K ι P ⟨hPp, hPh, hrel⟩
      choose i hi using hrel
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ringKrullDim (MRing ι F ⧸ P) = N := by
        generalize ringKrullDim (MRing ι F ⧸ P) = x at hge hlt
        induction x using WithBot.recBotCoe with
        | bot => exact absurd hge (not_le.mpr (WithBot.bot_lt_coe _))
        | coe a =>
          induction a using ENat.recTopCoe with
          | top => exact absurd hlt (by simp)
          | coe a => exact ⟨a, rfl⟩
      have hKN : Fintype.card K ≤ N := by rw [hN] at hge; exact_mod_cast hge
      have hdiff : ∀ k, ∃ q : MvPolynomial K ℚ, (q = 0 ∨ q.totalDegree < N - Fintype.card K) ∧
          EventuallyPoly (diffStep (Pi.single k 1) (hilbFn P)) q := by
        intro k
        have hs : IsMultiHomog (X ⟨k, i k⟩ : MRing ι F) (Pi.single k 1) :=
          isWeightedHomogeneous_X _ _ _
        have hJ := isMultiHomogIdeal_sup_span hPh hs
        obtain ⟨q, hq⟩ := h1 F K ι _ hJ
        refine ⟨q, ?_, ?_⟩
        · by_cases hq0 : q = 0
          · exact Or.inl hq0
          right
          have hdrop := ringKrullDim_sup_span_add_one_le (P := P) (hi k)
          rw [hN] at hdrop
          have hNn : N ≤ n := by
            rw [hN] at hlt
            have : N < n + 1 := by exact_mod_cast hlt
            omega
          have hltJ := lt_of_add_one_le_natCast (hdrop.trans (by exact_mod_cast hNn))
          have hb := ih _ hJ hltJ q hq hq0
          have h' : ((q.totalDegree + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ N := by
            refine le_trans ?_ hdrop
            gcongr
          have h'' : q.totalDegree + Fintype.card K + 1 ≤ N := by exact_mod_cast h'
          omega
        · refine hq.mono fun m hm => ?_
          have e := h2 F K ι P hPh (Pi.single k 1) _ hs m
          rw [colon_span_eq_of_isPrime hPp (hi k)] at e
          have ec : (fun k' => ((Pi.single k 1 : K → ℕ) k' : ℤ)) = (Pi.single k 1 : K → ℤ) := by
            funext k'
            by_cases h : k' = k <;> simp [h]
          rw [ec] at e
          simp only [diffStep]
          rw [e]
          exact hm
      obtain ⟨p', hp'deg, hp'⟩ := h3 K (hilbFn P) (N - Fintype.card K) hdiff
      have hpp' := hU K _ p p' hp hp'
      subst hpp'
      rw [hN]
      exact_mod_cast (show p.totalDegree + Fintype.card K ≤ N by omega)
    intro I hI hlt p hp hp0
    obtain ⟨r, Q, c, hQ, hsum, -, -⟩ := h4 F K ι I hI
    choose pj hpj using fun j => h1 F K ι (Q j) (hQ j).2.1
    choose q hq hqdeg hq0 using fun j => hS K _ (pj j) (fun k => (c j k : ℤ)) (hpj j)
    have hsumP : EventuallyPoly (hilbFn I) (∑ j, q j) := by
      have hall : ∀ᶠ m in Filter.atTop, ∀ j, (hilbFn (Q j) (m - fun k => (c j k : ℤ)) : ℚ) =
          eval (fun k => (m k : ℚ)) (q j) := Filter.eventually_all.mpr hq
      filter_upwards [hall, hsum] with m hm hm'
      rw [hm', map_sum]
      push_cast
      exact Finset.sum_congr rfl fun j _ => hm j
    have hpq := hU K _ p _ hp hsumP
    have hDQ : ∀ j, q j ≠ 0 → (((q j).totalDegree + Fintype.card K : ℕ) : WithBot ℕ∞) ≤
        ringKrullDim (MRing ι F ⧸ I) := by
      intro j hj
      have hpj0 : pj j ≠ 0 := fun h => hj (hq0 j h)
      have hle : ringKrullDim (MRing ι F ⧸ Q j) ≤ ringKrullDim (MRing ι F ⧸ I) :=
        ringKrullDim_le_of_surjective (Ideal.Quotient.factor (hQ j).2.2)
          (Ideal.Quotient.factor_surjective _)
      have hb := prime (Q j) (hQ j).1 (hQ j).2.1 (hle.trans_lt hlt) (pj j) (hpj j) hpj0
      refine le_trans ?_ (hb.trans hle)
      have := hqdeg j
      exact_mod_cast (show (q j).totalDegree + Fintype.card K ≤
        (pj j).totalDegree + Fintype.card K by omega)
    classical
    set T := Finset.univ.filter fun j => q j ≠ 0 with hT
    have hpT : p = ∑ j ∈ T, q j := by rw [hpq, hT, Finset.sum_filter_ne_zero]
    have hTne : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0, Finset.sum_empty] at hpT
      exact hp0 hpT
    obtain ⟨j, hjT, hjmax⟩ := Finset.exists_max_image T (fun j => (q j).totalDegree) hTne
    have hdeg : p.totalDegree ≤ (q j).totalDegree := by
      rw [hpT]
      exact totalDegree_finsetSum_le hjmax
    refine le_trans ?_ (hDQ j (Finset.mem_filter.mp hjT).2)
    exact_mod_cast (show p.totalDegree + Fintype.card K ≤ (q j).totalDegree + Fintype.card K by
      omega)

theorem HilbDegreeBound.proof (h1 : HilbEventuallyPoly.Statement.{u})
    (h2 : HilbExactDivide.Statement.{u}) (h3 : PolyOfDiffs.Statement)
    (h4 : PrimeFiltration.Statement.{u}) (hU : EventuallyPolyUnique.Statement)
    (hS : EventuallyPolyShift.Statement) (hZ : HilbIrrelevantZero.Statement.{u})
    (hD : RelevantPrimeDimGe.Statement.{u}) : HilbDegreeBound.Statement.{u} := by
  intro F _ K _ _ ι _ I hI
  refine ⟨fun _ p hp hp0 => ?_, fun hrel => hZ F K ι I hrel⟩
  have key := fun n => totalDegree_add_card_le_ringKrullDim h1 h2 h3 h4 hU hS hZ hD F K ι n I hI
  unfold relDim
  generalize hx : ringKrullDim (MRing ι F ⧸ I) = x at key
  induction x using WithBot.recBotCoe with
  | bot =>
    have := key 0 (WithBot.bot_lt_coe _) p hp hp0
    exact absurd this (not_le.mpr (WithBot.bot_lt_coe _))
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.mpr le_top
    | coe N =>
      have := key (N + 1) (by exact_mod_cast Nat.lt_succ_self N) p hp hp0
      have hle : p.totalDegree + Fintype.card K ≤ N := by exact_mod_cast this
      show ((p.totalDegree : ℕ) : WithBot (WithTop ℤ)) ≤
        (((N : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)
      have : (p.totalDegree : ℤ) ≤ (N : ℤ) - Fintype.card K := by omega
      exact_mod_cast this

end

end GroundTheory.Heights₂.Heights.FieldNumbers

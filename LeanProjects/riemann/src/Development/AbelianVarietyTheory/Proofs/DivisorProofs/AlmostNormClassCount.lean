import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaProdEqOfEverywhereNormDiv
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.QuadSymbol.SignCount

theorem card_prod_eq_mul_two {ι : Type} [Fintype ι] [Nonempty ι] (c : ℤˣ) :
    Nat.card {s : ι → ℤˣ // c * ∏ i, s i = 1} * 2 = 2 ^ Fintype.card ι := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let m : ι → ℤˣ := Pi.mulSingle i₀ (-1)
  have hm : ∏ i, m i = -1 := by simp [m, Finset.prod_pi_mulSingle']
  have hmm : m * m = 1 := by
    ext i
    by_cases h : i = i₀
    · subst h; simp [m]
    · simp [m, Pi.mulSingle_eq_of_ne h]
  have key : ∀ s : ι → ℤˣ, (c * ∏ i, (s * m) i = 1) ↔ ¬ (c * ∏ i, s i = 1) := by
    intro s
    simp only [Pi.mul_apply, Finset.prod_mul_distrib, hm]
    rcases Int.units_eq_one_or (c * ∏ i, s i) with h | h
    · rw [← mul_assoc, h]; decide
    · rw [← mul_assoc, h]; decide
  let e : {s : ι → ℤˣ // c * ∏ i, s i = 1} ≃ {s : ι → ℤˣ // ¬ (c * ∏ i, s i = 1)} :=
    { toFun := fun s => ⟨s.1 * m, fun h => (key s.1).1 h s.2⟩
      invFun := fun s => ⟨s.1 * m, by
        have := (key s.1).2 s.2
        exact this⟩
      left_inv := fun s => Subtype.ext (by simp [mul_assoc, hmm])
      right_inv := fun s => Subtype.ext (by simp [mul_assoc, hmm]) }
  have htot := Fintype.card_subtype_compl (fun s : ι → ℤˣ => c * ∏ i, s i = 1)
  rw [Nat.card_eq_fintype_card, mul_two]
  nth_rewrite 2 [Fintype.card_congr e]
  have hle := Fintype.card_subtype_le (fun s : ι → ℤˣ => c * ∏ i, s i = 1)
  rw [htot, Fintype.card_pi, Finset.prod_const, Fintype.card_units_int, Finset.card_univ] at *
  omega

end GlobalTheory.QuadSymbol.SignCount

namespace GlobalTheory.QuadSymbol.SignCount

theorem neg_one_not_mem_normGroup {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (hL : NumberField.IsTotallyComplex L)
    {w : InfinitePlace K} (hw : w.IsReal) : (-1 : (w.Completion)ˣ) ∉ normGroup K L w.Completion := by
  obtain ⟨δ, b, -, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hneg : InfinitePlace.embedding_of_isReal hw δ < 0 := by
    by_contra hc
    obtain ⟨r, hr⟩ := Real.isSquare_iff.2 (not_lt.1 hc)
    let τ : L →+* ℂ := ComplexEmbedding.lift L w.embedding
    have hτ : ∀ x : K, τ (algebraMap K L x) = InfinitePlace.embedding_of_isReal hw x := fun x => by
      rw [InfinitePlace.embedding_of_isReal_apply]
      exact ComplexEmbedding.lift_algebraMap_apply L w.embedding x
    have h2 : τ (b 1) * τ (b 1) = (r : ℂ) * r := by rw [← map_mul, h1, hτ, hr]; push_cast; rfl
    have h3 : starRingEnd ℂ (τ (b 1)) = τ (b 1) := by
      rcases mul_self_eq_mul_self_iff.1 h2 with h | h <;> rw [h] <;> simp
    refine InfinitePlace.not_isReal_iff_isComplex.2 (hL.isComplex (InfinitePlace.mk τ))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
    change starRingEnd ℂ (τ x) = τ x
    rw [← b.sum_repr x, Fin.sum_univ_two, h0, Algebra.smul_def, Algebra.smul_def]
    simp only [map_add, map_mul, map_one, hτ, h3, Complex.conj_ofReal]
  rw [mem_normGroup_iff_form b h0 h1]
  rintro ⟨x, y, hxy⟩
  let f := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hf : f (algebraMap K w.Completion δ) = InfinitePlace.embedding_of_isReal hw δ :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv _).symm δ)
  have := congrArg f hxy
  simp only [Units.val_neg, Units.val_one, map_neg, map_one, map_sub, map_mul, map_pow, hf] at this
  nlinarith [sq_nonneg (f x), sq_nonneg (f y)]

end GlobalTheory.QuadSymbol.SignCount

namespace GlobalTheory.QuadSymbol.SignCount

def infSigns (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L] (t : Kˣ) :
    InfinitePlace K → ℤˣ :=
  fun w => eta K L w.Completion (infDiag K t w)

theorem infSigns_eq_of_mem {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {t t' : Kˣ} (h : t⁻¹ * t' ∈ globalNorms K L) :
    infSigns K L t' = infSigns K L t := by
  funext w
  refine eta_eq_of_div_mem ?_
  have := toUnits_mem_normGroup (K := K) (L := L) w.Completion h
  rw [← div_eq_inv_mul, _root_.map_div] at this
  exact this

theorem infSigns_out {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (t : Kˣ) :
    infSigns K L (Quotient.out (QuotientGroup.mk t : Kˣ ⧸ globalNorms K L)) = infSigns K L t :=
  infSigns_eq_of_mem (QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm)

theorem card_classes_mul_two : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [Algebra.IsQuadraticExtension K L], NumberField.IsTotallyReal K → NumberField.IsTotallyComplex L → ∀ x : GlobalTheory.QuadSymbol.FinFam K, GlobalTheory.QuadSymbol.AlmostNorm K L x → Nat.card {q : Kˣ ⧸ GlobalTheory.QuadSymbol.globalNorms K L // ∃ t : Kˣ, q = QuotientGroup.mk t ∧ ∀ u, x u / GlobalTheory.QuadSymbol.finDiag K t u ∈ GlobalTheory.QuadSymbol.normGroup K L (u.adicCompletion K)} * 2 = 2 ^ Fintype.card (InfinitePlace K) := by
  intro K L _ _ _ _ _ _ hK hL x hx
  have hfd : FiniteDimensional K L := Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two K L)
  obtain ⟨-, hnorm, hseq, -⟩ := exactSequence K L
  obtain ⟨-, hc2⟩ := localCharacters K L
  set c : ℤˣ := ∏ᶠ v : HeightOneSpectrum (𝓞 K), eta K L (v.adicCompletion K) (x v) with hc
  rw [← card_prod_eq_mul_two c]
  congr 1
  have hprod : ∀ t : Kˣ, (∀ u, x u / finDiag K t u ∈ normGroup K L (u.adicCompletion K)) →
      c * ∏ w, infSigns K L t w = 1 := by
    intro t ht
    have := (hseq x (infDiag K t) hx).1 ⟨t, fun u => ht u, fun w => by simp [one_mem]⟩
    exact this
  refine Nat.card_congr (Equiv.ofBijective (fun q => ⟨infSigns K L (Quotient.out q.1), ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨t, hq, ht⟩ := q.2
    rw [hq, infSigns_out]
    exact hprod t ht
  · rintro ⟨q₁, t₁, rfl, h₁⟩ ⟨q₂, t₂, rfl, h₂⟩ he
    have he' : infSigns K L t₁ = infSigns K L t₂ := by
      have := congrArg Subtype.val he
      simpa only [infSigns_out] using this
    refine Subtype.ext (QuotientGroup.eq.2 ((hnorm (t₁⁻¹ * t₂)).1 ⟨fun u => ?_, fun w => ?_⟩))
    · have hm := div_mem (h₁ u) (h₂ u)
      rwa [div_div_div_cancel_left, finDiag, finDiag, ← _root_.map_div, div_eq_inv_mul] at hm
    · have hm := Converse.div_mem_normGroup (hc2 w) (congrFun he' w)
      rwa [infDiag, infDiag, ← _root_.map_div, div_eq_inv_mul] at hm
  · rintro ⟨s, hs⟩
    let y : InfFam K := fun w => if s w = 1 then 1 else -1
    have hy : ∀ w, eta K L w.Completion (y w) = s w := by
      intro w
      rcases Int.units_eq_one_or (s w) with h | h
      · simp only [y, h, if_true]
        exact eta_eq_one_iff.2 (one_mem _)
      · simp only [y, h, show (-1 : ℤˣ) ≠ 1 by decide, if_false]
        exact eta_eq_neg_one_iff.2 (neg_one_not_mem_normGroup hL (hK.isReal w))
    have hy1 : etaProd K L x y = 1 := by
      unfold etaProd
      rw [Finset.prod_congr rfl fun w _ => hy w]
      exact hs
    obtain ⟨t, ht1, ht2⟩ := (hseq x y hx).2 hy1
    refine ⟨⟨QuotientGroup.mk t, t, rfl, fun u => ht1 u⟩, Subtype.ext ?_⟩
    simp only [infSigns_out]
    funext w
    rw [← hy w]
    exact (eta_eq_of_div_mem (ht2 w)).symm

end GlobalTheory.QuadSymbol.SignCount

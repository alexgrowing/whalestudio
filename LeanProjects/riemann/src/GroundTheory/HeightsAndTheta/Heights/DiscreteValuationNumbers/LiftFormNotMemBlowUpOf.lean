import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Helpers

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]

theorem isMultiHomog_liftForm {J : Type} {p : MRing ι R} {c : K → ℕ} (h : IsMultiHomog p c) :
    IsMultiHomog (liftForm (J := J) p) (liftMDeg c) := by
  have key : ∀ a : (Σ k, ι k) →₀ ℕ,
      Finsupp.weight (blockWeight (extIdx ι J))
        (a.mapDomain fun v : Σ k, ι k => (⟨some v.1, v.2⟩ : Σ o, extIdx ι J o)) =
      liftMDeg (Finsupp.weight (blockWeight ι) a) := by
    intro a
    induction a using Finsupp.induction_linear with
    | zero => funext o; cases o <;> simp [liftMDeg]
    | add x y hx hy =>
      rw [Finsupp.mapDomain_add, map_add, map_add, hx, hy]
      funext o; cases o <;> simp [liftMDeg]
    | single v n =>
      rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]
      funext o; cases o <;> simp [liftMDeg, blockWeight, Pi.single_apply]
  intro a ha
  obtain ⟨a', rfl, ha'⟩ := coeff_rename_ne_zero _ _ _ ha
  rw [key, h ha']

theorem isMultiHomog_powMonomial (e : K → ℕ) (i : ∀ k, ι k) :
    IsMultiHomog (powMonomial e i : MRing ι R) e := by
  have h := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ e k)
    (fun k => e k • blockWeight ι ⟨k, i k⟩) (fun k _ => (isWeightedHomogeneous_X R _ _).pow (e k))
  unfold IsMultiHomog powMonomial
  convert h using 1
  funext k
  simp [Finset.sum_apply, blockWeight, Pi.single_apply]

theorem liftForm_X {J : Type} (v : Σ k, ι k) :
    liftForm (J := J) (X v : MRing ι R) = X ⟨some v.1, v.2⟩ := by
  simp [liftForm, rename_X]

theorem liftForm_C {J : Type} (r : R) : liftForm (J := J) (C r : MRing ι R) = C r := by
  simp [liftForm]

variable {J : Type}

theorem liftForm_mem_blowUpOf {P : Ideal (MRing ι R)} {u : J → MRing ι R} {p : MRing ι R} (h : p ∈ P) :
    liftForm p ∈ blowUpOf P u := by
  rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Ideal.Quotient.eq_zero_iff_mem.mpr h,
    map_zero]

theorem liftForm_not_mem_blowUpOf {P : Ideal (MRing ι R)} {u : J → MRing ι R} {p : MRing ι R}
    (h : p ∉ P) : liftForm (J := J) p ∉ blowUpOf P u := by
  rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
    Ideal.Quotient.eq_zero_iff_mem]
  exact h

theorem newVar_not_mem_blowUpOf {P : Ideal (MRing ι R)} {u : J → MRing ι R} {j : J} (h : u j ∉ P) :
    (newVar j : MRing (extIdx ι J) R) ∉ blowUpOf P u := by
  rw [blowUpOf, RingHom.mem_ker, newVar, aeval_X]
  change ¬ (Polynomial.C (Ideal.Quotient.mk P (u j)) * Polynomial.X = 0)
  intro h0
  have h1 := congrArg (fun p => Polynomial.coeff p 1) h0
  simp only [Polynomial.coeff_C_mul_X, if_true, Polynomial.coeff_zero] at h1
  exact h (Ideal.Quotient.eq_zero_iff_mem.mp h1)

theorem mem_blowUpOf_of_sub {P : Ideal (MRing ι R)} {u : J → MRing ι R} {j j' : J}
    {a a' : MRing ι R} (h : u j * a - u j' * a' ∈ P) :
    newVar j * liftForm a - newVar j' * liftForm a' ∈ blowUpOf P u := by
  rw [blowUpOf, RingHom.mem_ker]
  simp only [map_sub, map_mul, newVar, aeval_X, blowUpSubst, aeval_blowUpSubst_liftForm]
  have e : Polynomial.C (Ideal.Quotient.mk P (u j)) * Polynomial.X * Polynomial.C (Ideal.Quotient.mk P a) -
      Polynomial.C (Ideal.Quotient.mk P (u j')) * Polynomial.X * Polynomial.C (Ideal.Quotient.mk P a') =
      Polynomial.C (Ideal.Quotient.mk P (u j * a - u j' * a')) * Polynomial.X := by
    simp only [map_sub, map_mul]; ring
  rw [e, Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero, zero_mul]

theorem comap_liftForm_facts {P : Ideal (MRing ι R)} {u : J → MRing ι R}
    {W : Ideal (MRing (extIdx ι J) R)} (hW : W.IsPrime) (hQW : blowUpOf P u ≤ W) (hrel : IsRelevant W) :
    (W.comap (liftForm (J := J))).IsPrime ∧ P ≤ W.comap (liftForm (J := J)) ∧
      IsRelevant (W.comap (liftForm (J := J))) ∧ ∃ j, (newVar j : MRing (extIdx ι J) R) ∉ W := by
  refine ⟨Ideal.comap_isPrime _ _, fun p hp => hQW (liftForm_mem_blowUpOf hp), fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hrel (some k)
    exact ⟨i, by rw [Ideal.mem_comap, liftForm_X]; exact hi⟩
  · obtain ⟨j, hj⟩ := hrel none
    exact ⟨j, hj⟩

theorem powMonomial_not_mem {W : Ideal (MRing ι R)} (hW : W.IsPrime) (hrel : IsRelevant W) (e : K → ℕ) :
    ∃ i : ∀ k, ι k, powMonomial e i ∉ W := by
  choose i hi using hrel
  refine ⟨i, fun hmem => ?_⟩
  have h : powMonomial e i ∈ W.primeCompl :=
    W.primeCompl.prod_mem fun k _ => W.primeCompl.pow_mem (hi k) _
  exact h hmem

def blowUpCof (s m : MRing ι R) (e : K → ℕ) (u₀ v₀ : MRing ι R) : BlowUpIdx ι → MRing ι R
  | none => u₀ * s
  | some none => v₀ * m
  | some (some i) => v₀ * powMonomial e i

theorem blowUpCof_spec {P : Ideal (MRing ι R)} {s g f m u₀ v₀ : MRing ι R} (e : K → ℕ)
    (h : u₀ * f - v₀ * g ∈ P) (j : BlowUpIdx ι) :
    u₀ * blowUpGens s g f m e j - g * blowUpCof s m e u₀ v₀ j ∈ P := by
  rcases j with _ | _ | i
  · simp only [blowUpGens, blowUpCof]
    rw [show u₀ * (s * g) - g * (u₀ * s) = 0 by ring]
    exact P.zero_mem
  · simp only [blowUpGens, blowUpCof]
    rw [show u₀ * (f * m) - g * (v₀ * m) = m * (u₀ * f - v₀ * g) by ring]
    exact P.mul_mem_left _ h
  · simp only [blowUpGens, blowUpCof]
    rw [show u₀ * (f * powMonomial e i) - g * (v₀ * powMonomial e i) =
      powMonomial e i * (u₀ * f - v₀ * g) by ring]
    exact P.mul_mem_left _ h

theorem blowUpCof_relation {P : Ideal (MRing ι R)} (hP : P.IsPrime) {s g f m u₀ v₀ : MRing ι R}
    (e : K → ℕ) (hg : g ∉ P) (h : u₀ * f - v₀ * g ∈ P) (j j' : BlowUpIdx ι) :
    newVar j * liftForm (blowUpCof s m e u₀ v₀ j') - newVar j' * liftForm (blowUpCof s m e u₀ v₀ j) ∈
      blowUpOf P (blowUpGens s g f m e) := by
  apply mem_blowUpOf_of_sub
  have h1 := blowUpCof_spec (s := s) (m := m) e h j
  have h2 := blowUpCof_spec (s := s) (m := m) e h j'
  generalize blowUpGens s g f m e j = x at h1 ⊢
  generalize blowUpGens s g f m e j' = x' at h2 ⊢
  generalize blowUpCof s m e u₀ v₀ j = a at h1 ⊢
  generalize blowUpCof s m e u₀ v₀ j' = a' at h2 ⊢
  have key : g * (x * a' - x' * a) ∈ P := by
    rw [show g * (x * a' - x' * a) = x' * (u₀ * x - g * a) - x * (u₀ * x' - g * a') by ring]
    exact P.sub_mem (P.mul_mem_left _ h1) (P.mul_mem_left _ h2)
  exact (hP.mem_or_mem key).resolve_left hg

theorem blowUp_offSpecial {P : Ideal (MRing ι R)} (hP : P.IsPrime) {s g f m : MRing ι R} (e : K → ℕ)
    (hg : g ∉ P) {W : Ideal (MRing (extIdx ι (BlowUpIdx ι)) R)} (hW : W.IsPrime)
    (hQW : blowUpOf P (blowUpGens s g f m e) ≤ W) (hrel : IsRelevant W) {u₀ v₀ : MRing ι R}
    (hv : liftForm v₀ ∉ W) (h : u₀ * f - v₀ * g ∈ P) :
    ∃ i : ∀ k, ι k, liftForm (powMonomial e i) ∉ W ∧ newVar (some (some i)) ∉ W ∧
      (liftForm m ∉ W → newVar (some none) ∉ W) := by
  have mnm : ∀ {x y}, x ∉ W → y ∉ W → x * y ∉ W := fun hx hy hxy => (hW.mem_or_mem hxy).elim hx hy
  obtain ⟨hW₀, -, hrel₀, j, hj⟩ := comap_liftForm_facts hW hQW hrel
  obtain ⟨i, hi⟩ := powMonomial_not_mem hW₀ hrel₀ e
  have hi' : liftForm (powMonomial e i) ∉ W := hi
  have key : ∀ j', liftForm (blowUpCof s m e u₀ v₀ j') ∉ W → newVar j' ∉ W := by
    intro j' ha hj'
    have hr := hQW (blowUpCof_relation hP e hg h j j')
    have h3 : newVar j * liftForm (blowUpCof s m e u₀ v₀ j') ∈ W := by
      have h4 := W.add_mem hr (W.mul_mem_right (liftForm (blowUpCof s m e u₀ v₀ j)) hj')
      rwa [sub_add_cancel] at h4
    exact mnm hj ha h3
  refine ⟨i, hi', key _ ?_, fun hm => key _ ?_⟩
  · show liftForm (v₀ * powMonomial e i) ∉ W
    rw [map_mul]; exact mnm hv hi'
  · show liftForm (v₀ * m) ∉ W
    rw [map_mul]; exact mnm hv hm

end Helpers

theorem BlowUpDecomposition.proof (hmodel : BlowUpModel.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) : BlowUpDecomposition.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e hce m hm hmP hmH
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hDv := hD.1
  obtain ⟨⟨bf, bg, hf, hg, hb⟩, hfP, hgP, -, hunit⟩ := hD.1
  set Q := blowUpOf P (blowUpGens s g f m e) with hQ
  have hsgP : s * g ∉ P := fun h => (hPp.mem_or_mem h).elim hsP hgP
  have hfmP : f * m ∉ P := fun h => (hPp.mem_or_mem h).elim hfP hmP
  have hdeg : c + bg = bf + e := by
    funext k
    have h1 : (bf k : ℤ) - bg k = b k := congrFun hb k
    have h2 := hce k
    simp only [Pi.add_apply]
    omega
  have hgens : ∀ j, IsMultiHomog (blowUpGens s g f m e j) (c + bg) := by
    rintro (_ | _ | i)
    · exact hs.mul hg
    · rw [hdeg]; exact hf.mul hm
    · rw [hdeg]; exact hf.mul (isMultiHomog_powMonomial e i)
  have hmod := hmodel O K ι (BlowUpIdx ι) P (d + 1) hP (c + bg) (blowUpGens s g f m e) hgens
    ⟨none, hsgP⟩
  have hQp : Q.IsPrime := hmod.multiProj.isPrime
  have hY₁ : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ Q :=
    newVar_not_mem_blowUpOf (u := blowUpGens s g f m e) (j := some none) hfmP

  have hdegRes : ∃ bf' bg' : Option K → ℕ, IsMultiHomog (newVar (some none) :
      MRing (extIdx ι (BlowUpIdx ι)) O) bf' ∧ IsMultiHomog (liftForm (J := BlowUpIdx ι) m) bg' ∧
      (fun k => (bf' k : ℤ) - bg' k) = residualDeg e :=
    ⟨Pi.single none 1, liftMDeg e, isWeightedHomogeneous_X _ _ _, isMultiHomog_liftForm hm, by
      funext o; cases o <;> simp [residualDeg, liftDeg, liftMDeg]⟩
  have hdegExc : ∃ bf' bg' : Option K → ℕ, IsMultiHomog (liftForm (J := BlowUpIdx ι) (f * m)) bf' ∧
      IsMultiHomog (liftForm g * newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) bg' ∧
      (fun k => (bf' k : ℤ) - bg' k) = exceptionalDeg b e := by
    refine ⟨liftMDeg (bf + e), liftMDeg bg + Pi.single none 1, isMultiHomog_liftForm (hf.mul hm),
      (isMultiHomog_liftForm hg).mul (isWeightedHomogeneous_X _ _ _), ?_⟩
    funext o
    cases o with
    | none => simp [exceptionalDeg, liftDeg, liftMDeg]
    | some k =>
      have h1 : (bf k : ℤ) - bg k = b k := congrFun hb k
      simp [exceptionalDeg, liftDeg, liftMDeg]
      omega

  have hoff : ∀ W : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O), W.IsPrime → Q ≤ W → IsRelevant W →
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ W →
      (∃ u v, u ∉ W ∧ v ∉ W ∧ u * newVar (some none) - v * liftForm m ∈ Q) ∧
      (∃ u v, u ∉ W ∧ v ∉ W ∧ u * liftForm (f * m) - v * (liftForm g * newVar (some none)) ∈ Q) ∧
      (liftForm m ∉ W → newVar (some none) ∉ W) := by
    intro W hW hQW hrel hϖW
    have mnm : ∀ {x y}, x ∉ W → y ∉ W → x * y ∉ W := fun hx hy hxy => (hW.mem_or_mem hxy).elim hx hy
    obtain ⟨hW₀, hPW₀, hrel₀, -⟩ := comap_liftForm_facts hW hQW hrel
    obtain ⟨u₀, v₀, hu, hv, h⟩ := hunit _ hW₀ hPW₀ hrel₀ (by rw [Ideal.mem_comap, liftForm_C]; exact hϖW)
    obtain ⟨i, hpm, hYi, hY₁m⟩ := blowUp_offSpecial hPp e hgP hW hQW hrel (u₀ := u₀) hv h
    refine ⟨⟨liftForm (powMonomial e i), newVar (some (some i)), hpm, hYi, ?_⟩,
      ⟨liftForm u₀ * newVar (some (some i)), liftForm (v₀ * powMonomial e i), mnm hu hYi,
        by rw [map_mul]; exact mnm hv hpm, ?_⟩, hY₁m⟩
    · have h3 := mem_blowUpOf_of_sub (P := P) (u := blowUpGens s g f m e) (j := some none)
        (j' := some (some i)) (a := powMonomial e i) (a' := m) (by
          simp only [blowUpGens]
          rw [show f * m * powMonomial e i - f * powMonomial e i * m = 0 by ring]
          exact P.zero_mem)
      convert h3 using 1; ring
    · have h3 := mem_blowUpOf_of_sub (P := P) (u := blowUpGens s g f m e) (j := some (some i))
        (j' := some none) (a := u₀ * (f * m)) (a' := v₀ * powMonomial e i * g) (by
          simp only [blowUpGens]
          rw [show f * powMonomial e i * (u₀ * (f * m)) - f * m * (v₀ * powMonomial e i * g) =
            (f * m * powMonomial e i) * (u₀ * f - v₀ * g) by ring]
          exact P.mul_mem_left _ h)
      convert h3 using 1; simp only [map_mul]; ring

  have hRes : IsEffectiveVertical Q ϖ (residualDeg e) (newVar (some none)) (liftForm m) := by
    refine ⟨IsVerticalDivisor.of_unit_off_special hdegRes hY₁ (liftForm_not_mem_blowUpOf hmP)
      fun W hW hQW hrel hϖW => (hoff W hW hQW hrel hϖW).1, ?_⟩
    intro W hW hQW hrel
    obtain ⟨hW₀, -, hrel₀, -⟩ := comap_liftForm_facts hW hQW hrel
    obtain ⟨i, hi⟩ := powMonomial_not_mem hW₀ hrel₀ e
    refine ⟨liftForm (powMonomial e i), newVar (some (some i)), hi, ?_⟩
    have h3 := mem_blowUpOf_of_sub (P := P) (u := blowUpGens s g f m e) (j := some none)
      (j' := some (some i)) (a := powMonomial e i) (a' := m) (by
        simp only [blowUpGens]
        rw [show f * m * powMonomial e i - f * powMonomial e i * m = 0 by ring]
        exact P.zero_mem)
    convert h3 using 1; ring
  have hExc : IsEffectiveVertical Q ϖ (exceptionalDeg b e) (liftForm (f * m))
      (liftForm g * newVar (some none)) := by
    refine ⟨IsVerticalDivisor.of_unit_off_special hdegExc (liftForm_not_mem_blowUpOf hfmP)
      (fun h => (hQp.mem_or_mem h).elim (liftForm_not_mem_blowUpOf hgP) hY₁)
      fun W hW hQW hrel hϖW => (hoff W hW hQW hrel hϖW).2.1, ?_⟩
    intro W hW hQW hrel
    obtain ⟨hW₀, hPW₀, hrel₀, j, hj⟩ := comap_liftForm_facts hW hQW hrel
    obtain ⟨u₀, v₀, hu, h⟩ := hD.2 _ hW₀ hPW₀ hrel₀
    refine ⟨liftForm u₀ * newVar j, liftForm (blowUpCof s m e u₀ v₀ j),
      fun h' => (hW.mem_or_mem h').elim hu hj, ?_⟩
    have h3 := mem_blowUpOf_of_sub (P := P) (u := blowUpGens s g f m e) (j := j)
      (j' := some none) (a := u₀ * (f * m)) (a' := blowUpCof s m e u₀ v₀ j * g) (by
        have h4 := blowUpCof_spec (s := s) (m := m) e h j
        show blowUpGens s g f m e j * (u₀ * (f * m)) - f * m * (blowUpCof s m e u₀ v₀ j * g) ∈ P
        rw [show blowUpGens s g f m e j * (u₀ * (f * m)) - f * m * (blowUpCof s m e u₀ v₀ j * g) =
          (f * m) * (u₀ * blowUpGens s g f m e j - g * blowUpCof s m e u₀ v₀ j) by ring]
        exact P.mul_mem_left _ h4)
    convert h3 using 1; simp only [map_mul]; ring

  have hhor : ∀ H : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ H →
      (divCycle Q (liftForm s) H ≠ 0 ∨ divCycle Q (newVar none) H ≠ 0) →
      IsVerticalDivisor H ϖ (residualDeg e) (newVar (some none)) (liftForm m) ∧
      IsVerticalDivisor H ϖ (exceptionalDeg b e) (liftForm (f * m)) (liftForm g * newVar (some none)) := by
    intro H hϖH hH
    have hsupp : H.IsPrime ∧ Q ≤ H ∧ IsRelevant H := by
      rcases hH with hH | hH
      · exact le_and_isRelevant_of_divCycle_ne_zero hH
      · exact le_and_isRelevant_of_divCycle_ne_zero hH
    obtain ⟨hHp, hQH, hHrel⟩ := hsupp
    have mnm : ∀ {x y}, x ∉ H → y ∉ H → x * y ∉ H := fun hx hy hxy => (hHp.mem_or_mem hxy).elim hx hy
    have h0 := hst O ϖ hϖ K ι P d hP b f g hDv s hsP e m H hϖH hH
    have hϖH₀ : (C ϖ : MRing ι O) ∉ H.comap (liftForm (J := BlowUpIdx ι)) := by
      rw [Ideal.mem_comap, liftForm_C]; exact hϖH
    have hvH₀ := hsH _ h0 hϖH₀
    have hmH : liftForm m ∉ H := hmH _ h0 hϖH₀
    have hfH : liftForm f ∉ H := hvH₀.num_not_mem
    have hgH : liftForm g ∉ H := hvH₀.den_not_mem
    have hY₁H := (hoff H hHp hQH hHrel hϖH).2.2 hmH
    have tr : ∀ {F G : MRing (extIdx ι (BlowUpIdx ι)) O},
        (∀ W : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O), W.IsPrime → Q ≤ W → IsRelevant W →
          (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ W → ∃ u v, u ∉ W ∧ v ∉ W ∧ u * F - v * G ∈ Q) →
        ∀ W : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O), W.IsPrime → H ≤ W → IsRelevant W →
          (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ W → ∃ u v, u ∉ W ∧ v ∉ W ∧ u * F - v * G ∈ H := by
      intro F G hF W hW hHW hrel hϖW
      obtain ⟨u', v', hu', hv', h'⟩ := hF W hW (hQH.trans hHW) hrel hϖW
      exact ⟨u', v', hu', hv', hQH h'⟩
    refine ⟨IsVerticalDivisor.of_unit_off_special hdegRes hY₁H hmH
        (tr fun W hW hQW hrel hϖW => (hoff W hW hQW hrel hϖW).1),
      IsVerticalDivisor.of_unit_off_special hdegExc (by rw [map_mul]; exact mnm hfH hmH) (mnm hgH hY₁H)
        (tr fun W hW hQW hrel hϖW => (hoff W hW hQW hrel hϖW).2.1)⟩
  exact ⟨hmod, isMultiHomog_liftForm hs, liftForm_not_mem_blowUpOf hsP,
    newVar_not_mem_blowUpOf (u := blowUpGens s g f m e) (j := none) hsgP, hRes, hExc,
    fun H hH hϖH => hhor H hϖH (Or.inl hH), fun H hH hϖH => (hhor H hϖH (Or.inr hH)).2⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR

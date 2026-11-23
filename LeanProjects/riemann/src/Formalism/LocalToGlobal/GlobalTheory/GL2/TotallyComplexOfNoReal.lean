import Formalism.LocalToGlobal.GlobalTheory.GL2.Statement
import Formalism.SharpRestriction.GlobalSchurBounds.FirstClaimLemmaTwoFourOfLemmaTwoThree
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.UnipotentAdelicQuotients.ClassNumberQuad

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ShortIntervalPrimes NumberField

section Ray

variable {K0 : Type} [Field K0] [NumberField K0]

lemma exists_mem_sub_one_mem (qq I : Ideal (𝓞 K0)) (hI : CoprimeTo K0 qq I) :
    ∃ b ∈ I, b ≠ 0 ∧ b - 1 ∈ qq := by
  obtain ⟨i, hi, t, ht, hit⟩ := Submodule.mem_sup.1 (show (1 : 𝓞 K0) ∈ I ⊔ qq by rw [hI.2]; trivial)
  by_cases h0 : i = 0
  · subst h0
    have ht1 : t = 1 := by simpa using hit
    have hq : qq = ⊤ := (Ideal.eq_top_iff_one qq).2 (ht1 ▸ ht)
    obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI.1
    exact ⟨b, hb, hb0, by rw [hq]; trivial⟩
  · refine ⟨i, hi, h0, ?_⟩
    have : i - 1 = -t := by rw [← hit]; ring
    rw [this]
    exact qq.neg_mem ht

lemma exists_inv_mod (qq : Ideal (𝓞 K0)) (a : 𝓞 K0) (ha : Ideal.span {a} ⊔ qq = ⊤) :
    ∃ c : 𝓞 K0, c ≠ 0 ∧ c * a - 1 ∈ qq := by
  obtain ⟨c, t, ht, hct⟩ :=
    Ideal.mem_span_singleton_sup.1 (show (1 : 𝓞 K0) ∈ Ideal.span {a} ⊔ qq by rw [ha]; trivial)
  by_cases h0 : c = 0
  · subst h0
    have ht1 : t = 1 := by simpa using hct
    refine ⟨1, one_ne_zero, ?_⟩
    rw [(Ideal.eq_top_iff_one qq).2 (ht1 ▸ ht)]
    trivial
  · refine ⟨c, h0, ?_⟩
    have : c * a - 1 = -t := by rw [← hct]; ring
    rw [this]
    exact qq.neg_mem ht

lemma exists_rel_of_class (qq I J : Ideal (𝓞 K0)) (hI : CoprimeTo K0 qq I) (hJ : CoprimeTo K0 qq J)
    (x y : 𝓞 K0) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : Ideal.span {x} * I = Ideal.span {y} * J) :
    ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ b - 1 ∈ qq ∧ Ideal.span {a} ⊔ qq = ⊤ ∧
      Ideal.span {a} * I = Ideal.span {b} * J := by
  obtain ⟨b, hbI, hb0, hb1⟩ := exists_mem_sub_one_mem qq I hI
  have hxb : x * b ∈ Ideal.span {y} := by
    have : x * b ∈ Ideal.span {x} * I := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) hbI
    rw [hxy] at this
    exact Ideal.mul_le_left this
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hxb
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at ha
    exact mul_ne_zero hx hb0 ha.symm
  have hy' : Ideal.span {y} ≠ (0 : Ideal (𝓞 K0)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hy
  have key : Ideal.span {a} * I = Ideal.span {b} * J := by
    apply mul_left_cancel₀ hy'
    calc Ideal.span {y} * (Ideal.span {a} * I) = Ideal.span {a * y} * I := by
          rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton, mul_comm y a]
      _ = Ideal.span {b} * (Ideal.span {x} * I) := by
          rw [ha, ← mul_assoc, Ideal.span_singleton_mul_span_singleton, mul_comm b x]
      _ = Ideal.span {y} * (Ideal.span {b} * J) := by
          rw [hxy, mul_left_comm]
  have hbq : Ideal.span {b} ⊔ qq = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 K0) = b - (b - 1) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self b)) (Ideal.mem_sup_right hb1)
  have hcop : Ideal.span {b} * J ⊔ qq = ⊤ := by
    have h1 : IsCoprime (Ideal.span {b}) qq := Ideal.isCoprime_iff_sup_eq.2 hbq
    have h2 : IsCoprime J qq := Ideal.isCoprime_iff_sup_eq.2 hJ.2
    exact Ideal.isCoprime_iff_sup_eq.1 (h1.mul_left h2)
  have haq : Ideal.span {a} ⊔ qq = ⊤ := by
    rw [← key] at hcop
    refine top_unique ?_
    calc (⊤ : Ideal (𝓞 K0)) = Ideal.span {a} * I ⊔ qq := hcop.symm
      _ ≤ Ideal.span {a} ⊔ qq := sup_le_sup_right Ideal.mul_le_left qq
  exact ⟨a, b, ha0, hb0, hb1, haq, key⟩

theorem grCard_le_of_noReal (hE : IsEmpty (K0 →+* ℝ)) (qq : Ideal (𝓞 K0)) (hqq : qq ≠ ⊥) :
    Nat.card (RayCls K0 qq) ≤ classNumber K0 * Ideal.absNorm qq ∧ 0 < Nat.card (RayCls K0 qq) := by
  classical
  have htop : CoprimeTo K0 qq ⊤ := ⟨top_ne_bot, top_sup_eq qq⟩
  have hne : Nonempty {I : Ideal (𝓞 K0) // CoprimeTo K0 qq I} := ⟨⟨⊤, htop⟩⟩
  let cls : {I : Ideal (𝓞 K0) // CoprimeTo K0 qq I} → ClassGroup (𝓞 K0) := fun I =>
    ClassGroup.mk0 ⟨I.1, mem_nonZeroDivisors_of_ne_zero (by rw [Ne, Ideal.zero_eq_bot]; exact I.2.1)⟩
  let rep : ClassGroup (𝓞 K0) → {I : Ideal (𝓞 K0) // CoprimeTo K0 qq I} := fun C =>
    Classical.epsilon (fun J => cls J = C)
  have hrep : ∀ I, cls (rep (cls I)) = cls I := fun I =>
    Classical.epsilon_spec (p := fun J => cls J = cls I) ⟨I, rfl⟩
  have hex : ∀ I : {I : Ideal (𝓞 K0) // CoprimeTo K0 qq I}, ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ b - 1 ∈ qq ∧
      Ideal.span {a} ⊔ qq = ⊤ ∧ Ideal.span {a} * I.1 = Ideal.span {b} * (rep (cls I)).1 := by
    intro I
    obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 (hrep I).symm
    exact exists_rel_of_class qq I.1 _ I.2 (rep (cls I)).2 x y hx hy hxy
  choose a b ha0 hb0 hb1 haq hab using hex
  let F : {I : Ideal (𝓞 K0) // CoprimeTo K0 qq I} → ClassGroup (𝓞 K0) × (𝓞 K0 ⧸ qq) := fun I =>
    (cls I, Ideal.Quotient.mk qq (a I))
  have hF : ∀ I J, F I = F J → RayRel K0 qq I.1 J.1 := by
    intro I J h
    have hc : cls I = cls J := congrArg Prod.fst h
    have ha : a I - a J ∈ qq := Ideal.Quotient.eq.1 (congrArg Prod.snd h)
    have hrIJ : rep (cls I) = rep (cls J) := by rw [hc]
    obtain ⟨c, hc0, hc1⟩ := exists_inv_mod qq (a I) (haq I)
    refine ⟨c * a I * b J, c * a J * b I, mul_ne_zero (mul_ne_zero hc0 (ha0 I)) (hb0 J),
      mul_ne_zero (mul_ne_zero hc0 (ha0 J)) (hb0 I), ?_, ?_, fun σ => by have := hE; exact isEmptyElim σ, ?_⟩
    · have : c * a I * b J - 1 = c * a I * (b J - 1) + (c * a I - 1) := by ring
      rw [this]
      exact qq.add_mem (qq.mul_mem_left _ (hb1 J)) hc1
    · have : c * a J * b I - 1 = c * b I * (-(a I - a J)) + c * a I * (b I - 1) + (c * a I - 1) := by ring
      rw [this]
      exact qq.add_mem (qq.add_mem (qq.mul_mem_left _ (qq.neg_mem ha)) (qq.mul_mem_left _ (hb1 I))) hc1
    · have e1 := hab I
      have e2 := hab J
      rw [hrIJ] at e1
      calc Ideal.span {c * a I * b J} * I.1
          = Ideal.span {c} * Ideal.span {b J} * (Ideal.span {a I} * I.1) := by
            rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton]; ring
        _ = Ideal.span {c} * Ideal.span {b J} * (Ideal.span {b I} * (rep (cls J)).1) := by rw [e1]
        _ = Ideal.span {c} * Ideal.span {b I} * (Ideal.span {b J} * (rep (cls J)).1) := by ring
        _ = Ideal.span {c} * Ideal.span {b I} * (Ideal.span {a J} * J.1) := by rw [e2]
        _ = Ideal.span {c * a J * b I} * J.1 := by
            rw [← Ideal.span_singleton_mul_span_singleton (c * a J), ← Ideal.span_singleton_mul_span_singleton c]
            ring
  let G : RayCls K0 qq → ClassGroup (𝓞 K0) × (𝓞 K0 ⧸ qq) := fun R => F (Quot.out R)
  have hG : Function.Injective G := by
    intro R R' h
    rw [← Quot.out_eq R, ← Quot.out_eq R']
    exact Quot.sound (hF _ _ h)
  have hN : Nat.card (𝓞 K0 ⧸ qq) = Ideal.absNorm qq := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hN0 : Ideal.absNorm qq ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hqq
  have : Finite (𝓞 K0 ⧸ qq) := Nat.finite_of_card_ne_zero (hN ▸ hN0)
  have : Finite (RayCls K0 qq) := Finite.of_injective G hG
  have : Nonempty (RayCls K0 qq) := ⟨Quot.mk _ ⟨⊤, htop⟩⟩
  refine ⟨?_, Nat.card_pos⟩
  have hle := Nat.card_le_card_of_injective G hG
  rw [Nat.card_prod, hN] at hle
  rw [classNumber, ← Nat.card_eq_fintype_card]
  exact hle

theorem totallyComplex_of_noReal (hE : IsEmpty (K0 →+* ℝ)) : IsTotallyComplex K0 :=
  ⟨fun v => InfinitePlace.not_isReal_iff_isComplex.1 fun hv => by
    have := hE
    exact isEmptyElim (InfinitePlace.embedding_of_isReal hv)⟩

variable (hCN : HeckeCharacterZeroLocus.ClassNumberQuad.ClassNumberLe.{0})
include hCN

theorem classNumber_le_four (hK : Module.finrank ℚ K0 = 2) (hc : IsTotallyComplex K0) :
    (classNumber K0 : ℝ) ≤ 4 * |(discr K0 : ℝ)| := by
  have h := hCN K0 hK hc
  have hD1 : (1 : ℝ) ≤ |(discr K0 : ℝ)| := by
    have : (1 : ℤ) ≤ |discr K0| := Int.one_le_abs (discr_ne_zero K0)
    exact_mod_cast this
  have hs0 : 0 < Real.sqrt |(discr K0 : ℝ)| := Real.sqrt_pos.2 (by linarith)
  have hs2 : Real.sqrt |(discr K0 : ℝ)| ^ 2 = |(discr K0 : ℝ)| := Real.sq_sqrt (by linarith)
  have hlog : Real.log |(discr K0 : ℝ)| ≤ 2 * (Real.sqrt |(discr K0 : ℝ)| - 1) := by
    have e : Real.log |(discr K0 : ℝ)| = 2 * Real.log (Real.sqrt |(discr K0 : ℝ)|) := by
      rw [Real.log_sqrt (by linarith)]; ring
    rw [e]
    have := Real.log_le_sub_one_of_pos hs0
    linarith
  have hpi := Real.pi_gt_three
  calc (classNumber K0 : ℝ) ≤ Real.sqrt |(discr K0 : ℝ)| * (Real.log |(discr K0 : ℝ)| + 2) / Real.pi := h
    _ ≤ Real.sqrt |(discr K0 : ℝ)| * (2 * Real.sqrt |(discr K0 : ℝ)|) / Real.pi := by
        gcongr
        linarith
    _ ≤ 4 * |(discr K0 : ℝ)| := by
        rw [div_le_iff₀ Real.pi_pos]
        nlinarith

theorem grBound_of (hK : Module.finrank ℚ K0 = 2) (hE : IsEmpty (K0 →+* ℝ)) : GrBound K0 := by
  intro qq hqq
  obtain ⟨hle, hpos⟩ := grCard_le_of_noReal hE qq hqq
  refine ⟨hpos, ?_⟩
  have hh := classNumber_le_four hCN hK (totallyComplex_of_noReal hE)
  have h1 : (grCard K0 qq : ℝ) ≤ (classNumber K0 : ℝ) * (Ideal.absNorm qq : ℝ) := by
    unfold grCard
    exact_mod_cast hle
  unfold Bmod
  calc (grCard K0 qq : ℝ) ≤ (classNumber K0 : ℝ) * (Ideal.absNorm qq : ℝ) := h1
    _ ≤ 4 * |(discr K0 : ℝ)| * (Ideal.absNorm qq : ℝ) := by gcongr

end Ray

theorem finrank_sqrt_K (D : D7) :
    Module.finrank ℚ D.host.K = 2 ∧ ∃ s : D.host.K, s ^ 2 = -(D.host.d : D.host.K) := by
  have hd := D.host.hyp
  have hsq : D.host.sqd ^ 2 = -(D.host.d : D.host.E) :=
    Formalism.BasicNotions.Examples₂.bE_sq D.host
  have hK : Module.finrank ℚ D.host.K = 2 :=
    Formalism.FrobeniusOrbits.SplitK.finrank_K (L := D.host.E) (b := D.host.sqd) hd.2.1.pos hsq
  have hmem : D.host.sqd ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  exact ⟨hK, ⟨_, hmem⟩, by apply Subtype.ext; push_cast; exact hsq⟩

theorem noReal_K (D : D7) : IsEmpty (D.host.K →+* ℝ) := by
  obtain ⟨s, hs⟩ := (finrank_sqrt_K D).2
  refine ⟨fun σ => ?_⟩
  have h := congrArg σ hs
  rw [map_pow, map_neg, map_natCast] at h
  have hd : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have := sq_nonneg (σ s)
  linarith

theorem grBound_K (hCN : HeckeCharacterZeroLocus.ClassNumberQuad.ClassNumberLe.{0}) (D : D7) : GrBound D.host.K :=
  grBound_of hCN (finrank_sqrt_K D).1 (noReal_K D)

theorem linkAux_of_classNumberLe (hCN : HeckeCharacterZeroLocus.ClassNumberQuad.ClassNumberLe.{0}) : LinkPointsLemma := by
  intro C0 Cr cr cQ cQ' hC0 hCr hcr hcQ hcQ'
  obtain ⟨C0', c1, c2, p1, p2, p3, h⟩ := lemma_three_of_Q4_growth_bound C0 Cr cr cQ cQ' hC0 hCr hcr hcQ hcQ'
  exact ⟨C0', c1, c2, p1, p2, p3, fun D cT _ ha => h D cT ha (grBound_K hCN D)⟩

end Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

end

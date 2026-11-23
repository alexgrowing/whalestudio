import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutProjection
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagCutContraction

theorem pullDeg_comp_of_eq_zero {K K' : Type*} (j : K ↪ K') (b : K' → ℤ)
    (hb : ∀ o, o ∉ Set.range j → b o = 0) : FieldNumbers.pullDeg j (b ∘ j) = b := by
  funext o
  by_cases ho : ∃ a, j a = o
  · obtain ⟨a, rfl⟩ := ho
    exact j.injective.extend_apply (b ∘ j) 0 a
  · rw [FieldNumbers.pullDeg, Function.extend_apply' _ _ _ ho, Pi.zero_apply]
    exact (hb o (by simpa [Set.mem_range] using ho)).symm

theorem withBot_le_of_lt_succ (a : WithBot ℕ∞) (m : ℕ) (h : a < ((m + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ ((m : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) < (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      exact absurd (WithBot.coe_lt_coe.mp h') (by simp)
    | coe c =>
      have h' : (((c : ℕ) : ℕ∞) : WithBot ℕ∞) < (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      have hc : c < m + 1 := by exact_mod_cast WithBot.coe_lt_coe.mp h'
      show (((c : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((m : ℕ) : ℕ∞) : WithBot ℕ∞)
      exact WithBot.coe_le_coe.mpr (by exact_mod_cast (by omega : c ≤ m))

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K' : Type} [Fintype K'] [DecidableEq K'] {ι' : K' → Type} [∀ o, Fintype (ι' o)]

omit [IsDomain O] [IsDiscreteValuationRing O] [∀ o, Fintype (ι' o)] in

theorem ratDiv_support {P W : Ideal (MRing ι' O)} (hPm : IsMultiHomogIdeal P) {cs ch : K' → ℕ}
    {s h : MRing ι' O} (hs : IsMultiHomog s cs) (hh : IsMultiHomog h ch) (hW : ratDiv P s h W ≠ 0) :
    W.IsPrime ∧ P ≤ W ∧ IsMultiHomogIdeal W := by
  have key : ∀ {c : K' → ℕ} {u : MRing ι' O}, IsMultiHomog u c → divCycle P u W ≠ 0 →
      W.IsPrime ∧ P ≤ W ∧ IsMultiHomogIdeal W := by
    intro c u hu hne
    unfold divCycle at hne
    split_ifs at hne with hW'
    · exact ⟨hW'.1.1.1, le_sup_left.trans hW'.1.1.2,
        MinimalPrimeMultiHomog.full O K' ι' _ W (SupSpanMultiHomog.full O K' ι' P u c hPm hu) hW'.1⟩
    · exact absurd rfl hne
  by_cases h1 : divCycle P s W = 0
  · exact key hh fun h2 => hW (by simp [ratDiv, h1, h2])
  · exact key hs h1

theorem vNumL_eq_zero_of_contract {ϖ : O} (hϖ : Irreducible ϖ) {P W : Ideal (MRing ι' O)} {n : ℕ}
    (hP : IsModelOver P n) [hWp : W.IsPrime] (hPW : P ≤ W) (hWm : IsMultiHomogIdeal W)
    (hϖW : (C ϖ : MRing ι' O) ∈ W) {K : Type} [Fintype K] [DecidableEq K] (j : K ↪ K')
    (hcon : FieldNumbers.relDim (FieldNumbers.contractPrime j (specialIdeal W)) < ((n : ℕ) : WithBot (WithTop ℤ)))
    (l : List (K' → ℤ)) (hl : l.length = n) (hlj : ∀ b ∈ l, ∀ o, o ∉ Set.range j → b o = 0) :
    vNumL W l = 0 := by
  subst hl
  have : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι' O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι' O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'
  have hlt : P < W := lt_of_le_of_ne hPW (fun h => hϖP (h ▸ hϖW))
  have hdrop := DimStrictDrop.full (MRing ι' O) P W hlt
  rw [hP.dim] at hdrop
  obtain ⟨hQp, -, -, -⟩ := SpecialIdealCorresp.full O ϖ hϖ K' ι' P W hWp hϖW
  have hQm := SpecialIdealMultiHomog.full O K' ι' W hWm
  have hdimQ : ringKrullDim (MRing ι' (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
      ((l.length + Fintype.card K' + 1 : ℕ) : WithBot ℕ∞) := by
    rw [SpecialQuotDim.full O ϖ hϖ K' ι' W hϖW]
    refine lt_natCast_of_add_one_le ?_
    have e : l.length + Fintype.card K' + 1 = l.length + 1 + Fintype.card K' := by omega
    rw [e]
    exact hdrop
  change intNum (IsLocalRing.ResidueField O) (specialIdeal W) l.get = 0
  by_cases hcase : ¬ IsRelevant (specialIdeal W) ∨ ringKrullDim (MRing ι' (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
      ((l.length + Fintype.card K' : ℕ) : WithBot ℕ∞)
  · exact IntNumVanish.full (IsLocalRing.ResidueField O) K' ι' l.length (specialIdeal W) hQp hQm hcase l.get
  · push Not at hcase
    obtain ⟨hrel, hge⟩ := hcase
    have hdimEq : ringKrullDim (MRing ι' (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
        ((l.length + Fintype.card K' : ℕ) : WithBot ℕ∞) :=
      le_antisymm (withBot_le_of_lt_succ _ _ hdimQ) hge
    have hrelQ : FieldNumbers.relDim (specialIdeal W) = ((l.length : ℕ) : WithBot (WithTop ℤ)) := by
      rw [FieldNumbers.relDim, hdimEq]
      have : (((l.length + Fintype.card K' : ℕ) : ℤ) - Fintype.card K') = l.length := by push_cast; ring
      exact congrArg (fun z : ℤ => ((z : WithTop ℤ) : WithBot (WithTop ℤ))) this
    have hz := FieldNumbers.ProjectionFormulaContracted.full (IsLocalRing.ResidueField O) K K' j ι' (specialIdeal W)
      ⟨hQp, hQm, hrel⟩ l.length hrelQ hcon (fun i => l.get i ∘ j)
    rw [← hz]
    congr 1
    funext i
    exact (pullDeg_comp_of_eq_zero j _ (hlj _ (List.get_mem l i))).symm

end SegreFlagCutContraction

open SegreFlagCutContraction in

theorem SegreFlagCutContraction.proof (hModel : SegreFlagClosureModel.Statement)
    (hProj : SegreFlagCutProjection.Statement) : SegreFlagCutContraction.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk
  have hH : IsModelOver (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) (d + k) := by
    have h := (hModel O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
      Φ e t ht (k + 1) (by omega) (by omega)).1
    simpa using h
  obtain ⟨hp1, hp2⟩ := hProj O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  refine ⟨fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW l hl hl0 => ?_,
    fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW l hl hl0 => ?_⟩
  · obtain ⟨hWp, hPW, hWm⟩ := ratDiv_support hH.multiProj.multiHomog hs hh hW
    refine vNumL_eq_zero_of_contract hϖ hH hPW hWm hϖW Function.Embedding.some
      (hp1 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW) l hl fun b hb o ho => ?_
    cases o with
    | none => exact hl0 b hb
    | some o => exact absurd ⟨o, rfl⟩ ho
  · obtain ⟨hWp, hPW, hWm⟩ := ratDiv_support hH.multiProj.multiHomog hs hh hW
    refine vNumL_eq_zero_of_contract hϖ hH hPW hWm hϖW secondFactorBlocks
      (hp2 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW) l hl fun b hb o ho => ?_
    rcases o with _ | _ | o
    · exact absurd ⟨none, rfl⟩ ho
    · exact hl0 b hb
    · exact absurd ⟨some o, rfl⟩ ho

end

end GroundTheory.Heights₂.Heights.NumbersDVR

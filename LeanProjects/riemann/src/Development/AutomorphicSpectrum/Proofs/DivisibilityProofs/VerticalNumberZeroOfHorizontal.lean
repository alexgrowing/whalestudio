import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem relDim_lt_of_dim_lt {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} (I : Ideal (MRing ι F)) (n : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) < ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    GroundTheory.Heights₂.Heights.FieldNumbers.relDim I < ((n : ℕ) : WithBot (WithTop ℤ)) := by
  unfold GroundTheory.Heights₂.Heights.FieldNumbers.relDim
  generalize ringKrullDim (MRing ι F ⧸ I) = a at h ⊢
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : (⊤ : ℕ∞) < ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h
      exact not_top_lt h'
    | coe m =>
      have h' : ((m : ℕ) : ℕ∞) < ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h
      have h'' : m < n + Fintype.card K := by exact_mod_cast h'
      have hlt : (m : ℤ) - Fintype.card K < n := by omega
      change (((((m : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)) : WithBot (WithTop ℤ)) <
        (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
      exact_mod_cast hlt

theorem dim_lt_of_two_drops {a b : WithBot ℕ∞} {n : ℕ} (h₁ : a + 1 ≤ b)
    (h₂ : b + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) : a < (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => simp at h₁
    | coe b =>
      have h₁' : a + 1 ≤ b := by exact_mod_cast h₁
      have h₂' : b + 1 ≤ ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast h₂
      have h₃ : b ≤ (n : ℕ∞) := by
        have : b + 1 ≤ (n : ℕ∞) + 1 := by exact_mod_cast h₂'
        exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 this
      have h₄ : a < (n : ℕ∞) := by
        refine lt_of_lt_of_le ?_ h₃
        refine lt_of_lt_of_le ?_ h₁'
        refine ENat.lt_add_one_iff ?_ |>.2 le_rfl
        rintro rfl
        simp at h₁'
        subst h₁'
        simp at h₃
      exact_mod_cast h₄

theorem specialIdeal_dim_add_one_le {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι O)) [W.IsPrime]
    (hW : (C ϖ : MRing ι O) ∉ W) :
    ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) + 1 ≤
      ringKrullDim (MRing ι O ⧸ W) := by
  have hres : IsLocalRing.residue O ϖ = 0 :=
    (IsLocalRing.residue_eq_zero_iff ϖ).2
      ((IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit)
  have hsp : specialIdeal (W ⊔ Ideal.span {(C ϖ : MRing ι O)}) = specialIdeal W := by
    unfold specialIdeal
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, MvPolynomial.map_C, hres, map_zero]
    simp
  have hdim := SpecialQuotDim.full O ϖ hϖ K ι (W ⊔ Ideal.span {(C ϖ : MRing ι O)})
    (Ideal.mem_sup_right (Ideal.subset_span rfl))
  rw [hsp] at hdim
  rw [hdim]
  have hne : Ideal.Quotient.mk W (C ϖ) ≠ 0 := fun h => hW (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hne)
  have he : ringKrullDim ((MRing ι O ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W (C ϖ : MRing ι O)}) =
      ringKrullDim (MRing ι O ⧸ (W ⊔ Ideal.span {(C ϖ : MRing ι O)})) := by
    refine ringKrullDim_eq_of_ringEquiv ?_
    have hm : (Ideal.span {(C ϖ : MRing ι O)}).map (Ideal.Quotient.mk W) =
        Ideal.span {Ideal.Quotient.mk W (C ϖ : MRing ι O)} := by
      rw [Ideal.map_span, Set.image_singleton]
    exact (Ideal.quotEquivOfEq hm.symm).trans (DoubleQuot.quotQuotEquivQuotSup _ _)
  rwa [he] at h1

theorem horizontal_vNumL_eq_zero : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P → ∀ W, divCycle P f W ≠ 0 → (C ϖ : MRing ι O) ∉ W → ∀ l : List (K → ℤ), l.length = d → vNumL W l = 0 := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP a f hf hfP W hW hϖW l hl
  have hPp : P.IsPrime := hP.multiProj.isPrime
  unfold divCycle at hW
  split_ifs at hW with hW'
  swap
  · exact absurd rfl hW
  have hWmin := hW'.1
  have hWp : W.IsPrime := hWmin.1.1
  have hWm : IsMultiHomogIdeal W :=
    MinimalPrimeMultiHomog.full O K ι _ W
      (SupSpanMultiHomog.full O K ι P f a hP.multiProj.multiHomog hf) hWmin
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hfW : f ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hlt : P < W := lt_of_le_of_ne hPW (fun e => hfP (e ▸ hfW))
  have hdrop := DimStrictDrop.full (MRing ι O) P W hlt
  rw [hP.dim] at hdrop
  have hdrop' : ringKrullDim (MRing ι O ⧸ W) + 1 ≤ ((d + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
    have e : d + 1 + Fintype.card K = d + Fintype.card K + 1 := by omega
    rwa [e] at hdrop
  have hdim := dim_lt_of_two_drops (specialIdeal_dim_add_one_le hϖ W hϖW) hdrop'
  subst hl
  exact (GroundTheory.Heights₂.Heights.FieldNumbers.IntNumZeroSlot.full _ K ι (specialIdeal W)).2
    (SpecialIdealMultiHomog.full O K ι W hWm) _ _ (relDim_lt_of_dim_lt _ _ hdim)

end GlobalTheory.CompanionTheory.Ar.Num

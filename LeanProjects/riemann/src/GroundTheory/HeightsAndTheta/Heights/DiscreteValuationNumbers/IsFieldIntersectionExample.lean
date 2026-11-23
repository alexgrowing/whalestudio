import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumIsFieldIntersection
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumPoint
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumRatSection
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomogIdeal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabDivCycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

universe u

namespace Numbers

abbrev Statement : Prop := IntNumIsFieldIntersection.Statement.{u}

theorem proof (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) : Statement.{u} :=
  IntNumIsFieldIntersection.proof VocabMultiHomog.proof
    (VocabMultiHomogIdeal.proof VocabMultiHomog.proof) VocabDivCycle.proof
    (IntNumPoint.proof hBase) (IntNumRatSection.proof hCut)

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

theorem agree_of_existsUnique (hN : Statement.{u}) (hU : ExistsUniqueStatement F ι)
    (I : IFamily F ι) (hI : IsFieldIntersection I) (V : Ideal (MRingOver F ι)) (n : ℕ)
    (L : Fin n → K → ℤ) (hV : IsProjVarF V n) : I V n L = intNum F V L := by
  obtain ⟨I₀, -, h₀⟩ := hU
  exact (h₀ I hI V n L hV).trans (h₀ _ (hN F K ι) V n L hV).symm

theorem existsUnique_iff (hN : Statement.{u}) :
    ExistsUniqueStatement F ι ↔ ∀ I : IFamily F ι, IsFieldIntersection I →
      ∀ (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ), IsProjVarF V n →
        I V n L = intNum F V L :=
  ⟨fun hU I hI V n L hV => agree_of_existsUnique hN hU I hI V n L hV,
    fun h => ⟨fun V _ L => intNum F V L, hN F K ι, h⟩⟩

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem ringKrullDim_eq_of_relDim (V : Ideal (MRing ι F)) (n : ℕ)
    (h : FieldNumbers.relDim V = (n : WithBot (WithTop ℤ))) :
    ringKrullDim (MRing ι F ⧸ V) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  unfold FieldNumbers.relDim at h
  generalize ringKrullDim (MRing ι F ⧸ V) = d at h ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have h₁ : ((⊤ : WithTop ℤ) : WithBot (WithTop ℤ)) = (n : WithBot (WithTop ℤ)) := h
      have h' : (⊤ : WithTop ℤ) = (n : WithTop ℤ) := by exact_mod_cast h₁
      exact absurd h' (WithTop.top_ne_coe)
    | coe m =>
      have h₁ : ((((m : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) =
          (n : WithBot (WithTop ℤ)) := h
      have h' : (m : ℤ) - Fintype.card K = n := by exact_mod_cast h₁
      have hm : m = n + Fintype.card K := by omega
      rw [hm]
      rfl

theorem finsum_mul_eq_sum {α : Type*} (D : α →₀ ℤ) (J : α → ℤ) :
    ∑ᶠ W, D W * J W = D.sum fun W m => m * J W := by
  classical
  rw [Finsupp.sum, finsum_eq_sum_of_support_subset]
  intro W hW
  rw [Function.mem_support] at hW
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  exact hW (by rw [h0, zero_mul])

theorem isIntersectionTheory (hPt : IntNumPoint.Statement.{u})
    (hBase : FieldNumbers.IntNumBase.Statement.{u}) {I : IFamily F ι}
    (hI : IsFieldIntersection I) : FieldNumbers.IsIntersectionTheory F I where
  base P hP h0 := by
    have hdim := ringKrullDim_eq_of_relDim P 0 (by rw [h0]; rfl)
    choose i hi using hP.relevant
    rw [hI.1 P ![] i ⟨(Objects.isMultiProjPrime_iff P).mp hP, hdim⟩ hi,
      ← hPt F K ι P i hP hdim hi]
    obtain ⟨-, h2⟩ := hBase F K ι P hP h0
    rw [h2, FieldNumbers.resDeg, dif_pos hP.isPrime]
  cut P n hP hdim bf bg f g hf hg hfP hgP bs := by
    have hd := ringKrullDim_eq_of_relDim P (n + 1) hdim
    have hs : IsRatSection P (fun k => (bf k : ℤ) - bg k) f g :=
      ⟨bf, bg, (Objects.isMultiHomog_iff f bf).mp hf, (Objects.isMultiHomog_iff g bg).mp hg,
        hfP, hgP, fun k => rfl⟩
    rw [hI.2 P n bs _ f g ⟨(Objects.isMultiProjPrime_iff P).mp hP, hd⟩ hs]
    have hD : ∀ W, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv P f g W = ratDiv P f g W := by
      intro W
      simp only [ratDiv, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply]
      rw [VocabDivCycle.proof F K ι P f W, VocabDivCycle.proof F K ι P g W]
    simp only [cycEval, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval, ← hD]
    exact (finsum_mul_eq_sum _ _).symm

theorem agree (hUq : FieldNumbers.IntNumUnique.Statement.{u}) (hPt : IntNumPoint.Statement.{u})
    (hBase : FieldNumbers.IntNumBase.Statement.{u}) (I : IFamily F ι)
    (hI : IsFieldIntersection I) (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ)
    (hV : IsProjVarF V n) : I V n L = intNum F V L :=
  hUq F K ι I (isIntersectionTheory hPt hBase hI) V ((Objects.isMultiProjPrime_iff V).mpr hV.1) n
    (relDim_eq_of_ringKrullDim V n hV.2) L

theorem existsUnique (hN : Statement.{u}) (hUq : FieldNumbers.IntNumUnique.Statement.{u})
    (hPt : IntNumPoint.Statement.{u}) (hBase : FieldNumbers.IntNumBase.Statement.{u}) :
    ExistsUniqueStatement F ι :=
  (existsUnique_iff hN).mpr (agree hUq hPt hBase)

theorem agree_of (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) (hEx : FieldNumbers.ExistsForm.Statement.{u})
    (hDiv : FieldNumbers.DivCycleSupport.Statement.{u}) (I : IFamily F ι)
    (hI : IsFieldIntersection I) (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ)
    (hV : IsProjVarF V n) : I V n L = intNum F V L :=
  agree (FieldNumbers.IntNumUnique.proof hCut hBase hEx hDiv) (IntNumPoint.proof hBase) hBase I hI
    V n L hV

end Numbers

end

end GroundTheory.Heights₂.Heights.NumbersDVR

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.MemOfMemSupportDivCycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsComponentDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByFormField
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialQuotDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealCorresp
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealMultiHomog
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumSymm
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PExistsForm
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivCycleSupport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace VerticalDivisorsCommuting

def CartierStatement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (n : ℕ) (b b' : K → ℤ) (f g f' g' : MRing ι O)
      (L : Fin n → K → ℤ) (Iκ : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily (IsLocalRing.ResidueField O) ι),
      IndefiniteRowSideFullHecke.NumbersDVR.IsModelOver P (n + 1) → IsVerticalDivisor P ϖ b f g →
      IsVerticalDivisor P ϖ b' f' g' → ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection Iκ →
      IndefiniteRowSideFullHecke.NumbersDVR.redEval (fun G => Iκ G (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b'))
                                (IndefiniteRowSideFullHecke.NumbersDVR.divO P f g) =
        IndefiniteRowSideFullHecke.NumbersDVR.redEval (fun G => Iκ G (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b))
          (IndefiniteRowSideFullHecke.NumbersDVR.divO P f' g')

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem intNum_snoc {F : Type u} [Field F] (V : Ideal (MRing ι F)) {n : ℕ} (L : Fin n → K → ℤ)
    (b : K → ℤ) :
    intNum F V (Fin.snoc (α := fun _ => K → ℤ) L b) = intNum F V (Matrix.vecCons b L) := by
  rw [← CutByFormField.vecCons_comp_finRotate]
  exact FieldNumbers.IntNumSymm.proof F K ι V (n + 1) _ _

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem vNum_snoc (W : Ideal (MRing ι O)) {n : ℕ} (L : Fin n → K → ℤ) (b : K → ℤ) :
    vNum W (Fin.snoc (α := fun _ => K → ℤ) L b) = vNum W (Matrix.vecCons b L) :=
  intNum_snoc _ L b

theorem redEval_divO (J : Ideal (MRing ι (IsLocalRing.ResidueField O)) → ℤ)
    (P : Ideal (MRing ι O)) (f g : MRing ι O) :
    IndefiniteRowSideFullHecke.NumbersDVR.redEval J (IndefiniteRowSideFullHecke.NumbersDVR.divO P f g) =
      cycEval (fun W => J (specialIdeal W)) (ratDiv P f g) := by
  rw [Objects.redEval_eq_cycEval]
  congr 1
  funext W
  exact Objects.divO_eq_ratDiv P f g W

theorem isProjVarF_specialIdeal (hDim : ComponentDim.Statement.{u}) {ϖ : O} (hϖ : Irreducible ϖ)
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {a : K → ℕ} {f : MRing ι O}
    (hf : IsMultiHomog f a) (hfP : f ∉ P) {W : Ideal (MRing ι O)} (hW : divCycle P f W ≠ 0)
    (hϖW : (C ϖ : MRing ι O) ∈ W) : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (specialIdeal W) d := by
  have hmin : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    exact hW (by unfold divCycle; rw [dif_neg h])
  have hWp : W.IsPrime := hmin.1.1.1
  have hWh : IsMultiHomogIdeal W :=
    (Objects.isMultiHomogIdeal_iff W).mpr
      (ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes
        ((Objects.isMultiHomogIdeal_iff P).mp hP.multiProj.multiHomog)
        ((Objects.isMultiHomog_iff f a).mp hf) hmin.1)
  obtain ⟨hpr, -, hrel, -⟩ := SpecialIdealCorresp.proof O ϖ hϖ K ι P W hWp hϖW
  refine ⟨(Objects.isMultiProjPrime_iff _).mp
    ⟨hpr, SpecialIdealMultiHomog.proof O K ι W hWh, hrel.mp hmin.2⟩, ?_⟩
  have := SpecialQuotDim.proof O ϖ hϖ K ι W hϖW
  rw [hDim O ϖ hϖ K ι P d hP a f hf hfP W hW hϖW] at this
  exact this

theorem cycEval_family (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) (hDim : ComponentDim.Statement.{u}) {ϖ : O}
    (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)} {n : ℕ} (hP : IsModelOver P (n + 1)) {b : K → ℤ}
    {f g : MRing ι O} (hD : IsVerticalDivisor P ϖ b f g)
    (Iκ : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily (IsLocalRing.ResidueField O) ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection Iκ) (M : Fin (n + 1) → K → ℤ) :
    cycEval (fun W => Iκ (specialIdeal W) (n + 1) M) (ratDiv P f g) =
      cycEval (fun W => vNum W M) (ratDiv P f g) := by
  unfold cycEval
  refine finsum_congr fun W => ?_
  by_cases h0 : ratDiv P f g W = 0
  · rw [h0, zero_mul, zero_mul]
  · have hϖW := hD.vertical W h0
    obtain ⟨α, β, hα, hβ, -⟩ := hD.degrees
    have hV : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (specialIdeal W) (n + 1) := by
      by_cases hf : divCycle P f W = 0
      · have hg : divCycle P g W ≠ 0 := fun hg => h0 (by rw [ratDiv, hf, hg, sub_zero])
        exact isProjVarF_specialIdeal hDim hϖ hP hβ hD.den_not_mem hg hϖW
      · exact isProjVarF_specialIdeal hDim hϖ hP hα hD.num_not_mem hf hϖW
    dsimp only
    rw [Numbers.agree_of hBase hCut FieldNumbers.ExistsForm.proof FieldNumbers.DivCycleSupport.proof
      Iκ hI (specialIdeal W) (n + 1) M hV]
    rfl

end VerticalDivisorsCommuting

theorem VerticalDivisorsCommuting.cartier_imp (hN : Numbers.Statement.{u}) :
    VerticalDivisorsCommuting.CartierStatement.{u} → VerticalDivisorsCommute.Statement.{u} := by
  intro H O _ _ _ ϖ hϖ K _ _ ι _ P d hP b b' f g f' g' hD hD' L
  have h := H O ϖ hϖ K ι P d b b' f g f' g' L (fun V _ M => intNum _ V M)
    ((Objects.isModelOver_iff P _).mp hP) hD hD' (hN _ K ι)
  simp only [VerticalDivisorsCommuting.redEval_divO, VerticalDivisorsCommuting.intNum_snoc] at h
  exact h

theorem VerticalDivisorsCommuting.imp_cartier (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) (hDim : ComponentDim.Statement.{u}) :
    VerticalDivisorsCommute.Statement.{u} → VerticalDivisorsCommuting.CartierStatement.{u} := by
  intro H O _ _ _ ϖ hϖ K _ _ ι _ P n b b' f g f' g' L Iκ hP hD hD' hI
  have hP' := (Objects.isModelOver_iff P _).mpr hP
  rw [VerticalDivisorsCommuting.redEval_divO, VerticalDivisorsCommuting.redEval_divO,
    VerticalDivisorsCommuting.cycEval_family hBase hCut hDim hϖ hP' hD Iκ hI (Fin.snoc (α := fun _ => K → ℤ) L b'),
    VerticalDivisorsCommuting.cycEval_family hBase hCut hDim hϖ hP' hD' Iκ hI (Fin.snoc (α := fun _ => K → ℤ) L b)]
  simp only [VerticalDivisorsCommuting.vNum_snoc]
  exact H O ϖ hϖ K ι P n hP' b b' f g f' g' hD hD' L

theorem VerticalDivisorsCommuting.equiv (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) (hDim : ComponentDim.Statement.{u}) :
    VerticalDivisorsCommute.Statement.{u} ↔ VerticalDivisorsCommuting.CartierStatement.{u} :=
  ⟨VerticalDivisorsCommuting.imp_cartier hBase hCut hDim, VerticalDivisorsCommuting.cartier_imp (Numbers.proof hBase hCut)⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR

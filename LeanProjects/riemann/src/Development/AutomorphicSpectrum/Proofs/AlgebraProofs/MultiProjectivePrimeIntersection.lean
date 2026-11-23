import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutContraction
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Num.Contract

noncomputable section

theorem rename_liftVar_mem_pointIdeal {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
    {K K' : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {ι' : K' → Type}
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) {f : MRing ι R} (hf : f ∈ pointIdeal R x) :
    rename (liftVar ι') f ∈ pointIdeal R (joinCoord x z) := by
  have key : ((rename (Sum.inl : K → K ⊕ K') : MvPolynomial K Ω →ₐ[Ω] _).restrictScalars R).comp
      (pointConeMap R x) =
      (pointConeMap R (joinCoord x z)).comp (rename (liftVar ι')) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap, liftVar, joinCoord]
  have hf0 : pointConeMap R x f = 0 := hf
  have h := congrArg (fun φ => φ f) key
  simp only [AlgHom.comp_apply, hf0, map_zero] at h
  exact h.symm

theorem lowered_lt {a : WithBot ℕ∞} {c d n : ℕ} (h : a < ((d + 1 + c : ℕ) : WithBot ℕ∞)) (hn : d < n) :
    WithBot.map (fun e : ℕ∞ => WithTop.map (fun m : ℕ => (m : ℤ) - c) e) a <
      ((n : ℕ) : WithBot (WithTop ℤ)) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) < (((d + 1 + c : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      exact absurd (WithBot.coe_lt_coe.mp h') (by simp)
    | coe m =>
      have h' : (((m : ℕ) : ℕ∞) : WithBot ℕ∞) < (((d + 1 + c : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      have hm : m < d + 1 + c := by exact_mod_cast WithBot.coe_lt_coe.mp h'
      show ((((m : ℤ) - c : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) <
        (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by omega))

theorem dim_quot_le {A : Type*} [CommRing A] {I J : Ideal A} (h : I ≤ J) :
    ringKrullDim (A ⧸ J) ≤ ringKrullDim (A ⧸ I) :=
  ringKrullDim_le_of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem vNumL_eq_zero_of_dim_le {ϖ : O} (hϖ : Irreducible ϖ)
    {K' : Type} [Fintype K'] [DecidableEq K'] {ι' : K' → Type} [∀ o, Fintype (ι' o)]
    {W : Ideal (MRing ι' O)} (hW : IsMultiProjPrime W) (hϖW : (C ϖ : MRing ι' O) ∈ W)
    {K : Type} [Fintype K] [DecidableEq K] (j : K ↪ K') {n : ℕ}
    (hdim : ringKrullDim (MRing ι' O ⧸ W) ≤ ((n + Fintype.card K' : ℕ) : WithBot ℕ∞))
    (hcon : GroundTheory.Heights₂.Heights.FieldNumbers.relDim
      (GroundTheory.Heights₂.Heights.FieldNumbers.contractPrime j (specialIdeal W)) <
        ((n : ℕ) : WithBot (WithTop ℤ)))
    (l : List (K' → ℤ)) (hl : l.length = n) (hlj : ∀ b ∈ l, ∀ o, o ∉ Set.range j → b o = 0) :
    vNumL W l = 0 := by
  subst hl
  obtain ⟨hQp, -, hrelIff, -⟩ :=
    SpecialIdealCorresp.full O ϖ hϖ K' ι' ⊥ W hW.isPrime hϖW
  have hQm := SpecialIdealMultiHomog.full O K' ι' W hW.multiHomog
  have hdimQ := SpecialQuotDim.full O ϖ hϖ K' ι' W hϖW
  change intNum (IsLocalRing.ResidueField O) (specialIdeal W) l.get = 0
  by_cases hcase : ringKrullDim (MRing ι' (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
      ((l.length + Fintype.card K' : ℕ) : WithBot ℕ∞)
  · exact IntNumVanish.full (IsLocalRing.ResidueField O) K' ι' l.length (specialIdeal W) hQp hQm
      (Or.inr hcase) l.get
  · have hdimEq : ringKrullDim (MRing ι' (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
        ((l.length + Fintype.card K' : ℕ) : WithBot ℕ∞) :=
      le_antisymm (hdimQ ▸ hdim) (not_lt.mp hcase)
    have hrelQ : GroundTheory.Heights₂.Heights.FieldNumbers.relDim (specialIdeal W) =
        ((l.length : ℕ) : WithBot (WithTop ℤ)) := by
      rw [GroundTheory.Heights₂.Heights.FieldNumbers.relDim, hdimEq]
      have : (((l.length + Fintype.card K' : ℕ) : ℤ) - Fintype.card K') = l.length := by
        push_cast; ring
      exact congrArg (fun z : ℤ => ((z : WithTop ℤ) : WithBot (WithTop ℤ))) this
    have hz := GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaContracted.full
      (IsLocalRing.ResidueField O) K K' j ι' (specialIdeal W)
      ⟨hQp, hQm, hrelIff.mp hW.relevant⟩ l.length hrelQ hcon (fun i => l.get i ∘ j)
    rw [← hz]
    congr 1
    funext i
    exact (SegreFlagCutContraction.pullDeg_comp_of_eq_zero j _
      (hlj _ (List.get_mem l i))).symm

theorem specialIdeal_le_contract {Ω : Type} [Field Ω] [Algebra O Ω]
    {K K' : Type} [Fintype K] [DecidableEq K] [DecidableEq K'] {ι : K → Type} [∀ k, Fintype (ι k)]
    {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    {W : Ideal (MRing (Sum.elim ι ι') O)} (hW : pointIdeal O (joinCoord x z) ≤ W) :
    specialIdeal (pointIdeal O x) ≤
      (GroundTheory.Heights₂.Heights.FieldNumbers.contractPrime (Function.Embedding.inl : K ↪ K ⊕ K')
        (specialIdeal W) : Ideal (MRing ι (IsLocalRing.ResidueField O))) := by
  refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
  show rename (liftVar ι') (MvPolynomial.map (IsLocalRing.residue O) f) ∈ specialIdeal W
  rw [← MvPolynomial.map_rename]
  exact Ideal.mem_map_of_mem _ (hW (rename_liftVar_mem_pointIdeal x z hf))

theorem relDim_contract_lt {Ω : Type} [Field Ω] [Algebra O Ω] {ϖ : O} (hϖ : Irreducible ϖ)
    {K K' : Type} [Fintype K] [DecidableEq K] [DecidableEq K'] {ι : K → Type} [∀ k, Fintype (ι k)]
    {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) {d n : ℕ} (hdn : d < n)
    (hV : IsModelOver (pointIdeal O x) d)
    {W : Ideal (MRing (Sum.elim ι ι') O)} (hW : pointIdeal O (joinCoord x z) ≤ W) :
    GroundTheory.Heights₂.Heights.FieldNumbers.relDim
      (GroundTheory.Heights₂.Heights.FieldNumbers.contractPrime (Function.Embedding.inl : K ↪ K ⊕ K')
        (specialIdeal W)) < ((n : ℕ) : WithBot (WithTop ℤ)) := by
  have hb := SpecialDimBound.full O ϖ hϖ K ι (pointIdeal O x) d hV
  exact lowered_lt (lt_of_le_of_lt (dim_quot_le (specialIdeal_le_contract x z hW)) hb) hdn

end

end GlobalTheory.CompanionTheory.Ar.Num.Contract

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem vNumL_pull_eq_zero_of_contracted : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d r : ℕ, 0 < r → IsModelOver (pointIdeal O x) d → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (W : Ideal (MRing (Sum.elim ι ι') O)), IsMultiProjPrime W → pointIdeal O (joinCoord x z) ≤ W → (C ϖ : MRing (Sum.elim ι ι') O) ∈ W → ∀ l : List (K → ℤ), l.length = d + r → ringKrullDim (MRing (Sum.elim ι ι') O ⧸ W) ≤ ((d + r + Fintype.card (K ⊕ K') : ℕ) : WithBot ℕ∞) → vNumL W (l.map (pullDeg (K' := K'))) = 0 := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d r hr hV K' _ _ ι' _ z W hW hPW hϖW l hl hdim
  refine Contract.vNumL_eq_zero_of_dim_le hϖ hW hϖW (Function.Embedding.inl : K ↪ K ⊕ K')
    (n := d + r) hdim (Contract.relDim_contract_lt hϖ x z (by omega) hV hPW)
    (l.map (pullDeg (K' := K'))) (by simpa using hl) ?_
  intro b hb o ho
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hb
  cases o with
  | inl k => exact absurd ⟨k, rfl⟩ ho
  | inr k => rfl

end GlobalTheory.CompanionTheory.Ar.Num

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedComplementDimBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMaximalLePrimeAddDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalHeightSuccDimStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.CodimOneDim

theorem le_of_add (D : ℕ) (a : ℕ∞) (r : WithBot ℕ∞) (ha : a = 1)
    (h : (((D + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (a : WithBot ℕ∞) + r) : (D : WithBot ℕ∞) ≤ r := by
  subst ha
  induction r using WithBot.recBotCoe with
  | bot => simp at h
  | coe r =>
    induction r using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.2 le_top
    | coe r =>
      have : D + 1 ≤ 1 + r := by exact_mod_cast h
      exact_mod_cast (show D ≤ r by omega)

theorem topologicalKrullDim_eq_of_coheight_eq_one : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z],
    Order.coheight (i (genericPoint Z)) = 1 → topologicalKrullDim Z = D := by
  intro k _ Y p D h Z i _ _ hz
  have := h.isDomain
  have := h.finite
  have := h.charZero_base
  have := h.isIntegral
  obtain ⟨d, hd⟩ := h.exists_dim_eq i
  rw [hd]

  have hup : topologicalKrullDim Z + 1 ≤ topologicalKrullDim Y :=
    GlobalTheory.DimCodim.dim_add_le_of_le_coheight (S := Y) (W := Z) i.continuous
      i.isClosedEmbedding.injective 1 fun w => by
        rw [← hz]
        exact Order.coheight_anti (genericPoint_specializes w |>.map i.continuous)
  rw [hd, h.dim_eq] at hup
  have hdD : d ≤ D := by
    have : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((D + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hup
    have : d + 1 ≤ D + 1 := by exact_mod_cast this
    omega
  obtain ⟨A, _, _, j, _, q, hq, hj⟩ := exists_affine_chart_over p (i (genericPoint Z))
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨q⟩
  obtain ⟨_, _, _⟩ := RegGenSmooth.chart_props h j hj
  have : Algebra.FiniteType ℤ A := Algebra.FiniteType.trans (S := k) inferInstance inferInstance
  have hst : ringKrullDim (Y.presheaf.stalk (j q)) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hq, hz]; rfl
  let x : Spec (.of A) := q
  have : IsIso (j.stalkMap x) := inferInstance
  have e := (asIso (j.stalkMap x) ≪≫ Spec.stalkIso (.of A) x).commRingCatIsoToRingEquiv
  have hq1 : (q.asIdeal.height : WithBot ℕ∞) = 1 := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (Localization.AtPrime q.asIdeal),
      ← ringKrullDim_eq_of_ringEquiv e, hst]
  obtain ⟨_, hKA⟩ := RegGenSmooth.ringKrullDim_chart h
    (IsPullback.of_hasPullback p (spMap (algebraMap k (FractionRing k)))) j hj
  obtain ⟨M, _, hM⟩ := GlobalTheory.T.exists_maximal_height_succ_dim k A D hKA
  have h2 := GlobalTheory.T.height_maximal_le_prime_add_dim A q.asIdeal M
  have hM' : (((D + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤
      (q.asIdeal.height : WithBot ℕ∞) + ringKrullDim (A ⧸ q.asIdeal) :=
    (WithBot.coe_le_coe.2 hM).trans h2
  have hq1' : q.asIdeal.height = 1 := by exact_mod_cast hq1
  have hDq := le_of_add D _ _ hq1' hM'
  have hsub : (Set.range j ∩ closure {j q} : Set Y) ⊆ Set.range i := fun y hy =>
    closure_minimal (s := {j q}) (Set.singleton_subset_iff.2 (⟨genericPoint Z, hq.symm⟩ : j q ∈ Set.range i))
      i.isClosedEmbedding.isClosed_range hy.2
  have e₁ := topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding
    (rfl : Set.range i = Set.range i)
  have h3 : topologicalKrullDim (Set.range j ∩ closure {j q} : Set Y) ≤ topologicalKrullDim Z := by
    rw [← e₁]
    exact (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
  rw [topologicalKrullDim_range_inter_closure_eq j q, hd] at h3
  have h4 : (D : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := hDq.trans h3
  have h5 : D ≤ d := by exact_mod_cast h4
  rw [show d = D by omega]
end GlobalTheory.CodimOneDim

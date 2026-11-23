import Mathlib
import GroundTheory.GlobalFields.TateThesis.RayClassDensity
import GroundTheory.GlobalFields.GlobalReciprocity.General
import GroundTheory.GlobalFields.GlobalReciprocity.Frobenius
import GroundTheory.GlobalFields.NormResidueSymbol.Surjective
import GroundTheory.GlobalFields.KummerTheory.Splitting

open NumberField IsDedekindDomain Topology Filter Set GroundTheory.LocalField

open scoped WithZero

namespace GroundTheory.Global

open IdeleGroup SemiLocal ValuativeRel

noncomputable section

universe u

section Uniformizer

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem ord_eq_one_of_valued_eq_exp {π : v.adicCompletion K}
    (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) : ord π = 1 := by
  have hle : π ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  let x : v.adicCompletionIntegers K := ⟨π, hle⟩
  have hU : Valuation.IsUniformizer (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (x : v.adicCompletion K) := by
    rw [Valuation.IsUniformizer.iff,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (valued_adicCompletion_surjective v)]
    exact hπ
  have hx : Irreducible x :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer x).2
      (Valuation.IsUniformizer.is_generator (π := x) hU)
  let e : v.adicCompletionIntegers K ≃* 𝒪[v.adicCompletion K] :=
    { toFun := fun a ↦ ⟨a, (mem_valuationInteger_iff v _).2 a.2⟩
      invFun := fun a ↦ ⟨a, (mem_valuationInteger_iff v _).1 a.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  exact ord_uniformizer (hx.map e)

end Uniformizer

section Ramified

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem finite_setOf_exists_ramificationIdx_ne_one :
    {v : HeightOneSpectrum (𝓞 K) | ∃ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal ∧
      w.asIdeal.ramificationIdx (𝓞 K) ≠ 1}.Finite := by
  refine ((finite_setOf_ramificationIdx_ne_one K L).image (HeightOneSpectrum.under (𝓞 K))).subset ?_
  rintro v ⟨w, hw, he⟩
  refine ⟨w, he, HeightOneSpectrum.ext ?_⟩
  rw [HeightOneSpectrum.under_asIdeal]
  exact hw.over.symm

end Ramified

section Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative Gal(L/K)]

attribute [local instance] galCommGroup

theorem arithFrobAt_eq_of_liesOver {v : HeightOneSpectrum (𝓞 K)} (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal] :
    arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal = arithFrobAt (𝓞 K) Gal(L/K) w'.asIdeal :=
  isConj_iff_eq.1 (isConj_arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal w'.asIdeal
    ((Ideal.LiesOver.over (P := w.asIdeal) (p := v.asIdeal)).symm.trans
      (Ideal.LiesOver.over (P := w'.asIdeal) (p := v.asIdeal))))

end Chebotarev

section ChebotarevDensity

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative Gal(L/K)]

attribute [local instance] galCommGroup

theorem hasDirichletDensity_setOf_arithFrobAt_eq (σ : Gal(L/K)) :
    {v : HeightOneSpectrum (𝓞 K) | ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
      w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal = σ}.HasDirichletDensity
      (1 / Nat.card Gal(L/K)) := by
  have hS := hasDirichletDensity_setOf_map_eq (ideleSymbol K L) (isOpen_ker_ideleSymbol L)
    diagonal_range_le_ker_ideleSymbol ideleSymbol_surjective σ
  set S := {v : HeightOneSpectrum (𝓞 K) | ∀ π : (v.adicCompletion K)ˣ,
      Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) →
        ideleSymbol K L (finiteEmbedding v π) = σ} with hSdef
  set R := {v : HeightOneSpectrum (𝓞 K) | ∃ w : HeightOneSpectrum (𝓞 L),
    w.asIdeal.LiesOver v.asIdeal ∧ w.asIdeal.ramificationIdx (𝓞 K) ≠ 1} with hRdef
  have hR : R.Finite := finite_setOf_exists_ramificationIdx_ne_one K L
  set T := {v : HeightOneSpectrum (𝓞 K) | ∀ w : HeightOneSpectrum (𝓞 L),
    w.asIdeal.LiesOver v.asIdeal →
      w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal = σ} with hTdef
  have h1 : S \ R ⊆ T := by
    rintro v ⟨hvS, hvR⟩ w hw
    have he : w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
      by_contra h
      exact hvR ⟨w, hw, h⟩
    obtain ⟨π, hπ⟩ := exists_uniformizer v
    refine ⟨he, ?_⟩
    rw [← hvS π hπ]
    exact (ideleSymbol_finiteEmbedding_eq_arithFrobAt v w he (ord_eq_one_of_valued_eq_exp v hπ)).symm
  have h2 : T ⊆ S := by
    intro v hv π hπ
    obtain ⟨⟨w, hw⟩⟩ := nonempty_placesOver L v
    obtain ⟨he, hσ⟩ := hv w hw
    rw [← hσ]
    exact ideleSymbol_finiteEmbedding_eq_arithFrobAt v w he (ord_eq_one_of_valued_eq_exp v hπ)
  have hSR : (S \ R).HasDirichletDensity (1 / Nat.card Gal(L/K)) :=
    (hasDirichletDensity_iff_of_subset_of_isBoundedUnder sdiff_subset
      (isBoundedUnder_primeIdealZetaSum_of_finite (hR.subset fun v hv ↦ by
        by_contra h
        exact hv.2 ⟨hv.1, h⟩)) _).2 hS
  exact (hasDirichletDensity_iff_of_subset_of_isBoundedUnder h1
    (isBoundedUnder_primeIdealZetaSum_of_finite (hR.subset fun v hv ↦ by
      by_contra h
      exact hv.2 ⟨h2 hv.1, h⟩)) _).1 hSR

theorem hasDirichletDensity_setOf_arithFrobAt_eq_finrank (σ : Gal(L/K)) :
    {v : HeightOneSpectrum (𝓞 K) | ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
      w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal = σ}.HasDirichletDensity
      (1 / Module.finrank K L) := by
  rw [← IsGalois.card_aut_eq_finrank]
  exact hasDirichletDensity_setOf_arithFrobAt_eq σ

end ChebotarevDensity

end

end GroundTheory.Global

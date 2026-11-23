import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedClosureOfPointProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasurePullbackEqZeroOfLtDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralPullbackGenericallyFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TopSelfEqLengthOfSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericNeZeroEquidimensional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericPointNeZeroProjectiveSameDim
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.CycPush

theorem isProjOver_comp {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsProjOver p)
    (i : Z ⟶ X) [IsClosedImmersion i] : IsProjOver (i ≫ p) := by
  obtain ⟨N, j, hj, rfl⟩ := hp
  exact ⟨N, i ≫ j, inferInstance, by rw [Category.assoc]⟩

theorem pull_congr {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
    (A : MLine p σ) {a b : Y ⟶ X} (hab : a = b) (ha : a ≫ p = q) (hb : b ≫ p = q) :
    A.pull a ha = A.pull b hb := by
  subst hab; rfl

theorem dim_le_of_dominant : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → ∀ n : ℕ, topologicalKrullDim Y = n → ∃ m : ℕ, m ≤ n ∧ topologicalKrullDim X = m := by
  intro F _ W M _ _ p q hp hq f hπ hη n hM
  obtain ⟨N, i, hi, hcomp⟩ := hp
  obtain ⟨N', j, hj, hcomp'⟩ := hq
  haveI : IsProper (PSpace.str F N) := isProper_str F N
  haveI : IsProper (PSpace.str F N') := isProper_str F N'
  haveI : IsProper p := by rw [← hcomp]; infer_instance
  haveI : IsProper (f ≫ p) := by rw [hπ, ← hcomp']; infer_instance
  haveI : IsProper f := IsProper.of_comp f p
  have hf : LocallyOfFiniteType f := inferInstance
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint W)) isOpen_univ
  have hV : IsAffineOpen V := hV
  have hx : f (genericPoint M) ∈ V := hη ▸ hxV
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, hUV⟩ := M.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint M ∈ f ⁻¹ᵁ V from hx) (f ⁻¹ᵁ V).isOpen
  have hU : IsAffineOpen U := hU
  haveI : Nonempty V := ⟨⟨_, hx⟩⟩
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  have e : U ≤ f ⁻¹ᵁ V := hUV
  let φ := Spec.preimage (hV.fromSpec ≫ p)
  have hφ : Spec.map φ = hV.fromSpec ≫ p := Spec.map_preimage _
  letI : Algebra F Γ(W, V) := φ.hom.toAlgebra
  have hftA : Algebra.FiniteType F Γ(W, V) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  letI : Algebra Γ(W, V) Γ(M, U) := (f.appLE V U e).hom.toAlgebra
  have hftB : Algebra.FiniteType Γ(W, V) Γ(M, U) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f hf ⟨V, hV⟩ ⟨U, hU⟩ e
  letI : Algebra F Γ(M, U) := (φ ≫ f.appLE V U e).hom.toAlgebra
  haveI : IsScalarTower F Γ(W, V) Γ(M, U) := IsScalarTower.of_algebraMap_eq' rfl
  have hftC : Algebra.FiniteType F Γ(M, U) := Algebra.FiniteType.trans hftA hftB
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(W, V)
  have hd : topologicalKrullDim (V : Set W) = d := by
    rw [← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
      hV.range_fromSpec
  rw [GlobalTheory.OpenDim.topologicalKrullDim_open F p V ⟨_, hx⟩] at hd
  have hB : Algebra.trdeg F Γ(M, U) = n := GlobalTheory.GenFinite.trdeg_affineOpen_eq F (f ≫ p) hU ⟨_, hy⟩ n hM
  letI := (W.evaluation V _ hx).hom.toAlgebra
  have nat : f.appLE V U e ≫ M.evaluation U _ hy =
      W.evaluation V _ hx ≫ f.residueFieldMap (genericPoint M) := by
    rw [Scheme.evaluation_naturality f _ hx, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp only [Scheme.evaluation]
    rw [← Category.assoc, TopCat.Presheaf.germ_res]
  haveI := GenFiniteEtale.isFractionRing_eval W hV hη hx
  have hinj : Function.Injective (IsScalarTower.toAlgHom F Γ(W, V) Γ(M, U)) := by
    have h₃ : Function.Injective (f.appLE V U e ≫ M.evaluation U _ hy).hom := by
      rw [nat]
      exact (f.residueFieldMap (genericPoint M)).hom.injective.comp
        (IsFractionRing.injective Γ(W, V) (W.residueField (f (genericPoint M))))
    exact Function.Injective.of_comp (f := (M.evaluation U _ hy).hom) h₃
  have hle := trdeg_le_of_injective _ hinj
  rw [h₂, hB] at hle
  exact ⟨d, by exact_mod_cast hle, hd⟩

theorem cycInt_pull : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (e : ℕ) (L : Fin e → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → ∀ w : Y, topologicalKrullDim (closure ({w} : Set Y)) = e → (topologicalKrullDim (closure ({π w} : Set X)) = e → cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = π.residueDegree w * cycInt L f (π w)) ∧ (topologicalKrullDim (closure ({π w} : Set X)) ≠ e → cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = 0) := by
  intro F _ X Y p q σ hp hq π hπ e L f hf w hw
  obtain ⟨hIw, hgw, hdw, -⟩ := GlobalTheory.ClosFacts.clos_facts Y w
  obtain ⟨hIx, hgx, hdx, hfac⟩ := GlobalTheory.ClosFacts.clos_facts X (π w)
  have hη : (closι w ≫ π) (genericPoint (clos w)) = π w := by
    rw [Scheme.Hom.comp_apply, hgw]
  obtain ⟨g, hg, hgg, hgdeg, -⟩ := hfac (clos w) (closι w ≫ π) hη
  have hpX : IsProjOver (closι (π w) ≫ p) := isProjOver_comp hp _
  have hpY : IsProjOver (closι w ≫ q) := isProjOver_comp hq _
  have hgp : g ≫ closι (π w) ≫ p = closι w ≫ q := by
    rw [← Category.assoc, hg, Category.assoc, hπ]
  have hdY : topologicalKrullDim (clos w) = e := hdw.trans hw
  let L' : Fin e → MLine (closι (π w) ≫ p) σ := fun i => (L i).pull (closι (π w)) rfl
  let f' : CxPts (closι (π w) ≫ p) σ → ℝ := fun y => f (ptMap (closι (π w)) rfl σ y)
  have hf' : Measurable f' := hf.comp (PtsOver.continuous_map _ _ _).measurable

  have h1 : (closι w ≫ π) ≫ p = closι w ≫ q := by rw [Category.assoc, hπ]
  have h2 : (g ≫ closι (π w)) ≫ p = closι w ≫ q := by rw [Category.assoc, hgp]
  have hpart : ∀ ε : ℤˣ, part (fun i => ((L i).pull π hπ).pull (closι w) rfl) ε = part (fun i => (L' i).pull g hgp) ε := by
    intro ε
    have c1 := (GlobalTheory.Mix.isom_calculus F X Y p q σ π hπ).2.2.2.2.2 (clos w) (closι w ≫ q) (closι w) rfl h1
    have c2 := (GlobalTheory.Mix.isom_calculus F X (clos (π w)) p (closι (π w) ≫ p) σ (closι (π w)) rfl).2.2.2.2.2 (clos w)
      (closι w ≫ q) g hgp h2
    have e1 := GlobalTheory.Mix.part_eq_of_isom F (clos w) (closι w ≫ q) σ hpY e _ _ (fun i => c1 (L i)) ε
    have e2 := GlobalTheory.Mix.part_eq_of_isom F (clos w) (closι w ≫ q) σ hpY e _ _ (fun i => c2 (L i)) ε
    rw [e1, e2]
    congr 1
    funext i
    exact pull_congr _ hg.symm _ _
  have hfun : (fun y => (fun y => f (ptMap π hπ σ y)) (ptMap (closι w) rfl σ y)) = fun y => f' (ptMap g hgp σ y) := by
    funext y
    show f _ = f _
    congr 1
    apply Subtype.ext
    simp only [PtsOver.map_val, Category.assoc, hg]
  have hint : cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w =
      Mix.int (fun i => (L' i).pull g hgp) (fun y => f' (ptMap g hgp σ y)) := by
    simp only [cycInt, Mix.int]
    rw [hfun, hpart 1, hpart (-1)]
  refine ⟨fun hX => ?_, fun hX => ?_⟩
  · have hdX : topologicalKrullDim (clos (π w)) = e := hdx.trans hX
    have hne := GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint F (clos (π w)) (clos w)
      (closι (π w) ≫ p) (closι w ≫ q) e hpX hpY hdX hdY g hgp hgg
    have hpush := (GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) σ e hpX hdX hpY g hgp
      hgg hne L' f' hf').2
    have hdeg : g.residueDegree (genericPoint (clos w)) = π.residueDegree w := by
      rw [hgdeg, GlobalTheory.CurveDegreesCompare.residueDegree_comp, GlobalTheory.ProperCut.residueDegree_of_isClosedImmersion (closι w),
        mul_one, hgw]
    rw [hint, hpush, hdeg]
    rfl
  · obtain ⟨m, hm, hdX⟩ := dim_le_of_dominant F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) hpX hpY g hgp
      hgg e hdY
    have hlt : m < e := lt_of_le_of_ne hm fun h => hX (by rw [← hdx, hdX, h])
    have h0 := GlobalTheory.T.mixedChernMeasure_pullback_eq_zero_of_lt_dim F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) σ e m hlt hpX hdX hpY g hgp hgg L'
    rw [hint]
    simp only [Mix.int, h0, integral_zero_measure, sub_zero]

end GlobalTheory.CycPush

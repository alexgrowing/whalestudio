import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosurePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightEqOneIffClosureDimProjectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem finsum_weighted_regroup_along_fibres {A B : Type} (π : A → B) (m : A → ℤ) (n : B → ℤ) (d : A → ℕ) (g : A → ℝ) (h : B → ℝ)
    (P : B → Prop) (hm : (Function.support m).Finite) (hn : (Function.support n).Finite)
    (hP : ∀ z, n z ≠ 0 → P z) (hs : ∀ z, P z → ∑ᶠ (w : A) (_ : π w = z), m w * (d w : ℤ) = n z)
    (h₁ : ∀ w, m w ≠ 0 → P (π w) → g w = d w * h (π w)) (h₀ : ∀ w, m w ≠ 0 → ¬ P (π w) → g w = 0) :
    ∑ᶠ w, (m w : ℝ) * g w = ∑ᶠ z, (n z : ℝ) * h z := by
  classical
  set S := hm.toFinset with hS
  set T := hn.toFinset ∪ S.image π with hT
  have hmS : ∀ w, m w ≠ 0 ↔ w ∈ S := fun w => by simp [hS]
  rw [finsum_eq_sum_of_support_subset (s := S) _ (fun w hw => by
      have : m w ≠ 0 := fun h0 => hw (by simp [h0])
      exact Finset.mem_coe.2 ((hmS w).1 this)),
    finsum_eq_sum_of_support_subset (s := T) _ (fun z hz => by
      have : n z ≠ 0 := fun h0 => hz (by simp [h0])
      simp [hT, this]),
    ← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := π) (fun w hw => by
      simp only [hT, Finset.mem_union]; exact Or.inr (Finset.mem_image_of_mem _ hw))]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : P z
  · have e : ∑ᶠ (w : A) (_ : π w = z), m w * (d w : ℤ) = ∑ w ∈ S.filter (fun w => π w = z), m w * (d w : ℤ) := by
      refine finsum_mem_eq_sum_of_inter_support_eq (s := {w | π w = z}) _ ?_
      ext w
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, Finset.coe_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨(hmS w).1 (left_ne_zero_of_mul h2), h1⟩, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1.2, h2⟩
    rw [← hs z hz, e]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨hw', rfl⟩ := Finset.mem_filter.1 hw
    rw [h₁ w ((hmS w).2 hw') hz, mul_assoc]
  · have e : n z = 0 := by
      by_contra h'
      exact hz (hP z h')
    rw [e, Int.cast_zero, zero_mul]
    refine Finset.sum_eq_zero fun w hw => ?_
    obtain ⟨hw', rfl⟩ := Finset.mem_filter.1 hw
    rw [h₀ w ((hmS w).2 hw') hz, mul_zero]

theorem finsum_cycInt_push : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → IsProjOver q → topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ (Δ : CartierDiv X) (Δ' : CartierDiv Y), (∀ z : X, Order.coheight z = 1 → ∑ᶠ (w : Y) (_ : π w = z), Δ'.mult w * (π.residueDegree w : ℤ) = Δ.mult z) → ∀ (L : Fin e → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → ∑ᶠ w, (Δ'.mult w : ℝ) * cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L f z := by
  intro F _ X Y _ _ _ _ p q σ e hp hX hq hY π hπ _ Δ Δ' hΔ L f hf
  have hc : ∀ {Z : Scheme.{0}} {s : Z ⟶ Sp F}, IsProjOver s → CompactSpace Z := by
    rintro Z _ ⟨m, i, hi, rfl⟩
    have := isProper_str F m
    have : IsProper (i ≫ PSpace.str F m) := inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str F m)
  haveI := hc hp
  haveI := hc hq
  have key := fun (w : Y) (hw : Δ'.mult w ≠ 0) => GlobalTheory.T.mixedChernIntegral_pointClosure_pullback F X Y p q σ hp hq π hπ e L f hf w
    ((GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F Y q e hq hY w).1 (CartierDiv.coheight_eq_one_of_mult_ne_zero (D := Δ') hw))
  exact finsum_weighted_regroup_along_fibres π Δ'.mult Δ.mult (fun w => π.residueDegree w) _ _ (fun z => Order.coheight z = 1)
    Δ'.finite_support_mult Δ.finite_support_mult
    (fun z hz => CartierDiv.coheight_eq_one_of_mult_ne_zero (D := Δ) hz) hΔ
    (fun w hw h => (key w hw).1 ((GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hX _).1 h))
    (fun w hw h => (key w hw).2 fun h' => h ((GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hX _).2 h'))

end GlobalTheory.Mix

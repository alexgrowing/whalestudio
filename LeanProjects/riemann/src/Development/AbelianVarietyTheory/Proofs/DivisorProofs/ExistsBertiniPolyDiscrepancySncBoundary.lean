import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniCoordinateStrataEtaleChartCotangentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartSingleEquationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyEqFormOrderSubWeightedCoordOrdersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyLtAdaptedCoordsIndependentFunctionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Discrepancy

theorem exists_mvPolynomial_of_forall_nhds {X : Type} [TopologicalSpace X] [CompactSpace X]
    {ι : Type} (P : (ι → ℂ) → X → Prop)
    (h : ∀ x₀ : X, ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧ ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧
      ∀ c, MvPolynomial.eval c Q ≠ 0 → ∀ x ∈ W, P c x) :
    ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ c, MvPolynomial.eval c Q ≠ 0 → ∀ x, P c x := by
  classical
  choose W hW hxW Q hQ hP using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hW
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  refine ⟨∏ x ∈ t, Q x, Finset.prod_ne_zero_iff.2 fun x _ => hQ x, fun c hc y => ?_⟩
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  rw [map_prod] at hc
  exact hP x c (Finset.prod_ne_zero_iff.1 hc x hx) y hy

theorem exists_poly_neg_one_lt_discrep_member : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q → ∀ (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ (A : CartierDiv Y) (ι : Type) [Fintype ι] (s : ι → Y.functionField), (∀ i, s i ∈ A.sections) → ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ t : Y.functionFieldˣ, (t : Y.functionField) = ∑ i, Cartier.constFn q (u i) * s i → ∀ y : Y, (∃ i, A.GeneratesAt y (s i)) → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (c : ℚ) (g f : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → c < 1 → (∀ w, w ⤳ y → Θ.mult w < m) → (Θ + m • K).IsEqn y g → (GlobalTheory.Cartier.CartierDiv.principal t + A).IsEqn y f → ∀ E : DivOver q, E.Through y → -1 < discrep E η m g - c * E.ord f := by
  intro Y _ _ q n _ hproj B hB A ι _ s hs
  haveI : IsProper q := ((isProjOver_iff_isProper_and_exists_isAmpleLB q).1 hproj).1
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  refine (exists_mvPolynomial_of_forall_nhds (X := Y) (fun c y =>
    ∀ t : Y.functionFieldˣ, (t : Y.functionField) = ∑ i, Cartier.constFn q (c i) * s i →
    (∃ i, A.GeneratesAt y (s i)) → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (c' : ℚ)
      (g f : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → c' < 1 →
      (∀ w, w ⤳ y → Θ.mult w < m) → (Θ + m • K).IsEqn y g →
      (GlobalTheory.Cartier.CartierDiv.principal t + A).IsEqn y f → ∀ E : DivOver q, E.Through y →
      -1 < discrep E η m g - c' * E.ord f) fun y₀ => ?_).imp
    fun Q ⟨hQ, hQc⟩ => ⟨hQ, fun c hc t ht y => hQc c hc y t ht⟩
  obtain ⟨W, hW, z, w, u, e, f, hfr, he, hf, hch⟩ := GlobalTheory.T.exists_affine_snc_chart_cartier_single_equation Y q n B hB A ι s hs y₀
  obtain ⟨Q, hQ, hQc⟩ := GlobalTheory.T.bertini_coordinateStrata_etaleChart_cotangent Y q n W z hfr ι f
  refine ⟨W, W.isOpen, hW, Q, hQ, fun c hc y hy t ht hgen η K Θ m c' g f' hη hK hm hΘ hc' hmult
    hg hf' E hE => ?_⟩
  obtain ⟨J, hJ, hJz⟩ := hch y hy
  have hFv : fnOf W (gen_mem hy) (∑ i, algX q W (c i) * f i) = ((t * e : Y.functionFieldˣ) : Y.functionField) := by
    rw [Units.val_mul, ht, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hf i, ← RingHom.comp_apply, fnOf_comp_algX, mul_assoc]
  have hunit : UnitAt y ((f' : Y.functionField) / ((t * e : Y.functionFieldˣ) : Y.functionField)) :=
    ((CartierDiv.isEqn_principal t y).add (he y hy)).iff_unitAt.1 hf'
  have hbas : ∃ i, y ∈ Y.basicOpen (f i) := by
    obtain ⟨i, hi⟩ := hgen
    refine ⟨i, (unitAt_fnOf_iff hy (gen_mem hy) (f i)).1 ?_⟩
    rw [hf i]
    exact (he y hy).generatesAt_iff.1 hi
  rw [GlobalTheory.T.discrepancy_eq_formOrder_sub_weighted_coordOrders Y q n B y W hy z J w u hJ η K Θ m g hη hK hm hΘ hg E hE]
  exact GlobalTheory.T.discrepancy_lt_adaptedCoords_independent_function Y q n B y W hy z J w u hJ hJz _ (fun h => hQc c hc y hy hbas J h) (t * e) f'
    (fun j => (Θ.mult (w j) : ℚ) / m) c' hFv.symm hunit (fun j hj => by
      have := hmult (w j) (hJ.spec j hj)
      have hm' : (0 : ℚ) < m := by exact_mod_cast hm
      rw [div_lt_one hm']
      exact_mod_cast this) hc' E hE

end GlobalTheory.Discrepancy

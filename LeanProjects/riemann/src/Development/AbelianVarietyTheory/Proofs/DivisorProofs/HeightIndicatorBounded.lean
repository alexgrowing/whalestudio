import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedBasePt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootHeightLeAbelianHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearCombStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBoundedBelowOffZeroLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsNonvanishingClosedPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootCombinationRationalSectionUnitsStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts GlobalTheory.ShFam.Pad
open CategoryTheory AlgebraicGeometry GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.Cartier
open scoped Classical
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RefFlatHt

theorem exists_secs : ∀ (D : D7) (O : Setup D), O.Core → ∀ (c : O.s.Comp) (W : O.LatModel ∅ c) (τ : D.what₂.Tau), ∃ (s : (GlobalTheory.ArInt.comb (fun i : Fin O.N => W.root ∅ (τ, i)) (fun _ => 1)).B.Sec) (s' : (GlobalTheory.ArInt.comb (fun i : Fin O.N => W.root ∅ (τ, i)) (fun _ => 1)).dual.B.Sec), ∀ w : W.V.G, IsClosed ({w} : Set W.V.G) → W.V.j w ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ∧ W.V.j w ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s' := by
  intro D O hC c W τ
  obtain ⟨r, hr, hu⟩ := GlobalTheory.T.root_combination_rational_section_units D O hC c W τ
  exact GlobalTheory.T.exists_sections_nonvanishing_closed_points W.V _ r hr hu

theorem ptHt_comb (hE : GlobalTheory.Published.ArExists) {D : D7} (O : Setup D) (hC : O.Core) (c : O.s.Comp) (W : O.LatModel ∅ c)
    (τ : D.what₂.Tau) (w : W.V.G) (hw : IsClosed ({w} : Set W.V.G)) :
    IsAlgPt (W.V.j w) ∧
      IsPtHt (GlobalTheory.ArInt.comb (fun i : Fin O.N => W.root ∅ (τ, i)) (fun _ => 1)) (W.V.j w)
        (∑ i : Fin O.N, (O.root0 c ∅ (τ, i)).ht (W.V.π w)) ∧
      IsPtHt (GlobalTheory.ArInt.comb (fun i : Fin O.N => W.root ∅ (τ, i)) (fun _ => 1)).dual (W.V.j w)
        (-∑ i : Fin O.N, (O.root0 c ∅ (τ, i)).ht (W.V.π w)) := by
  have hx : ∀ i : Fin O.N, IsAlgPt (W.V.j w) ∧
      IsPtHt (W.root ∅ (τ, i)) (W.V.j w) ((1 : ℕ) * (((O.root0 c ∅ (τ, i)).n : ℕ) : ℝ) * (O.root0 c ∅ (τ, i)).ht (W.V.π w)) :=
    fun i => GlobalTheory.Mean4O.CoverHt.main hE _ _ _ W.V _ _ 1 w hw
      (Setup.induces_root0 D O hC.dualRef ∅ c W ∅ subset_rfl (τ, i))
  have hn : ∀ i : Fin O.N, (((O.root0 c ∅ (τ, i)).n : ℕ) : ℝ) = 1 := fun i => by
    simp [Setup.root0, Setup.adl0, adlOf]
  have halg : IsAlgPt (W.V.j w) := (hx ⟨0, by have := O.S.two_le; omega⟩).1
  have hI := GlobalTheory.T.point_height_dual_and_linear_comb hE _ W.V.X W.V.p _ W.V.ar (W.V.j w) halg
  have hc := hI.2 (Fin O.N) (fun i => W.root ∅ (τ, i)) (fun i => (O.root0 c ∅ (τ, i)).ht (W.V.π w))
    (fun i => by simpa [hn i] using (hx i).2) (fun _ => 1)
  simp only [Int.cast_one, one_mul] at hc
  exact ⟨halg, hc, hI.1 _ _ hc⟩

theorem sum_ht_bdd (hE : GlobalTheory.Published.ArExists) {D : D7} (O : Setup D) (hC : O.Core) (c : O.s.Comp) (W : O.LatModel ∅ c)
    (τ : D.what₂.Tau) : ∃ C : ℝ, ∀ b : (O.var c).X, IsClosed ({b} : Set (O.var c).X) →
      |∑ i : Fin O.N, (O.root0 c ∅ (τ, i)).ht b| ≤ C := by
  obtain ⟨s, s', hs⟩ := exists_secs D O hC c W τ
  obtain ⟨c₁, h₁⟩ := GlobalTheory.T.height_bounded_below_off_zero_locus _ W.V.X W.V.p _ W.V.ar _ s
  obtain ⟨c₂, h₂⟩ := GlobalTheory.T.height_bounded_below_off_zero_locus _ W.V.X W.V.p _ W.V.ar _ s'
  refine ⟨|c₁| + |c₂|, fun b hb => ?_⟩
  obtain ⟨w, hw, rfl⟩ := GlobalTheory.RootHtBound.exists_closed_over W.V hb
  obtain ⟨halg, hp, hd⟩ := ptHt_comb hE O hC c W τ w hw
  have e₁ := h₁ _ (hs w hw).1 halg _ hp
  have e₂ := h₂ _ (hs w hw).2 halg _ hd
  rw [abs_le]
  constructor <;> linarith [le_abs_self c₁, le_abs_self c₂, neg_abs_le c₁, neg_abs_le c₂]

theorem height_indicator_eq_neg_root_heights {D : D7} {O : Setup D} {H : Ht O.Y} (hH : O.HtIs H) (τ : D.what₂.Tau) (y : Pt O.s) :
    H.h0 (fun τ' _ => if τ' = τ then 1 else 0) y =
      -∑ i : Fin O.N, (O.root0 (compPt O.s y) ∅ (τ, i)).ht (basePt O.Φ y) := by
  rw [hH.h0]
  unfold Setup.htWt
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem refHt : Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → OnObj fun D O _ _ H _ => ∃ C : ℝ, ∀ (τ : D.what₂.Tau) (y : Pt O.s), |H.h0 (fun τ' _ => if τ' = τ then 1 else 0) y| ≤ C := by
  intro p2 _ _ D O hC _ A T H h
  have hE : GlobalTheory.Published.ArExists := p2.p4.arExists
  choose C hC' using fun (c : O.s.Comp) (τ : D.what₂.Tau) => sum_ht_bdd hE O hC c (h.mdl ∅ c) τ
  refine ⟨∑ c, ∑ τ, |C c τ|, fun τ y => ?_⟩
  rw [height_indicator_eq_neg_root_heights h.ht τ y, abs_neg]
  refine (hC' _ τ _ (HtTieRead.isClosed_basePt O y)).trans ((le_abs_self _).trans ?_)
  refine (Finset.single_le_sum (f := fun τ' => |C (compPt O.s y) τ'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)).trans ?_
  exact Finset.single_le_sum (f := fun c => ∑ τ', |C c τ'|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.mem_univ (compPt O.s y))

end GlobalTheory.RefFlatHt

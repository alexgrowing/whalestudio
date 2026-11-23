import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootHeightLeAbelianHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedBasePt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearCombStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMetricFinitelyManyPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightDecompositionClosedPointStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorDetOmegaSymSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierRatioLocalNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierLogHeightFormulaStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped Classical
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.OmCmpProof

theorem ht_le_of_induces (hE : GlobalTheory.Published.ArExists) {D : D7} (O : Setup D) (hO : O.Core) (c : O.s.Comp)
    (W : O.LatModel ∅ c) (A : Adl (cxSt D.what₂.LL) (O.var c)) (L : GlobalTheory.HermLB W.V.p) (hA : ((A.n : ℕ) : ℝ) = 1)
    (hR : W.V.Induces A L 1) :
    ∃ C : ℝ, ∀ b : (O.var c).X, IsClosed ({b} : Set (O.var c).X) → |A.ht b| ≤ C * (|(O.met.ab c).ht b| + 1) := by
  obtain ⟨n₁, c₁, h₁⟩ := GlobalTheory.RootHtBound.dom hE W.V (O.met.ab c) W.amp W.k W.k_pos W.amp_spec (hO.ample_ab c) L
  obtain ⟨n₂, c₂, h₂⟩ := GlobalTheory.RootHtBound.dom hE W.V (O.met.ab c) W.amp W.k W.k_pos W.amp_spec (hO.ample_ab c) L.dual
  set K : ℝ := (W.k : ℝ) * (((O.met.ab c).n : ℕ) : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨((max n₁ n₂ : ℕ) : ℝ) * K + |c₁| + |c₂|, fun b hb => ?_⟩
  obtain ⟨w, hw, hwb⟩ := GlobalTheory.RootHtBound.exists_closed_over W.V hb
  have ha := (GlobalTheory.Mean4O.CoverHt.main hE _ _ _ W.V _ _ _ w hw W.amp_spec).2
  have hr := GlobalTheory.Mean4O.CoverHt.main hE _ _ _ W.V _ _ _ w hw hR
  have hd := (GlobalTheory.T.point_height_dual_and_linear_comb hE _ W.V.X W.V.p _ W.V.ar (W.V.j w) hr.1).1 _ _ hr.2
  have e₁ := h₁ w hw _ _ ha hr.2
  have e₂ := h₂ w hw _ _ ha hd
  rw [hwb] at e₁ e₂
  rw [hA] at e₁ e₂
  simp only [Nat.cast_one, one_mul] at e₁ e₂
  exact GlobalTheory.RootHtBound.abs_le_of_two n₁ n₂ c₁ c₂ K _ _ hK0 e₁ e₂

theorem line_ht_le (hE : GlobalTheory.Published.ArExists) {D : D7} (O : Setup D) (hO : O.Core) (c : O.s.Comp) (W : O.LatModel ∅ c)
    (k : Fin (D.R.f * O.N)) : ∃ C : ℝ, ∀ b : (O.var c).X, IsClosed ({b} : Set (O.var c).X) →
      |(O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)).ht b| ≤ C * (|(O.met.ab c).ht b| + 1) := by
  have hs : (letterOf O.S.Dw (Sum.inr (k : ℕ))).isSome := by
    rw [letterOf_whole O.S k]; rfl
  exact ht_le_of_induces hE O hO c W _ _ (by simp [Setup.adl0, adlOf]) (W.line_spec ∅ subset_rfl _ hs)

end GlobalTheory.OmCmpProof

namespace GlobalTheory.OmCmpProof

theorem isComb_det {D : D7} (O : Setup D) (hO : O.Core) (c : O.s.Comp) : IsComb (O.adl0 c (detOmSym D.host.E (D.R.f * O.N)))
    (fun k : Fin (D.R.f * O.N) => (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1))) (fun _ => -1) (fun _ _ => 0) := by
  refine ⟨1, fun _ => -1, one_pos, fun i => by simp [Setup.adl0, adlOf], by rw [one_smul]; exact GlobalTheory.T.divisor_det_omega_sym_sum D O c,
    fun σ z => ⟨hO.referenceMetric_posAt c σ _ z, ?_⟩, fun v e y => ?_⟩
  · have h := GlobalTheory.T.cartier_ratio_local_norm D O hO c σ z
    simp only [Nat.cast_one, one_mul, pow_one, mul_zero, sub_zero, Int.cast_neg, Int.cast_one, neg_one_mul,
      Finset.sum_neg_distrib]
    rw [h]; ring
  · have h := GlobalTheory.T.cartier_log_height_formula D O c v e y
    simp only [Nat.cast_one, one_mul, pow_one, Int.cast_neg, Int.cast_one, neg_one_mul, Finset.sum_neg_distrib]
    rw [h]; ring

theorem ht_det : ∀ (D : D7) (O : Setup D), O.Core → ∀ (c : O.s.Comp), O.LatModel ∅ c → ∀ b : (O.var c).X, IsClosed ({b} : Set (O.var c).X) → (O.adl0 c (detOmSym D.host.E (D.R.f * O.N))).ht b = -∑ k : Fin (D.R.f * O.N), (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)).ht b := by
  intro D O hO c W b hb
  have hs : ∀ k : Fin (D.R.f * O.N), (letterOf O.S.Dw (Sum.inr (k : ℕ))).isSome := fun k => by
    rw [letterOf_whole O.S k]; rfl
  have e := GlobalTheory.T.height_decomposition_closed_point _ _ _ _ _ _ _ _ (isComb_det O hO c)
    (fun k y => GlobalTheory.T.adelic_metric_finitely_many_places _ _ _ _ _ _ _ one_ne_zero (W.line_spec ∅ subset_rfl _ (hs k)) y) b hb
  rw [e]
  simp [finsum_zero]

end GlobalTheory.OmCmpProof

namespace GlobalTheory.OmCmpProof

theorem om_cmp : Hypotheses2 → HypothesesH → OmCmp := by
  intro hP _ D O hO _ A T H h
  have hE : GlobalTheory.Published.ArExists := hP.p4.arExists
  choose C hC using fun (c : O.s.Comp) (k : Fin (D.R.f * O.N)) => line_ht_le hE O hO c (h.mdl ∅ c) k
  refine ⟨∑ c, ∑ k, |C c k|, fun y => ?_⟩
  have hb := HtTieRead.isClosed_basePt O y
  show |(O.adl0 (compPt O.s y) (detOmSym D.host.E (D.R.f * O.N))).ht (basePt O.Φ y)| ≤ _
  rw [h.ht.hA y, GlobalTheory.OmCmpProof.ht_det D O hO _ (h.mdl ∅ _) _ hb, abs_neg]
  set X := |(O.met.ab (compPt O.s y)).ht (basePt O.Φ y)| + 1 with hX
  have hX0 : 0 ≤ X := by positivity
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ k : Fin (D.R.f * O.N), |(O.adl0 (compPt O.s y) (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)).ht (basePt O.Φ y)|
      ≤ |C (compPt O.s y) k| * X := fun k => (hC _ k _ hb).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hX0)
  refine (Finset.sum_le_sum fun k _ => h1 k).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ hX0
  exact Finset.single_le_sum (f := fun c => ∑ k, |C c k|) (fun c _ => Finset.sum_nonneg fun k _ => abs_nonneg _)
    (Finset.mem_univ (compPt O.s y))

end GlobalTheory.OmCmpProof

end

import Mathlib
import Formalism.LocalRingCardinality.DataErr
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.PeriodLowerBounds
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ColumnAvoidanceConditions

noncomputable section

namespace GlobalTheory.ExpAtTypePrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.PeriodLowerBounds

theorem col_smul {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (a : ℂ)
    (φ : C.cls 0 → C.Y 0 → ℂ) : C.col (a • φ) = a • C.col φ := by
  unfold ColumnChain.col
  generalize R.m = n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext j
    simp only [Formalism.ThetaLiftIndependence.chainOpM, Formalism.ThetaLiftIndependence.kerOpM, ih, Pi.smul_apply, map_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem perCol_smul (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (a : ℂ) (φ : D.what₂.Mu u) (F : D.what₂.Amb μ) :
    D.what₂.perCol u μ (a • φ) F = a * D.what₂.perCol u μ φ F := by
  by_cases hμ : μ = D.what₂.mu0
  · subst hμ
    simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, Submodule.coe_smul, col_smul,
      LinearMap.smul_apply, smul_eq_mul]
  · simp only [D.perCol_tie u μ hμ, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, Submodule.coe_smul, col_smul,
      LinearMap.smul_apply, smul_eq_mul]

theorem perGe_mono {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {φ : (D.div.Nu u).V}
    {F : D.what₂.Amb μ} {s s' : ℝ} (hs : s' ≤ s) (h : PerGe_vw D u μ w φ F s) : PerGe_vw D u μ w φ F s' :=
  let ⟨y, hy, hv⟩ := h
  ⟨y, hy, hv.imp id fun h1 => hs.trans h1⟩

theorem vAdd_of_notMem {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K}
    (ha : a ∉ w.asIdeal) : vAdd w (algebraMap (𝓞 K) K a) = 0 := by
  have h : w.valuation K (algebraMap (𝓞 K) K a) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 ha
  simp [vAdd, h]

theorem perGe_of_smul {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {φ : (D.div.Nu u).V}
    {F : D.what₂.Amb μ} {s : ℝ} {a : 𝓞 D.what₂.LL} (ha : a ∉ (D.plEq w).asIdeal)
    (h : PerGe_vw D u μ w (a • φ) F s) : PerGe_vw D u μ w φ F s := by
  obtain ⟨y, hy, hv⟩ := h
  set a' : D.what₂.LL := algebraMap (𝓞 D.what₂.LL) D.what₂.LL a with ha'
  have ha0 : a' ≠ 0 := by
    intro h0
    have : a = 0 := (FaithfulSMul.algebraMap_injective (𝓞 D.what₂.LL) D.what₂.LL) (by rw [map_zero]; exact h0)
    exact ha (this ▸ Ideal.zero_mem _)
  have e : a • φ = a' • φ := (algebraMap_smul D.what₂.LL a φ).symm
  rw [e, LinearMap.map_smulₛₗ, perCol_smul] at hy
  have hc : D.what₂.embLL a' ≠ 0 := (map_ne_zero _).2 ha0
  refine ⟨y / a', ?_, ?_⟩
  · rw [map_div₀, hy]; field_simp
  · by_cases hy0 : y = 0
    · left; simp [hy0]
    · right
      have h1 := hv.resolve_left hy0
      have h2 : vAdd (D.plEq w) y = vAdd (D.plEq w) (y / a') := by
        have h3 : y = a' * (y / a') := by field_simp
        have h4 := WeilJacquetShalikaLaw.vAdd_mul' (D.plEq w) ha0 (div_ne_zero hy0 ha0)
        rw [← h3, ha', vAdd_of_notMem _ ha, zero_add] at h4
        exact h4
      rwa [← h2]

theorem linkRam_of {D : D7} {L : SizeData₂ D} {X : ErrX D} {C1 : ℝ} (hE : ExpLe L X C1) (hP : PeriodBound L X C1) :
    LinkRam L := fun i w hw u μ hμ φ hφ F hF =>
  perGe_mono (mul_le_mul_of_nonneg_left (hE i w hw u) (Nat.cast_nonneg _))
    (hP i w hw u (hw ▸ T_ne_g X u i) μ hμ φ hφ F hF)

theorem linkNu_of {D : D7} {L : SizeData₂ D} (X : ErrX D) (hR : LinkRam L) (hN : DV.NuDef D L) : LinkNu L := by
  intro i w hw u φ hφ F hF
  obtain ⟨a, ha, hm⟩ := hN.1 u w (hw ▸ T_ne_g X u i) φ hφ
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hm
  exact perGe_of_smul ha (hR i w hw u _ (WeilJacquetShalikaLaw.used_muAt D w) _ hm F hF)

theorem stmt : GlobalTheory.IndefiniteRowSideFullHecke.PeriodLowerBounds.Stmt := fun _ _ X _ _ _ _ hF hE hC =>
  have h1 := expLe_of hF hE hC
  ⟨h1, fun hP => ⟨linkRam_of h1 hP, linkNu_of X (linkRam_of h1 hP)⟩⟩

theorem periodBound_iff {D : D7} (L : SizeData₂ D) (X : ErrX D) (C1 : ℝ) :
    PeriodBound L X C1 ↔ ∀ (i : Fin 2) (w : LiftErrorLocal.Pl D), LiftErrorLocal.Over D i w → ∀ u : D.what₂.Word,
      D.what₂.places.resChar w ≠ (D.mem u).A.T → ∀ μ : D.what₂.Tup, DV.Used D μ → GlobalTheory.IndefiniteRowSideFullHecke.ColumnAvoidanceConditions.Bound D L X C1 i w u μ := by
  refine forall_congr' fun i => forall_congr' fun w => forall_congr' fun _ => forall_congr' fun u => forall_congr' fun _ =>
    forall_congr' fun μ => forall_congr' fun _ => forall_congr' fun φ => forall_congr' fun _ => forall_congr' fun F =>
    forall_congr' fun _ => exists_congr fun y => and_congr_right fun _ => or_congr_right ?_
  have he : (0 : ℝ) < (D.what₂.places.ramIdx w : ℝ) := by exact_mod_cast D.what₂.places.ramIdx_pos w
  unfold LiftErrorLocal.vG
  rw [le_div_iff₀ he, mul_comm]
  rfl

theorem stmtFam {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) : FamilyErrorExponentBound Fm C1 := stmtFam_of stmt Fm C1

end GlobalTheory.ExpAtTypePrimes

end

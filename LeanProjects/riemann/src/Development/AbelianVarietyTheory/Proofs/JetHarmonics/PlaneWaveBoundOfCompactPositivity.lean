import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfHeads
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialExhaustion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWaveMain
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.XiExistsOfBesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegrableWeightNormSq
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.QuantumDeterminants NumberField MeasureTheory
open scoped ComplexOrder
open Formalism.FourierDecayAlt.P.TBBx5 Filter Topology
open scoped ComplexConjugate ENNReal

namespace GlobalTheory

noncomputable section

open Classical

namespace PlaneWaveCompact

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end PlaneWaveCompact

open NumberField MeasureTheory in
open scoped ComplexOrder in
open Filter Topology in
open scoped ComplexConjugate ENNReal in
open Classical in
private lemma integral_planeWave_eq_lemma_3 (hQ : _root_.Formalism.FourierDecayAlt.P5.ThmPActualCpt) {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Cb : ℝ)
    (hI : _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base F) (j : ℕ) (hj : j ≤ P.r)
    (h : _root_.Formalism.FourierDecayAlt.C.LPt) (hh : _root_.Formalism.FourierDecayAlt.D.IsLocPt h j) (w : List _root_.Formalism.FourierDecayAlt.C.Letter) (hw : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w) (s : ℂ) :
    ∫ c : ℂ, _root_.Formalism.FourierDecayAlt.P5.fsv s c * _root_.Formalism.FourierDecayAlt.TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) =
      ((_root_.Formalism.FourierDecayAlt.C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / _root_.Formalism.FourierDecayAlt.TBB.normC nn w : ℝ) : ℂ) *
        p.form j hj w (_root_.Formalism.FourierDecayAlt.KB.waveG (p.T.bs j) s w (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj w h (And.right hh)))
          (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj w h (And.right hh)) := by
  obtain ⟨φ, -, -, hφ, hint⟩ := _root_.Formalism.FourierDecayAlt.P.PBO.pStdCpt_of_heads hQ _root_.Formalism.FourierDecayAlt.P.radial_head _root_.Formalism.FourierDecayAlt.P.head_top Wp Wq P p F j hj w h h hh hh Cb hI hF hw
  rw [← hint s, ← integral_const_mul]
  apply integral_congr_ae
  have h0 : ∀ᵐ c : ℂ, c ≠ 0 := by
    rw [ae_iff]
    simpa using (measure_singleton (μ := (volume : Measure ℂ)) (0 : ℂ))
  filter_upwards [h0] with c hc
  rw [hφ c hc, ← _root_.Formalism.FourierDecayAlt.P.TBBx5.wv_np p nn F j hj h hh w c]
  ring

open NumberField MeasureTheory in
open scoped ComplexOrder in
open Filter Topology in
open scoped ComplexConjugate ENNReal in
open Classical in
private lemma shiftedPairing_bound_lemma_4 (hQ : _root_.Formalism.FourierDecayAlt.P5.ThmPActualCpt) (hV : _root_.Formalism.FourierDecayAlt.KB.VIsoCpt) (hS : _root_.Formalism.FourierDecayAlt.KB.SizeStdCpt)
    (hPos : _root_.Formalism.FourierDecayAlt.P.PBL.FormPosCpt) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (nn : ℝ → ℝ)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hF : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base F) (hnn : ∀ y, 0 < nn y)
    (j : ℕ) (hj : j ≤ P.r) (h : _root_.Formalism.FourierDecayAlt.C.LPt) (hh : _root_.Formalism.FourierDecayAlt.D.IsLocPt h j) (w : List _root_.Formalism.FourierDecayAlt.C.Letter) (s : ℂ)
    (ys : List ℝ) (h₁ : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 (_root_.Formalism.FourierDecayAlt.KB.plusW ys w)) (h₂ : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 (_root_.Formalism.FourierDecayAlt.KB.minusW ys w))
    (hys : List.Pairwise (fun y y' => 2 < |y - y'|) ys) :
    _root_.Formalism.FourierDecayAlt.C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / _root_.Formalism.FourierDecayAlt.TBB.normC nn w *
        ‖_root_.Formalism.FourierDecayAlt.KB.pairJ (p.form j hj w) ys
          (_root_.Formalism.FourierDecayAlt.KB.waveG (p.T.bs j) s (_root_.Formalism.FourierDecayAlt.KB.plusW ys w)
            (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj (_root_.Formalism.FourierDecayAlt.KB.plusW ys w) h (And.right hh)))
          (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj (_root_.Formalism.FourierDecayAlt.KB.minusW ys w) h (And.right hh))‖ ≤
      √((ys.map nn).prod * (ys.map fun y : ℝ => nn (y + 1)).prod /
          (ys.map fun y : ℝ => (_root_.Formalism.FourierDecayAlt.Wd.qw (_root_.Formalism.FourierDecayAlt.M.qC P) (_root_.Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re).prod) *
        max (_root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.plusW ys w) h) (_root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.minusW ys w) h) := by
  have hx : ∀ e, _root_.Formalism.FourierDecayAlt.KB.CptCoef (p.T.bs j) (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj (_root_.Formalism.FourierDecayAlt.KB.plusW ys w) h (And.right hh) e) :=
    fun e => _root_.Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj _ h hh hF e
  have hx' : ∀ e, _root_.Formalism.FourierDecayAlt.KB.CptCoef (p.T.bs j) (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj (_root_.Formalism.FourierDecayAlt.KB.minusW ys w) h (And.right hh) e) :=
    fun e => _root_.Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj _ h hh hF e
  obtain ⟨hθ, hbd⟩ := hS hQ Wp Wq P p j hj w ys h₁ h₂ hys
  have hU := hV hQ Wp Wq P p j hj (_root_.Formalism.FourierDecayAlt.KB.plusW ys w) h₁ s _ _ hx hx
  have key := hbd _ _ hU.1 hx'
  rw [hU.2] at key
  have f₁ := (Complex.nonneg_iff.mp (hPos hQ Wp Wq P p j hj _ h₁ _ hx)).1
  have f₂ := (Complex.nonneg_iff.mp (hPos hQ Wp Wq P p j hj _ h₂ _ hx')).1
  have hJL := _root_.Formalism.FourierDecayAlt.P.TBBx5.weighted_auxiliary_norm_nonneg P j hj h hh
  have hN := _root_.Formalism.FourierDecayAlt.P.TBBx5.normC_pos nn hnn w
  have hQ₁ := _root_.Formalism.FourierDecayAlt.P.TBBx5.prod_map_pos nn hnn ys
  have hQ₂ := _root_.Formalism.FourierDecayAlt.P.TBBx5.prod_map_pos (fun y => nn (y + 1)) (fun y => hnn _) ys
  have hq : 0 < (ys.map fun y : ℝ => (_root_.Formalism.FourierDecayAlt.Wd.qw (_root_.Formalism.FourierDecayAlt.M.qC P) (_root_.Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re).prod := by
    apply List.prod_pos
    intro a ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
    exact hθ y hy
  have hα : 0 ≤ _root_.Formalism.FourierDecayAlt.C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / _root_.Formalism.FourierDecayAlt.TBB.normC nn w := div_nonneg hJL hN.le
  have hcs := _root_.Formalism.FourierDecayAlt.P.TBBx5.scal_cs _ _ _ _ _ _ _ _ _ hα (by ring) hα hα hq hQ₁ hQ₂ (norm_nonneg _) f₁ f₂ key
  refine hcs.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  rw [_root_.Formalism.FourierDecayAlt.P.TBBx5.wv_ew p nn F j hj _ h hh, _root_.Formalism.FourierDecayAlt.P.TBBx5.wv_ew p nn F j hj _ h hh, _root_.Formalism.FourierDecayAlt.P.TBBx5.normC_plusW, _root_.Formalism.FourierDecayAlt.P.TBBx5.normC_minusW]
  refine le_trans (le_of_eq ?_) (_root_.Formalism.FourierDecayAlt.P.TBBx5.sqrt_mul_le_max _ _ ?_ ?_)
  · congr 1 <;> field_simp
  · exact mul_nonneg (div_nonneg hJL (mul_pos hQ₁ hN).le) f₁
  · exact mul_nonneg (div_nonneg hJL (mul_pos hQ₂ hN).le) f₂

open NumberField MeasureTheory in
open scoped ComplexOrder in
open Filter Topology in
open scoped ComplexConjugate ENNReal in
open Classical in
private lemma planeWave_grid_bound_lemma (hQ : _root_.Formalism.FourierDecayAlt.P5.ThmPActualCpt) (hV : _root_.Formalism.FourierDecayAlt.KB.VIsoCpt) (hS : _root_.Formalism.FourierDecayAlt.KB.SizeStdCpt)
    (hPos : _root_.Formalism.FourierDecayAlt.P.PBL.FormPosCpt) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (nn : ℝ → ℝ)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Cb : ℝ) (hI : _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ)
    (hF : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base F) (hnn : ∀ y, 0 < nn y) (j : ℕ) (hj : j ≤ P.r) (h : _root_.Formalism.FourierDecayAlt.C.LPt)
    (hh : _root_.Formalism.FourierDecayAlt.D.IsLocPt h j) (w : List _root_.Formalism.FourierDecayAlt.C.Letter) (hw : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w) (s : ℂ) (K : ℕ)
    (grid : Fin K → Fin (2 * j + 1) → ℝ) (hinj : ∀ a, Function.Injective (grid a))
    (hcut : ∀ n : Fin K → Fin (2 * j + 1),
      _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 (_root_.Formalism.FourierDecayAlt.KB.plusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n) w) ∧ _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 (_root_.Formalism.FourierDecayAlt.KB.minusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n) w) ∧
        List.Pairwise (fun y y' => 2 < |y - y'|) (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n)) :
    ‖s‖ ^ K *
        ‖∫ c : ℂ, _root_.Formalism.FourierDecayAlt.P5.fsv s c * _root_.Formalism.FourierDecayAlt.TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])‖ ≤
      ∑ n, |∏ a, _root_.Formalism.FourierDecayAlt.F7.lagCo (grid a) (n a)| *
        (√(((_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n).map nn).prod * ((_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n).map fun y : ℝ => nn (y + 1)).prod /
            ((_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n).map fun y : ℝ => (_root_.Formalism.FourierDecayAlt.Wd.qw (_root_.Formalism.FourierDecayAlt.M.qC P) (_root_.Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re).prod) *
          max (_root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.plusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n) w) h)
            (_root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.minusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n) w) h)) := by
  have hα : 0 ≤ _root_.Formalism.FourierDecayAlt.C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / _root_.Formalism.FourierDecayAlt.TBB.normC nn w :=
    div_nonneg (_root_.Formalism.FourierDecayAlt.P.TBBx5.weighted_auxiliary_norm_nonneg P j hj h hh) (_root_.Formalism.FourierDecayAlt.P.TBBx5.normC_pos nn hnn w).le
  have hdeg := _root_.Formalism.FourierDecayAlt.P.degree_of_plane_wave Wp Wq P p F j hj w h h hh hh K grid s LinearMap.id
    (fun _ _ hx e => hx e) hF hinj
  simp only [LinearMap.id_apply, _root_.Formalism.FourierDecayAlt.P.PBL.onOld_id] at hdeg
  rw [integral_planeWave_eq_lemma_3 hQ P p nn F Cb hI hF j hj h hh w hw s, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hα]
  calc ‖s‖ ^ K * (_root_.Formalism.FourierDecayAlt.C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / _root_.Formalism.FourierDecayAlt.TBB.normC nn w *
          ‖p.form j hj w (_root_.Formalism.FourierDecayAlt.KB.waveG (p.T.bs j) s w (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj w h (And.right hh)))
            (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj w h (And.right hh))‖)
      = _root_.Formalism.FourierDecayAlt.C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / _root_.Formalism.FourierDecayAlt.TBB.normC nn w *
          ‖s ^ K * p.form j hj w (_root_.Formalism.FourierDecayAlt.KB.waveG (p.T.bs j) s w (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj w h (And.right hh)))
            (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj w h (And.right hh))‖ := by
        rw [norm_mul, norm_pow]; ring
    _ ≤ _ := by
        rw [hdeg]
        refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hα).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun n _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_left_comm]
        exact mul_le_mul_of_nonneg_left
          (shiftedPairing_bound_lemma_4 hQ hV hS hPos P p nn F hF hnn j hj h hh w s _
            (hcut n).1 (hcut n).2.1 (hcut n).2.2) (abs_nonneg _)

open NumberField MeasureTheory in
open scoped ComplexOrder in
open Filter Topology in
open scoped ComplexConjugate ENNReal in
open Classical in
private lemma normalizedWeight_nonneg_lemma_2 (hQ : _root_.Formalism.FourierDecayAlt.P5.ThmPActualCpt) (hPos : _root_.Formalism.FourierDecayAlt.P.PBL.FormPosCpt) {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par)
    (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hF : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base F) (hnn : ∀ y, 0 < nn y) (j : ℕ) (hj : j ≤ P.r) (h : _root_.Formalism.FourierDecayAlt.C.LPt)
    (hh : _root_.Formalism.FourierDecayAlt.D.IsLocPt h j) (w : List _root_.Formalism.FourierDecayAlt.C.Letter) (hw : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w) :
    0 ≤ _root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j w h := by
  rw [_root_.Formalism.FourierDecayAlt.P.TBBx5.wv_ew p nn F j hj w h hh]
  have h1 := _root_.Formalism.FourierDecayAlt.P.TBBx5.weighted_auxiliary_norm_nonneg P j hj h hh
  have h2 := _root_.Formalism.FourierDecayAlt.P.TBBx5.normC_pos nn hnn w
  have h3 := hPos hQ Wp Wq P p j hj w hw _ (fun e => _root_.Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w h hh hF e)
  exact mul_nonneg (div_nonneg h1 h2.le) (Complex.nonneg_iff.mp h3).1

open NumberField MeasureTheory in
open scoped ComplexOrder in
open Filter Topology in
open scoped ComplexConjugate ENNReal in
open Classical in

theorem _root_.GlobalTheory.planeWave_bound_of_xiExists (hXi : _root_.Formalism.FourierDecayAlt.B.XiExists) :
    _root_.Formalism.FourierDecayAlt.P5.ThmPActualCpt → _root_.Formalism.FourierDecayAlt.KB.VIsoCpt → _root_.Formalism.FourierDecayAlt.KB.SizeStdCpt → _root_.Formalism.FourierDecayAlt.P.PBL.FormPosCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) (Cb : ℝ), _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base F → (∀ y, 0 < nn y) → _root_.Formalism.FourierDecayAlt.P.TBBx5.WaveGrid p nn Y Λ K N → _root_.Formalism.FourierDecayAlt.TBB.KernelFourierIntegralBound p nn F Y Λ K N := by
  intro hQ hV hS hPos Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N Cb hI hF hnn hgrid
  unfold _root_.Formalism.FourierDecayAlt.TBB.KernelFourierIntegralBound
  intro j hj h hh w hw hlen s
  have hw0 : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w := by
    unfold _root_.Formalism.FourierDecayAlt.TBB.AdmW at hw
    exact hw.1
  unfold _root_.Formalism.FourierDecayAlt.P.TBBx5.WaveGrid at hgrid
  obtain ⟨grid, hg⟩ := hgrid j hj w hw hlen
  unfold _root_.Formalism.FourierDecayAlt.P.TBBx5.GridOK at hg
  obtain ⟨hinj, hmem, hcut, hsum⟩ := hg

  have hE₁ : ‖∫ c : ℂ, _root_.Formalism.FourierDecayAlt.P5.fsv s c * _root_.Formalism.FourierDecayAlt.TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])‖ ≤
      _root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j w h := by
    have hnil : ∀ n : Fin 0 → Fin (2 * j + 1),
        _root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf (fun a => Fin.elim0 a : Fin 0 → Fin (2 * j + 1) → ℝ) n = [] :=
      fun n => List.ofFn_zero
    have hb := planeWave_grid_bound_lemma hQ hV hS hPos P p nn F Cb hI hF hnn j hj h hh w hw0 s 0
      (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
      (fun n => by simp only [hnil, _root_.Formalism.FourierDecayAlt.P.TBBx5.plusW_eq, _root_.Formalism.FourierDecayAlt.P.TBBx5.minusW_eq, List.map_nil, List.nil_append]; exact ⟨hw0, hw0, List.Pairwise.nil⟩)
    simpa [hnil, _root_.Formalism.FourierDecayAlt.P.TBBx5.plusW_eq, _root_.Formalism.FourierDecayAlt.P.TBBx5.minusW_eq] using hb

  obtain ⟨n₀, hn₀⟩ := _root_.Formalism.FourierDecayAlt.P.TBBx5.sum_le_max
    (fun n => |∏ a, _root_.Formalism.FourierDecayAlt.F7.lagCo (grid a) (n a)| *
      √(((_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n).map nn).prod * ((_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n).map fun y : ℝ => nn (y + 1)).prod /
          ((_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n).map fun y : ℝ => (_root_.Formalism.FourierDecayAlt.Wd.qw (_root_.Formalism.FourierDecayAlt.M.qC P) (_root_.Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re).prod))
    (fun n => max (_root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.plusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n) w) h)
      (_root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.minusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n) w) h))
    (Λ ^ K) (fun n => by positivity)
    (fun n => le_max_of_le_left
      (normalizedWeight_nonneg_lemma_2 hQ hPos P p nn F hF hnn j hj h hh _ (hcut n).1)) hsum
  have hE₂ : 0 < ‖s‖ → ‖s‖ ^ K *
      ‖∫ c : ℂ, _root_.Formalism.FourierDecayAlt.P5.fsv s c * _root_.Formalism.FourierDecayAlt.TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])‖ ≤
      Λ ^ K * max (_root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.plusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n₀) w) h)
        (_root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.minusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n₀) w) h) := fun _ =>
    (planeWave_grid_bound_lemma hQ hV hS hPos P p nn F Cb hI hF hnn j hj h hh w hw0 s K grid hinj
      hcut).trans (by simpa only [mul_assoc] using hn₀)
  have hlenK : (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n₀).length = K := List.length_ofFn
  rcases _root_.Formalism.FourierDecayAlt.P.TBBx5.mn_pick Λ ‖s‖ _ _ _ K (norm_nonneg s) hE₁ hE₂ with H | H
  · exact ⟨w, _root_.Formalism.FourierDecayAlt.P.TBBx5.isExt_self P p.l0 Y N K w hw (by omega), H⟩
  · by_cases hm : _root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.minusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n₀) w) h ≤
        _root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.plusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n₀) w) h
    · refine ⟨_root_.Formalism.FourierDecayAlt.KB.plusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n₀) w,
        _root_.Formalism.FourierDecayAlt.P.TBBx5.isExt_plusW P p.l0 Y N K w _ hlen hlenK (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf_mem grid hmem n₀) (hcut n₀).1, ?_⟩
      rwa [max_eq_left hm] at H
    · refine ⟨_root_.Formalism.FourierDecayAlt.KB.minusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n₀) w,
        _root_.Formalism.FourierDecayAlt.P.TBBx5.isExt_minusW P p.l0 Y N K w _ hlen hlenK (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf_mem grid hmem n₀) (hcut n₀).2.1, ?_⟩
      rwa [max_eq_right (le_of_not_ge hm)] at H

end

end GlobalTheory

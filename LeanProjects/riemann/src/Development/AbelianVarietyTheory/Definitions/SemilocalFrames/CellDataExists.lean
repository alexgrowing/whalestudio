import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellAmp.Model

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

theorem amp_dirac {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (R : BranchingSupport.Rep k r) (l : R.H → Wp) (l' : R.H → Wq) (w : R.H)
    (x : Mt k r) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (η : Wq) :
    amp R l l' w (Measure.dirac x) γ η =
      ⟪l' (R.σ (Matrix.of x) w), η⟫_ℂ • l (R.σ (γ * Matrix.of x) w) := by
  unfold amp ampJ
  rw [integral_dirac]
  simp

theorem coefF_apply {k r : ℕ} (L : LocBessel k r) (v v' : L.Hs) (ξ : L.Wp) (ξ' η : L.Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    coefF L v v' ξ ξ' g η = (⟪ξ', η⟫_ℂ * ⟪v, L.σ g v'⟫_ℂ) • ξ := by
  simp [coefF, smul_smul]

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
private theorem inv_mul_conj_mul_cancel {n : Type*} [Fintype n] [DecidableEq n] (A B C D γ a : Matrix n n ℂ)
    (hγ : IsUnit γ.det) (ha : IsUnit a.det) :
    A⁻¹ * (a * B)⁻¹ * γ * (γ⁻¹ * a * γ * C) * D = A⁻¹ * B⁻¹ * γ * C * D := by
  rw [Matrix.mul_inv_rev]
  have h1 : γ * γ⁻¹ = 1 := Matrix.mul_nonsing_inv γ hγ
  have h2 : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a ha
  calc A⁻¹ * (B⁻¹ * a⁻¹) * γ * (γ⁻¹ * a * γ * C) * D
      = A⁻¹ * B⁻¹ * (a⁻¹ * ((γ * γ⁻¹) * a)) * γ * C * D := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.one_mul, h2, Matrix.mul_one]

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in

theorem _root_.GlobalTheory.CellAmp.Model.pairMaj_stabAct {k r : ℕ} (γ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hγ : IsUnit γ.det)
    (ha : IsUnit a.det) (b : ℝ) (p : _root_.Formalism.MainNotions.S.PairSp k r) : _root_.GlobalTheory.CellAmp.pairMaj γ b (_root_.Formalism.MainNotions.S.stabAct γ a p) = _root_.GlobalTheory.CellAmp.pairMaj γ b p :=
  congrArg (fun M => _root_.Formalism.FourierDecayAlt.B.gN M ^ (-b))
    (inv_mul_conj_mul_cancel (of p.1.1) (of p.1.2) (of p.2.2) (of p.2.1) γ a hγ ha)

theorem gap_exists (k r : ℕ) (hk : 1 ≤ k) : ∃ h : ℝ, Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h ∧ GapCell k r h := by
  have hs : 0 < 8 * Real.sqrt (2 * ((r : ℝ) + 1)) := by positivity
  have ht : Filter.Tendsto (fun h : ℝ => Formalism.FourierDecayAlt.ThreeDimData.aOf r h) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.atTop_div_const hs
  obtain ⟨h, h1, h2, h3, h4⟩ := ((Filter.eventually_ge_atTop (120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)).and
    ((ht.eventually_ge_atTop _).and ((ht.eventually_ge_atTop _).and (ht.eventually_ge_atTop _)))).exists
  exact ⟨h, ⟨hk, h1, h2, h3⟩, h4⟩

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.CellAmp.Model.ell_one (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) : _root_.Formalism.QuantumDeterminants.ell k r z 1 = 0 := by
  unfold _root_.Formalism.QuantumDeterminants.ell
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with h
  · rw [Matrix.one_apply_ne]
    intro he
    have := congrArg Fin.val he
    simp [_root_.Formalism.QuantumDeterminants.eI] at this
  · rw [Matrix.one_mulVec]
    exact hz _ (Or.inl (by simp [_root_.Formalism.QuantumDeterminants.eI]))

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in

theorem _root_.GlobalTheory.CellAmp.Model.cellData_open {k r : ℕ} (L : _root_.Formalism.MainNotions.S.LocBessel k r) (μG : Measure (_root_.Formalism.QuantumDeterminants.Mt k r))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r)) (hinv : g⁻¹ * g = 1)
    (hG : 0 < _root_.Formalism.QuantumDeterminants.Gf k r L.z L.z' g) (hm : _root_.Formalism.FourierDecayAlt.C2.IsMonomial (_root_.Formalism.QuantumDeterminants.Zhat k r L.z L.z' g))
    (hR : _root_.Formalism.MainNotions.S.RStab k r g = {1}) :
    _root_.GlobalTheory.CellAmp.CellData L μG g (Measure.dirac (fun i j => (1 : _root_.Formalism.MainNotions.S.MatKR k r) i j)) μG (_root_.Formalism.MainNotions.S.pairMeas L) := by
  have hone : (of fun i j => (1 : _root_.Formalism.MainNotions.S.MatKR k r) i j) = 1 := rfl
  refine ⟨hg, hG, hm, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hR, Set.mem_singleton_iff] at ha
    subst ha
    rw [Matrix.mul_one, hinv]
    unfold _root_.Formalism.QuantumDeterminants.psi
    rw [_root_.GlobalTheory.CellAmp.Model.ell_one _ _ _ L.hz.1, _root_.GlobalTheory.CellAmp.Model.ell_one _ _ _ L.hz'.1]
  · refine ⟨inferInstance, Measure.dirac_ne_zero, ?_, ?_⟩
    · rw [hR, Measure.dirac_apply]
      simp only [Set.mem_singleton_iff, Set.indicator_apply, Set.mem_setOf_eq]
      rw [hone]
      simp
    · intro s hs
      rw [hR, Set.mem_singleton_iff] at hs
      subst hs
      have hid : _root_.Formalism.QuantumDeterminants.lmulM (k := k) (r := r) 1 = id := funext fun x => by
        unfold _root_.Formalism.QuantumDeterminants.lmulM
        rw [Matrix.one_mul]
        rfl
      rw [hid, Measure.map_id]
  · intro f hf
    have hstab : ∀ x, _root_.Formalism.MainNotions.S.stabAct g (of fun i j => (1 : _root_.Formalism.MainNotions.S.MatKR k r) i j) x = x := by
      intro x
      unfold _root_.Formalism.MainNotions.S.stabAct
      rw [hone, Matrix.one_mul, Matrix.mul_one, hinv, Matrix.one_mul]
      rfl
    refine lintegral_congr fun x => ?_
    rw [lintegral_dirac, hstab]
  · intro f hf
    rw [Measure.map_congr (ae_eq_dirac _)]
    erw [Measure.map_const]
    rw [measure_univ, one_smul]
    refine lintegral_congr fun x => ?_
    rw [lintegral_dirac, hone, Matrix.mul_one, hinv, hone, Matrix.one_mul]
    rfl

theorem nset_zero (k : ℕ) : Nset k 0 = {1} := Formalism.FourierDecayAlt.P.unipotent_haar_base_case k

theorem cellData_exists {k : ℕ} (hk : 1 ≤ k) (L : LocBessel k 0) (μG : Measure (Mt k 0)) :
    ∃ g μR νR ν, CellData L μG g μR νR ν := by
  obtain ⟨μs, -, hμ⟩ := Formalism.FourierDecayAlt.P.SettingConstruction.sectionExists k 0 L.z L.z' hk L.hz.1 L.hz'.1 L.hz.2 L.hz'.2
  set τ := Tz k 0 L.z * Tz k 0 L.z' with hτ
  have hτ0 : 0 < τ := mul_pos L.hz.2 L.hz'.2
  set ζ : ℂ := ((τ + 1 : ℝ) : ℂ) with hζ
  have hn : τ < Complex.normSq ζ := by
    rw [hζ, Complex.normSq_ofReal]; nlinarith
  obtain ⟨hU, hz⟩ := hμ ζ hn
  let c : Fin 0 → ℂ := fun a => a.elim0
  have hmem := bigCellMem k 0 c (μs ζ) (fun a => a.elim0) hU
  have hZ := bigCellZhat k 0 L.z L.z' c (μs ζ) L.hz.1 L.hz'.1
  rw [Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ L.hz.1 L.hz'.1, hz] at hZ
  have hinv : (bigCell k 0 c (μs ζ))⁻¹ * bigCell k 0 c (μs ζ) = 1 := by
    apply Matrix.nonsing_inv_mul
    have h := congrArg Matrix.det (show (bigCell k 0 c (μs ζ))ᴴ * Hpk k 0 * bigCell k 0 c (μs ζ) = Hpk k 0 from hmem)
    have hH : (Hpk k 0).det ≠ 0 := by
      have h2 := congrArg Matrix.det (hpkFacts k 0).2.1
      rw [Matrix.det_mul, Matrix.det_one] at h2
      intro h0; rw [h0] at h2; simp at h2
    rw [Matrix.det_mul, Matrix.det_mul] at h
    refine isUnit_iff_ne_zero.2 fun h0 => hH ?_
    rw [← h, h0, mul_zero]
  refine ⟨_, _, _, _, cellData_open L μG _ hmem hinv ?_ ?_ ?_⟩
  · unfold Gf Dmin
    rw [hZ]
    have e1 : ((Matrix.diagonal fun a : Fin (0 + 1) => if h : a.val < 0 then c ⟨a.val, h⟩ else ζ).submatrix
        (Fin.castLE (Nat.le_of_lt_succ (Fin.last (0 + 1)).isLt))
        (Fin.castLE (Nat.le_of_lt_succ (Fin.last (0 + 1)).isLt))).det = ζ := by
      have : Unique (Fin (Fin.last (0 + 1)).val) := inferInstanceAs (Unique (Fin 1))
      rw [Matrix.det_unique]; simp
    rw [e1]
    have : IsEmpty (Fin (⟨0, by omega⟩ : Fin (0 + 2)).val) := inferInstanceAs (IsEmpty (Fin 0))
    rw [Matrix.det_isEmpty]
    simp only [map_one, mul_one]
    linarith
  · refine ⟨1, fun _ => ζ, fun _ h0 => ?_, ?_⟩
    · have h0' : ζ = 0 := h0
      rw [h0'] at hn; simp at hn; linarith
    · rw [hZ]; ext i j
      have : i = j := Subsingleton.elim (α := Fin 1) i j
      subst this
      simp [Formalism.FourierDecayAlt.C2.monoP]
  · ext a
    simp only [RStab, nset_zero, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, by rw [mul_one, hinv]⟩

end GlobalTheory.CellAmp.Model

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnDiagValExtTrace

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CurveDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

def part (ρ : AlgChart p σ 1 → CxPts p σ → ℝ) : Measure (CxPts p σ) :=
  ChartGlue.glueMeas (fun c : AlgChart p σ 1 => c.e) fun c y => ENNReal.ofReal (ρ c y)

def IsDens (ρ : AlgChart p σ 1 → CxPts p σ → ℝ) : Prop :=
  (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
    ρ c y = ‖ChartGlue.transDet c.e c'.e y‖ ^ 2 * ρ c' y) ∧
  ∀ c : AlgChart p σ 1, ContinuousOn (fun v => ρ c (c.e.symm v)) c.e.target

def total (ρ : AlgChart p σ 1 → CxPts p σ → ℝ) : ℝ :=
  (part ρ univ).toReal - (part (fun c y => -ρ c y) univ).toReal

variable {ρ ρ' : AlgChart p σ 1 → CxPts p σ → ℝ}

theorem part_congr (h : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = ρ' c y) :
    part ρ = part ρ' := by
  unfold part ChartGlue.glueMeas
  refine iSup_congr fun c => Measure.ext fun A hA => ?_
  rw [ChartGlue.chartMeas_apply _ _ hA, ChartGlue.chartMeas_apply _ _ hA]
  refine setLIntegral_congr_fun (ChartGlue.measurableSet_image _
    (c.e.open_source.measurableSet.inter hA) inter_subset_left) ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [c.e.left_inv hy.1, h c y hy.1]

theorem total_congr (h : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = ρ' c y) :
    total ρ = total ρ' := by
  rw [total, total, part_congr h,
    part_congr (ρ := fun c y => -ρ c y) (ρ' := fun c y => -ρ' c y) fun c y hy => by rw [h c y hy]]

theorem part_eq_zero (h : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y ≤ 0) : part ρ = 0 := by
  refine le_antisymm (iSup_le fun c => le_of_eq (Measure.measure_univ_eq_zero.1 ?_)) bot_le
  rw [ChartGlue.chartMeas_apply _ _ MeasurableSet.univ, inter_univ, c.e.image_source_eq_target]
  refine setLIntegral_eq_zero c.e.open_target.measurableSet fun v hv => ?_
  exact ENNReal.ofReal_eq_zero.2 (h c _ (c.e.map_target hv))

theorem total_eq_of_nonneg (h : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, 0 ≤ ρ c y) :
    total ρ = (part ρ univ).toReal := by
  rw [total, part_eq_zero (ρ := fun c y => -ρ c y) fun c y hy => neg_nonpos.2 (h c y hy)]
  simp

theorem IsDens.part_apply [SecondCountableTopology (CxPts p σ)] (h : IsDens ρ) (c : AlgChart p σ 1)
    {T : Set (CxPts p σ)} (hT : MeasurableSet T) (hc : T ⊆ c.e.source) :
    part ρ T = ∫⁻ v in c.e '' T, ENNReal.ofReal (ρ c (c.e.symm v)) := by
  rw [part, ChartGlue.glueMeas_apply _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => by
    rw [h.1 c c' y hy hy', ENNReal.ofReal_mul (sq_nonneg _)]) c hT hc,
    ChartGlue.chartMeas_apply_of_subset _ _ hT hc]

theorem IsDens.add (h : IsDens ρ) (h' : IsDens ρ') : IsDens fun c y => ρ c y + ρ' c y :=
  ⟨fun c c' y hy hy' => by beta_reduce; rw [h.1 c c' y hy hy', h'.1 c c' y hy hy', mul_add],
    fun c => (h.2 c).add (h'.2 c)⟩

theorem IsDens.sub (h : IsDens ρ) (h' : IsDens ρ') : IsDens fun c y => ρ c y - ρ' c y :=
  ⟨fun c c' y hy hy' => by beta_reduce; rw [h.1 c c' y hy hy', h'.1 c c' y hy hy', mul_sub],
    fun c => (h.2 c).sub (h'.2 c)⟩

theorem IsDens.neg (h : IsDens ρ) : IsDens fun c y => -ρ c y :=
  ⟨fun c c' y hy hy' => by beta_reduce; rw [h.1 c c' y hy hy', mul_neg], fun c => (h.2 c).neg⟩

theorem IsDens.mul (h : IsDens ρ) {f : CxPts p σ → ℝ} (hf : Continuous f) :
    IsDens fun c y => f y * ρ c y :=
  ⟨fun c c' y hy hy' => by beta_reduce; rw [h.1 c c' y hy hy', mul_left_comm],
    fun c => (hf.comp_continuousOn c.e.continuousOn_symm).mul (h.2 c)⟩

theorem IsDens.congr (h : IsDens ρ) (e : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ' c y = ρ c y) :
    IsDens ρ' :=
  ⟨fun c c' y hy hy' => by rw [e c y hy, e c' y hy', h.1 c c' y hy hy'],
    fun c => (h.2 c).congr fun v hv => e c _ (c.e.map_target hv)⟩

theorem chernPart_eq {B : LB X} (φ : Weight p σ B) :
    φ.chernPart 1 1 = part (fun c y => c.chernDens φ y) ∧
      φ.chernPart 1 (-1) = part fun c y => -c.chernDens φ y := by
  constructor <;> simp [Weight.chernPart, part]

section BC

variable {S : ShortComplex X.Modules} {r s : ℕ} {h : Met p σ S.X₂ (r + s)} (hS : S.ShortExact)
  (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s)

theorem bcMeas_eq_part : h.bcMeas hS h₁ h₃ = part fun c y => h.bcDens hS h₁ h₃ c y := rfl

theorem isDens_bcDens (H : h.IsCInf) : IsDens fun c y => h.bcDens hS h₁ h₃ c y := by
  refine ⟨fun c c' y hy hy' => Met.bcDens_trans hS h₁ h₃ c c' H hy hy', fun c v hv => ?_⟩
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ (c.e.symm v)
  have hWo := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) a.U)
  have hK : ∀ w ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ a.U,
      MContDiffAt ∞ (fun v => h.gram a.frame (c.e.symm v)) w := fun w hw => by
    have := (H.gram a.frame hw.2).mContDiffAt c (c.e.map_target hw.1)
    rwa [c.e.right_inv hw.1] at this
  have hg := continuousOn_diagVal_extTrace hWo hK (fun w hw => h.posDef_gram_frame hS a hw.2)
    (EuclideanSpace.single 0 1)
  have hm := hWo.mem_nhds (show v ∈ _ from ⟨hv, ha⟩)
  refine ContinuousAt.continuousWithinAt
    (((continuousOn_const (c := (2 : ℝ))).mul hg).continuousAt hm |>.congr ?_)
  filter_upwards [hm] with w hw
  rw [Met.bcDens_eq hS h₁ h₃ a c H (c.e.map_target hw.1) hw.2, Met.bcForm, c.e.right_inv hw.1]
  rfl

theorem total_bcDens (H : h.IsCInf) :
    total (fun c y => h.bcDens hS h₁ h₃ c y) = (h.bcMeas hS h₁ h₃ univ).toReal :=
  total_eq_of_nonneg fun c _ hy => Met.bcDens_nonneg hS h₁ h₃ c H hy

end BC

def IsCosSq {V L L' : X.Modules} {r : ℕ} (h : Met p σ V r) (l : L ⟶ V) (l' : L' ⟶ V)
    (v : CxPts p σ → ℝ) : Prop :=
  ∀ (U : X.Opens) (t : Γ(L, U)) (t' : Γ(L', U)), ∀ y ∈ ptsIn p σ U,
    ‖h.form (l'.app U t') (l.app U t) y‖ ^ 2 =
      v y * (h.form (l.app U t) (l.app U t) y).re * (h.form (l'.app U t') (l'.app U t') y).re

theorem IsCosSq.symm {V L L' : X.Modules} {r : ℕ} {h : Met p σ V r} {l : L ⟶ V} {l' : L' ⟶ V}
    {v : CxPts p σ → ℝ} (H : IsCosSq h l l' v) : IsCosSq h l' l v := fun U t' t y hy => by
  rw [← h.conj_form, Complex.norm_conj, H U t t' y hy, mul_right_comm]

def VanishesAt {F Q : X.Modules} (s : F ⟶ Q) (z : X) : Prop :=
  ∀ (U : X.Opens) (t : Γ(F, U)) (e : Γ(Q, U)) (b : Γ(X, U)), z ∈ U →
    IsFrame (fun _ : Fin 1 => e) → s.app U t = b • e → z ∉ X.basicOpen b

section Calc

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

def angleForm (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ z : E) : ℂ :=
  ((‖q z‖ ^ 2 / (a z * a' z)) ^ n : ℝ) *
    (starRingEnd ℂ (q z) * (del q z ξ - q z * del (fun x => (Real.log (a' x) : ℂ)) z ξ) -
      q z * starRingEnd ℂ (dbar q z ξ - q z * dbar (fun x => (Real.log (a x) : ℂ)) z ξ)) /
    ((a z * a' z : ℝ) : ℂ)

end Calc

end GlobalTheory.CurveDens

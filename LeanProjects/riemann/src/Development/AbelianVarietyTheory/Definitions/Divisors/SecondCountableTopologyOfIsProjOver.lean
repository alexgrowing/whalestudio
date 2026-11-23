import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.LintegralBallRpowLtTop
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeI
import Development.AbelianVarietyTheory.Definitions.Divisors.NoCommonZeroCombVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOnEqZeroOfEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ContDiff TensorProduct
open MeasureTheory ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal

namespace GlobalTheory

variable {k : Type} [CommRing k] {Y : Scheme.{0}}

open CxPts

structure AnRead (p : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) where

  ι : Type

  chart : ι → AlgChart p σ D

  cover : ∀ y, ∃ i, y ∈ (chart i).e.source

namespace AnRead

variable {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

variable (p σ D) in

def all [SmoothOfRelativeDimension D p] : AnRead p σ D := ⟨_, id, AlgChart.exists_mem_source⟩

instance nonempty [SmoothOfRelativeDimension D p] : Nonempty (AnRead p σ D) := ⟨all p σ D⟩

variable (R R' : AnRead p σ D) {S T : Set (CxPts p σ)}

theorem exists_finite [CompactSpace (CxPts p σ)] :
    ∃ s : Finset R.ι, ∀ y, ∃ i ∈ s, y ∈ (R.chart i).e.source := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _ (fun i => (R.chart i).e.open_source)
    fun y _ => mem_iUnion.2 (R.cover y)
  exact ⟨s, fun y => by simpa using hs (mem_univ y)⟩

def HoloOn (S : Set (CxPts p σ)) (f : CxPts p σ → ℂ) : Prop :=
  ∀ i, DifferentiableOn ℂ (f ∘ (R.chart i).e.symm)
    ((R.chart i).e.target ∩ (R.chart i).e.symm ⁻¹' S)

def SmoothOn (S : Set (CxPts p σ)) (f : CxPts p σ → ℝ) : Prop :=
  ∀ i, ContDiffOn ℝ ∞ (f ∘ (R.chart i).e.symm) ((R.chart i).e.target ∩ (R.chart i).e.symm ⁻¹' S)

theorem holoOn_ev (W : Y.Opens) (f : Γ(Y, W)) : R.HoloOn (ptsIn p σ W) (ev p σ W f) :=
  fun i => (R.chart i).holo W f

variable {R}

theorem exists_eventuallyEq (c : AlgChart p σ D) {v : V D} (hv : v ∈ c.e.target) {E : Type*}
    (f : CxPts p σ → E) : ∃ i, c.e.symm v ∈ (R.chart i).e.source ∧
      f ∘ c.e.symm =ᶠ[𝓝 v] (f ∘ (R.chart i).e.symm) ∘ (R.chart i).e ∘ c.e.symm := by
  obtain ⟨i, hi⟩ := R.cover (c.e.symm v)
  exact ⟨i, hi, eventually_of_mem ((isOpen_over c.e (R.chart i).e.open_source).mem_nhds ⟨hv, hi⟩)
    fun w hw => (congrArg f ((R.chart i).e.left_inv hw.2)).symm⟩

theorem HoloOn.chart {f : CxPts p σ → ℂ} (h : R.HoloOn S f) (hS : IsOpen S) (c : AlgChart p σ D) :
    DifferentiableOn ℂ (f ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' S) := fun v hv => by
  obtain ⟨i, hi, e⟩ := exists_eventuallyEq (R := R) c hv.1 f
  exact ((((h i).differentiableAt ((isOpen_over _ hS).mem_nhds (mem_over _ hi hv.2))).comp v
    ((c.holo_trans _).differentiableAt ((isOpen_over _ (R.chart i).e.open_source).mem_nhds
      ⟨hv.1, hi⟩))).congr_of_eventuallyEq e).differentiableWithinAt

theorem SmoothOn.chart {f : CxPts p σ → ℝ} (h : R.SmoothOn S f) (hS : IsOpen S)
    (c : AlgChart p σ D) : ContDiffOn ℝ ∞ (f ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' S) :=
  fun v hv => by
  obtain ⟨i, hi, e⟩ := exists_eventuallyEq (R := R) c hv.1 f
  have ho := isOpen_over c.e (R.chart i).e.open_source
  have ht : ContDiffOn ℝ ∞ ((R.chart i).e ∘ c.e.symm) _ := (contDiffOn_piLp 2).2 fun a =>
    contDiffOn_real ho (differentiableOn_euclidean.1 (c.holo_trans _) a)
  exact ((((h i).contDiffAt ((isOpen_over _ hS).mem_nhds (mem_over _ hi hv.2))).comp v
    (ht.contDiffAt (ho.mem_nhds ⟨hv.1, hi⟩))).congr_of_eventuallyEq e).contDiffWithinAt

theorem holoOn_iff (R R' : AnRead p σ D) (hS : IsOpen S) {f : CxPts p σ → ℂ} :
    R.HoloOn S f ↔ R'.HoloOn S f := ⟨fun h _ => h.chart hS _, fun h _ => h.chart hS _⟩

theorem smoothOn_iff (R R' : AnRead p σ D) (hS : IsOpen S) {f : CxPts p σ → ℝ} :
    R.SmoothOn S f ↔ R'.SmoothOn S f := ⟨fun h _ => h.chart hS _, fun h _ => h.chart hS _⟩

theorem HoloOn.mono {f : CxPts p σ → ℂ} (h : R.HoloOn S f) (e : T ⊆ S) : R.HoloOn T f :=
  fun i => (h i).mono fun _ hv => ⟨hv.1, e hv.2⟩

theorem SmoothOn.mono {f : CxPts p σ → ℝ} (h : R.SmoothOn S f) (e : T ⊆ S) : R.SmoothOn T f :=
  fun i => (h i).mono fun _ hv => ⟨hv.1, e hv.2⟩

theorem HoloOn.congr {f g : CxPts p σ → ℂ} (h : R.HoloOn S f) (e : ∀ y ∈ S, g y = f y) :
    R.HoloOn S g := fun i => (h i).congr fun _ hv => e _ hv.2

theorem SmoothOn.congr {f g : CxPts p σ → ℝ} (h : R.SmoothOn S f) (e : ∀ y ∈ S, g y = f y) :
    R.SmoothOn S g := fun i => (h i).congr fun _ hv => e _ hv.2

theorem continuousOn_of_charts {E : Type*} [TopologicalSpace E] {f : CxPts p σ → E} (hS : IsOpen S)
    (h : ∀ i, ContinuousOn (f ∘ (R.chart i).e.symm)
      ((R.chart i).e.target ∩ (R.chart i).e.symm ⁻¹' S)) : ContinuousOn f S := fun y hy => by
  obtain ⟨i, hi⟩ := R.cover y
  refine ((((h i).continuousAt ((isOpen_over _ hS).mem_nhds (mem_over _ hi hy))).comp
    ((R.chart i).e.continuousAt hi)).congr ?_).continuousWithinAt
  exact eventually_of_mem ((R.chart i).e.open_source.mem_nhds hi) fun z hz =>
    congrArg f ((R.chart i).e.left_inv hz)

theorem HoloOn.continuousOn {f : CxPts p σ → ℂ} (h : R.HoloOn S f) (hS : IsOpen S) :
    ContinuousOn f S := continuousOn_of_charts hS fun i => (h i).continuousOn

theorem SmoothOn.continuousOn {f : CxPts p σ → ℝ} (h : R.SmoothOn S f) (hS : IsOpen S) :
    ContinuousOn f S := continuousOn_of_charts hS fun i => (h i).continuousOn

theorem HoloOn.smoothOn_log {f : CxPts p σ → ℂ} (h : R.HoloOn S f) (hS : IsOpen S)
    (h0 : ∀ y ∈ S, f y ≠ 0) : R.SmoothOn S fun y => Real.log (‖f y‖ ^ 2) :=
  fun i => contDiffOn_log_normSq (isOpen_over _ hS) (h i) fun _ hv => h0 _ hv.2

end AnRead

variable {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

namespace AnRead

variable {R : AnRead p σ D} {A B : LB Y} {S : Set (CxPts p σ)}

theorem holoOn_of_chart (c : AlgChart p σ D) {f : CxPts p σ → ℂ}
    (h : DifferentiableOn ℂ (f ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' S)) :
    R.HoloOn (c.e.source ∩ S) f := fun i =>
  (h.comp (((R.chart i).holo_trans c).mono fun _ hv => ⟨hv.1, hv.2.1⟩)
    fun _ hv => mem_over _ hv.2.1 hv.2.2).congr fun _ hv => congrArg f (c.e.left_inv hv.2.1).symm

theorem holoOn_of_cover {ι : Type*} {T : ι → Set (CxPts p σ)} (hT : ∀ j, IsOpen (T j))
    (hc : ∀ y ∈ S, ∃ j, y ∈ T j) {f : CxPts p σ → ℂ} (h : ∀ j, R.HoloOn (S ∩ T j) f) :
    R.HoloOn S f := fun i => differentiableOn_of_locally_differentiableOn fun _ hv => by
  obtain ⟨j, hj⟩ := hc _ hv.2
  exact ⟨_, isOpen_over (R.chart i).e (hT j), ⟨hv.1, hj⟩,
    (h j i).mono fun _ hw => ⟨hw.1.1, hw.1.2, hw.2.2⟩⟩

theorem smoothOn_of_cover {ι : Type*} {T : ι → Set (CxPts p σ)} (hT : ∀ j, IsOpen (T j))
    (hc : ∀ y ∈ S, ∃ j, y ∈ T j) {f : CxPts p σ → ℝ} (h : ∀ j, R.SmoothOn (S ∩ T j) f) :
    R.SmoothOn S f := fun i => contDiffOn_of_locally_contDiffOn fun _ hv => by
  obtain ⟨j, hj⟩ := hc _ hv.2
  exact ⟨_, isOpen_over (R.chart i).e (hT j), ⟨hv.1, hj⟩,
    (h j i).mono fun _ hw => ⟨hw.1.1, hw.1.2, hw.2.2⟩⟩

theorem holoOn_ev_of_subset {W : Y.Opens} (f : Γ(Y, W)) (h : S ⊆ ptsIn p σ W) :
    R.HoloOn S (ev p σ W f) := (R.holoOn_ev W f).mono h

theorem HoloOn.mul {f g : CxPts p σ → ℂ} (hf : R.HoloOn S f) (hg : R.HoloOn S g) :
    R.HoloOn S fun y => f y * g y := fun i => (hf i).mul (hg i)

theorem HoloOn.zpow {f : CxPts p σ → ℂ} (hf : R.HoloOn S f) (h0 : ∀ y ∈ S, f y ≠ 0) (n : ℤ) :
    R.HoloOn S fun y => f y ^ n := fun i => (hf i).zpow (Or.inl fun _ hv => h0 _ hv.2)

theorem HoloOn.inv {f : CxPts p σ → ℂ} (hf : R.HoloOn S f) (h0 : ∀ y ∈ S, f y ≠ 0) :
    R.HoloOn S fun y => (f y)⁻¹ := fun i => (hf i).inv fun _ hv => h0 _ hv.2

variable (R B) in

def holSec : Submodule ℂ (B.ι → CxPts p σ → ℂ) where
  carrier := {s | s ∈ fibSec p σ B ∧ ∀ i, R.HoloOn (ptsIn p σ (B.U i)) (s i)}
  zero_mem' := ⟨zero_mem _, fun _ _ => differentiableOn_const (0 : ℂ)⟩
  add_mem' hs ht := ⟨add_mem hs.1 ht.1, fun i j => (hs.2 i j).add (ht.2 i j)⟩
  smul_mem' c _ hs := ⟨Submodule.smul_mem _ c hs.1, fun i j => (hs.2 i j).const_smul c⟩

theorem holSec_eq (R R' : AnRead p σ D) (B : LB Y) : R.holSec B = R'.holSec B :=
  Submodule.ext fun _ => and_congr_right fun _ =>
    forall_congr' fun _ => holoOn_iff R R' (isOpen_ptsIn _)

variable (R) in

theorem secVal_mem_holSec (s : B.Sec) : secVal p σ s ∈ R.holSec B :=
  ⟨secVal_mem s, fun _ => R.holoOn_ev _ _⟩

variable (R B) in

def valC : SecC p σ B →ₗ[ℂ] R.holSec B :=
  SecC.val.codRestrict _ (SecC.val_mem_of R.secVal_mem_holSec)

@[simp] theorem coe_valC (x : SecC p σ B) : (R.valC B x : B.ι → CxPts p σ → ℂ) = SecC.val x := rfl

theorem secTens_mem_holSec {s : A.ι → CxPts p σ → ℂ} {t : B.ι → CxPts p σ → ℂ}
    (hs : s ∈ R.holSec A) (ht : t ∈ R.holSec B) : secTens s t ∈ R.holSec (tens A B) :=
  ⟨secTens_mem hs.1 ht.1, fun c => ((hs.2 c.1).mono (ptsIn_mono inf_le_left)).mul
    ((ht.2 c.2).mono (ptsIn_mono inf_le_right))⟩

end AnRead

namespace Weight

open AnRead

variable {R : AnRead p σ D} {A B : LB Y} {φ : Weight p σ B}

def IsSmooth (φ : Weight p σ B) (R : AnRead p σ D) : Prop :=
  ∀ i, R.SmoothOn (ptsIn p σ (B.U i)) (φ.φ i)

def SemiPos (φ : Weight p σ B) (R : AnRead p σ D) : Prop :=
  ∀ (i : B.ι) (c : R.ι), ∀ y ∈ (R.chart c).e.source ∩ ptsIn p σ (B.U i), ∀ ξ : Fin D → ℂ,
    0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => (φ.φ i ((R.chart c).e.symm v) : ℂ)) ((R.chart c).e y) ξ).re

def StrictPos (φ : Weight p σ B) (R : AnRead p σ D) : Prop :=
  ∀ (i : B.ι) (c : R.ι), ∀ y ∈ (R.chart c).e.source ∩ ptsIn p σ (B.U i), ∀ ξ : Fin D → ℂ, ξ ≠ 0 →
    0 < (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => (φ.φ i ((R.chart c).e.symm v) : ℂ)) ((R.chart c).e y) ξ).re

theorem IsSmooth.of_anRead (h : φ.IsSmooth R) (R' : AnRead p σ D) : φ.IsSmooth R' :=
  fun i => (smoothOn_iff R R' (isOpen_ptsIn _)).1 (h i)

theorem IsSmooth.addFn (h : φ.IsSmooth R) {u : CxPts p σ → ℝ} (hu : R.SmoothOn univ u) :
    (φ.addFn u).IsSmooth R := fun i c => (h i c).add (hu.mono (subset_univ _) c)

theorem IsSmooth.tens {ψ : Weight p σ A} (h' : ψ.IsSmooth R) (h : φ.IsSmooth R) :
    (ψ.tens φ).IsSmooth R := fun i c =>
  ((h' i.1).mono (ptsIn_mono inf_le_left) c).add ((h i.2).mono (ptsIn_mono inf_le_right) c)

theorem IsSmooth.dual (h : φ.IsSmooth R) : φ.dual.IsSmooth R := fun i c => (h i c).neg

theorem IsSmooth.zpow (h : φ.IsSmooth R) (n : ℤ) : (φ.zpow n).IsSmooth R := fun j =>
  SmoothOn.congr (f := fun y => n * φ.φ (j PUnit.unit) y)
    (fun c => contDiffOn_const.mul ((h _).mono (fun _ => mem_pow_iff.1) c))
    fun y _ => φ.zpow_φ n j y

theorem isSmooth_ofPairs {hA : A.IsLB} {hB : B.IsLB} {ψ : A.ι → B.ι → CxPts p σ → ℝ} {h}
    (hψ : ∀ a b, R.SmoothOn (ptsIn p σ (A.U a) ∩ ptsIn p σ (B.U b)) (ψ a b)) :
    (ofPairs hA hB ψ h).IsSmooth R := fun a =>
  smoothOn_of_cover (fun b => isOpen_ptsIn (B.U b)) (fun y _ => ⟨_, mem_pick hB y⟩)
    fun b => (hψ a b).congr fun _ hy => ofPairs_φ hy.1 hy.2

theorem IsSmooth.cancel (hA : A.IsLB) {χ : Weight p σ (CechPic.tens A B)} (h' : χ.IsSmooth R)
    (h : φ.IsSmooth R) : (cancel hA χ φ).IsSmooth R :=
  isSmooth_ofPairs fun a b c => ((h' (a, b)).mono (fun _ => mem_ptsIn_inf.2) c).sub
    ((h b).mono inter_subset_right c)

theorem IsSmooth.ofIso (h : φ.IsSmooth R) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) :
    (φ.ofIso hA w hw).IsSmooth R :=
  isSmooth_ofPairs fun a b c => ((h b).mono inter_subset_right c).add
    ((holoOn_ev_of_subset (w.s (a, b)).val fun _ => mem_ptsIn_inf.2).smoothOn_log
      ((isOpen_ptsIn _).inter (isOpen_ptsIn _)) (fun _ hy => ev_iso_ne_zero w hy.2 hy.1) c)

theorem isSmooth_fs {α : Type*} [Fintype α] {e : α → B.ι → CxPts p σ → ℂ} (hB : B.IsLB)
    (he : ∀ a, e a ∈ R.holSec B) (h : NoCommonZero e) :
    (fs hB e (fun a => (he a).1) h).IsSmooth R := fun i c =>
  (ContDiffOn.sum (f := fun a v => ‖e a i ((R.chart c).e.symm v)‖ ^ 2) fun a _ =>
    (contDiffOn_real (isOpen_over _ (isOpen_ptsIn _)) ((he a).2 i c)).norm_sq ℂ).log
    fun _ hv => (h.sum_pos hv.2).ne'

theorem isSmooth_fsBasis {α : Type*} [Fintype α] [DecidableEq α] (hB : B.IsLB) (b : α → B.Sec)
    (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (M : Matrix α α ℂ) (hM : M.det ≠ 0) :
    (fsBasis p σ hB b hb M hM).IsSmooth R :=
  isSmooth_fs hB (fun a => combVal_eq (p := p) (σ := σ) b M a ▸ (R.valC B _).2) _

def ofFun (u : CxPts p σ → ℝ) : Weight p σ (LB.triv Y) where
  isLB := LB.isLB_triv Y
  φ _ := u
  trans _ _ _ hi _ := by
    rw [gv_self (LB.isLB_triv Y) hi, norm_one, one_pow, Real.log_one, sub_zero]

theorem isSmooth_ofFun {u : CxPts p σ → ℝ} (hu : R.SmoothOn univ u) : (ofFun u).IsSmooth R :=
  fun _ => hu.mono (subset_univ _)

theorem IsSmooth.continuous_nsq (h : φ.IsSmooth R) {s : B.ι → CxPts p σ → ℂ}
    (hs : s ∈ R.holSec B) : Continuous (φ.nsq s) := continuous_iff_continuousAt.2 fun y => by
  have ho := (isOpen_ptsIn (p := p) (σ := σ) _).mem_nhds (mem_pick φ.isLB y)
  refine ((((hs.2 _).continuousOn (isOpen_ptsIn _)).norm.pow 2).mul
    ((h _).continuousOn (isOpen_ptsIn _)).neg.rexp).continuousAt ho |>.congr ?_
  exact eventually_of_mem ho fun z hz => (φ.nsq_eq hs.1 hz).symm

end Weight

section Integral

variable [SmoothOfRelativeDimension D p] {B : LB Y} (K : CanonLB p D) (φ : Weight p σ B)
  (f : (tens K.bundle B).ι → CxPts p σ → ℂ)

namespace AlgChart

variable (c c' : AlgChart p σ D) {y : CxPts p σ}

def topCoeff (a : K.bundle.ι) (b : B.ι) (y : CxPts p σ) : ℂ :=
  rv σ c.isFrame (K.isFrame a) y * f (a, b) y

theorem rv_mul_jacobian {a : K.bundle.ι} (hy : y ∈ ptsIn p σ c.U)
    (ha : y ∈ ptsIn p σ (K.bundle.U a)) : rv σ c.isFrame (K.isFrame a) y *
      ev p σ _ (K.jacobian a inf_le_left fun i => resG Y (inf_le_right : _ ⊓ c.U ≤ _) (c.x i)) y =
      1 := by
  have e : ev p σ _ (K.jacobian a inf_le_left fun i => resG Y (inf_le_right : _ ⊓ c.U ≤ _) (c.x i)) =
      rv σ (K.isFrame a) c.isFrame := by
    rw [CanonLB.jacobian, ← resForm_dOn]
    rfl
  rw [e, rv_mul _ _ _ hy ha hy]
  exact mul_left_cancel₀ (rv_ne_zero c.isFrame c.isFrame hy hy)
    ((rv_mul _ _ _ hy hy hy).trans (mul_one _).symm)

theorem rv_mul_jacobian_eq_det {a : K.bundle.ι} {W : Y.Opens} (h : W ≤ K.bundle.U a)
    (g : Fin D → Γ(Y, W)) (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) :
    rv σ c.isFrame (K.isFrame a) y * ev p σ W (K.jacobian a h g) y = (c.jacMat g y).det := by
  have hy' : y ∈ ptsIn p σ (c.U ⊓ W) := mem_ptsIn_inf.2 ⟨c.source_subset hy, hW⟩
  rw [← c.jacMat_res inf_le_right g hy hy', ← c.ev_coeff_dOn inf_le_left _ hy hy',
    c.isFrame.coeff_change (K.isFrame a) inf_le_left (inf_le_right.trans h), ev_mul,
    ← ev_res inf_le_right hy', K.resG_jacobian, rv, ← ev_res (inf_le_inf_left _ h) hy',
    IsFrame.resG_ratio]
  rfl

def topDens (y : CxPts p σ) : ℝ :=
  2 ^ D * (‖c.topCoeff K f (pick K.isLB y) (pick φ.isLB y) y‖ ^ 2 *
    Real.exp (-φ.φ (pick φ.isLB y) y))

variable {f} in

theorem topDens_eq (hf : f ∈ fibSec p σ (tens K.bundle B)) (hy : y ∈ c.e.source) {a : K.bundle.ι}
    {b : B.ι} (ha : y ∈ ptsIn p σ (K.bundle.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    c.topDens K φ f y = 2 ^ D * (‖c.topCoeff K f a b y‖ ^ 2 * Real.exp (-φ.φ b y)) := by
  have ha' := mem_pick K.isLB y
  have hb' := mem_pick φ.isLB y
  have e : y ∈ ptsIn p σ ((tens K.bundle B).U (a, b)) := mem_ptsIn_inf.2 ⟨ha, hb⟩
  have e' : y ∈ ptsIn p σ ((tens K.bundle B).U (pick K.isLB y, pick φ.isLB y)) :=
    mem_ptsIn_inf.2 ⟨ha', hb'⟩
  rw [topDens, ← normSq_mul_exp (gv_ne_zero hb hb'), φ.trans b _ y hb hb', sub_add_cancel, topCoeff,
    topCoeff, hf.1 _ _ y e e', gv_tens e e', gv_canon,
    ← rv_mul _ (K.isFrame a) _ (c.source_subset hy) ha ha']
  congr 4
  ring

theorem topDens_trans (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) :
    c.topDens K φ f y = ‖transDet c.e c'.e y‖ ^ 2 * c'.topDens K φ f y := by
  rw [topDens, topDens, topCoeff, topCoeff, ← rv_mul _ c'.isFrame _ (c.source_subset hy)
    (c'.source_subset hy') (mem_pick K.isLB y), rv_chart c c' hy hy', mul_assoc (transDet _ _ _),
    norm_mul]
  ring

theorem chartMeas_topDens {A : Set (CxPts p σ)} (hA : MeasurableSet A) (h : A ⊆ c.e.source)
    (h' : A ⊆ c'.e.source) : chartMeas c.e (fun y => ENNReal.ofReal (c.topDens K φ f y)) A =
      chartMeas c'.e (fun y => ENNReal.ofReal (c'.topDens K φ f y)) A :=
  chartMeas_eq _ _ (c.holo_trans c') hA h h' fun y hy => by
    rw [c.topDens_trans K φ f c' (h hy) (h' hy), ENNReal.ofReal_mul (sq_nonneg _)]

end AlgChart

namespace AnRead

variable (R : AnRead p σ D)

def topMeasure : Measure (CxPts p σ) :=
  glueMeas (fun i => (R.chart i).e) fun i y => ENNReal.ofReal ((R.chart i).topDens K φ f y)

def topInt : ℝ≥0∞ := R.topMeasure K φ f univ

variable [SecondCountableTopology (CxPts p σ)]

theorem topMeasure_apply (c : AlgChart p σ D) {A : Set (CxPts p σ)} (hA : MeasurableSet A)
    (h : A ⊆ c.e.source) : R.topMeasure K φ f A =
      ∫⁻ v in c.e '' A, ENNReal.ofReal (c.topDens K φ f (c.e.symm v)) := by
  have key : (R.topMeasure K φ f).restrict A =
      (chartMeas c.e fun y => ENNReal.ofReal (c.topDens K φ f y)).restrict A :=
    ext_of_cover _ (fun i => (R.chart i).e.open_source) R.cover fun i T hT hi => by
      rw [Measure.restrict_apply hT, Measure.restrict_apply hT, topMeasure,
        glueMeas_apply _ _ (fun i j => (R.chart i).holo_trans (R.chart j)) (fun i j y hi hj => by
          rw [(R.chart i).topDens_trans K φ f _ hi hj, ENNReal.ofReal_mul (sq_nonneg _)])
        i (hT.inter hA) (inter_subset_left.trans hi)]
      exact AlgChart.chartMeas_topDens K φ f _ c (hT.inter hA) (inter_subset_left.trans hi)
        (inter_subset_right.trans h)
  rw [← chartMeas_apply_of_subset c.e (fun y => ENNReal.ofReal (c.topDens K φ f y)) hA h,
    ← Measure.restrict_apply_self, key, Measure.restrict_apply_self]

theorem topMeasure_eq (R' : AnRead p σ D) : R.topMeasure K φ f = R'.topMeasure K φ f :=
  ext_of_cover _ (fun i => (R.chart i).e.open_source) R.cover fun i _ hA h =>
    (R.topMeasure_apply K φ f _ hA h).trans (R'.topMeasure_apply K φ f _ hA h).symm

theorem topInt_eq (R' : AnRead p σ D) : R.topInt K φ f = R'.topInt K φ f := by
  rw [topInt, topInt, R.topMeasure_eq K φ f R']

variable {R φ f} in

theorem isLocallyFiniteMeasure_topMeasure (hφ : φ.IsSmooth R) (hf : f ∈ R.holSec (tens K.bundle B)) :
    IsLocallyFiniteMeasure (R.topMeasure K φ f) := ⟨fun y => by
  obtain ⟨i, hi⟩ := R.cover y
  set c := R.chart i
  have ha := mem_pick K.isLB y
  have hb := mem_pick φ.isLB y
  let S := ptsIn p σ (c.U ⊓ K.bundle.U (pick K.isLB y)) ∩ ptsIn p σ (B.U (pick φ.isLB y))
  have hS : IsOpen S := (isOpen_ptsIn _).inter (isOpen_ptsIn _)
  have hc : ContinuousOn (fun v => c.topDens K φ f (c.e.symm v)) (c.e.target ∩ c.e.symm ⁻¹' S) := by
    have h₁ := (holoOn_ev_of_subset (R := R) (c.isFrame.ratio (K.isFrame (pick K.isLB y))).val
      (inter_subset_left (t := ptsIn p σ (B.U (pick φ.isLB y))))).mul
      ((hf.2 (pick K.isLB y, pick φ.isLB y)).mono
        fun _ hz => mem_ptsIn_inf.2 ⟨(mem_ptsIn_inf.1 hz.1).2, hz.2⟩) i
    have h₂ := (hφ (pick φ.isLB y)).mono (inter_subset_right : S ⊆ _) i
    exact (continuousOn_const.mul ((h₁.continuousOn.norm.pow 2).mul h₂.continuousOn.neg.rexp)).congr
      fun v hv => c.topDens_eq K φ hf.1 (c.e.map_target hv.1) (mem_ptsIn_inf.1 hv.2.1).2 hv.2.2
  obtain ⟨C, hC, hCs, hCc⟩ := local_compact_nhds ((isOpen_over c.e hS).mem_nhds
    (mem_over c.e hi ⟨mem_ptsIn_inf.2 ⟨c.source_subset hi, ha⟩, hb⟩))
  have ho := c.e.isOpen_inter_preimage (isOpen_interior (s := C))
  refine ⟨_, ho.mem_nhds ⟨hi, mem_interior_iff_mem_nhds.2 hC⟩, ?_⟩
  rw [R.topMeasure_apply K φ f c ho.measurableSet inter_subset_left]
  refine (lintegral_mono_set ?_).trans_lt
    (Integrable.lintegral_lt_top ((hc.mono hCs).integrableOn_compact hCc))
  rintro _ ⟨z, hz, rfl⟩
  exact interior_subset hz.2⟩

variable {R φ f} in

theorem topInt_lt_top [CompactSpace (CxPts p σ)] (hφ : φ.IsSmooth R)
    (hf : f ∈ R.holSec (tens K.bundle B)) : R.topInt K φ f < ⊤ :=
  have := isLocallyFiniteMeasure_topMeasure K hφ hf
  isCompact_univ.measure_lt_top

end AnRead

end Integral

structure WeightFamily [SmoothOfRelativeDimension D p] (R : AnRead p σ D) (κ : Type) where

  K : CanonLB p D

  φK : Weight p σ K.bundle

  smoothK : φK.IsSmooth R

  L : κ → LB Y

  φ : ∀ a, Weight p σ (L a)

  smooth : ∀ a, (φ a).IsSmooth R

namespace WeightFamily

open AnRead

variable [SmoothOfRelativeDimension D p] {R : AnRead p σ D} {κ : Type} (F : WeightFamily R κ)

abbrev Idx : Type := R.ι × F.K.bundle.ι × ∀ a, (F.L a).ι

def dom (c : F.Idx) : Set (CxPts p σ) :=
  ptsIn p σ (F.K.bundle.U c.2.1) ∩ ⋂ a, ptsIn p σ ((F.L a).U (c.2.2 a))

variable [Fintype κ]

def refine : AnRead p σ D where
  ι := F.Idx
  chart c := (R.chart c.1).restr (F.dom c)
    ((isOpen_ptsIn _).inter (isOpen_iInter_of_finite fun _ => isOpen_ptsIn _))
  cover y := by
    obtain ⟨i, hi⟩ := R.cover y
    exact ⟨(i, pick F.K.isLB y, fun a => pick (F.φ a).isLB y), hi, mem_pick F.K.isLB y,
      mem_iInter.2 fun a => mem_pick (F.φ a).isLB y⟩

variable {F} {c c' : F.Idx} {y : CxPts p σ}

theorem mem_U (h : y ∈ (F.refine.chart c).e.source) : y ∈ ptsIn p σ (R.chart c.1).U :=
  (R.chart c.1).source_subset h.1

theorem mem_K (h : y ∈ (F.refine.chart c).e.source) : y ∈ ptsIn p σ (F.K.bundle.U c.2.1) := h.2.1

theorem mem_L (h : y ∈ (F.refine.chart c).e.source) (a : κ) :
    y ∈ ptsIn p σ ((F.L a).U (c.2.2 a)) := mem_iInter.1 h.2.2 a

variable (F)

def g₀ : Option κ → F.Idx → F.Idx → CxPts p σ → ℂ
  | none, c, c' => rv σ (R.chart c.1).isFrame (R.chart c'.1).isFrame
  | some a, c, c' => gv p σ (F.L a) (c.2.2 a) (c'.2.2 a)

def ph₀ : Option κ → F.Idx → CxPts p σ → ℝ
  | none, c => fun y =>
      F.φK.φ c.2.1 y + Real.log (‖rv σ (R.chart c.1).isFrame (F.K.isFrame c.2.1) y‖ ^ 2)
  | some a, c => (F.φ a).φ (c.2.2 a)

variable [DecidableEq κ] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)]

def atlas : WeightedAtlas D (CxPts p σ) F.Idx (Option κ → ℤ) :=
  freeAtlas (fun c => (F.refine.chart c).e) F.refine.cover
    (fun c c' => (F.refine.chart c).holo_trans (F.refine.chart c')) F.g₀
    (by
      rintro (_ | a) c c'
      · exact ((F.refine.chart c).holo _ _).mono fun v hv =>
          mem_ptsIn_inf.2 ⟨mem_U ((F.refine.chart c).e.map_target hv.1), mem_U hv.2⟩ |> And.intro hv.1
      · exact ((F.refine.chart c).holo _ _).mono fun v hv => mem_ptsIn_inf.2
          ⟨mem_L ((F.refine.chart c).e.map_target hv.1) a, mem_L hv.2 a⟩ |> And.intro hv.1)
    (by
      rintro (_ | a) c c' y h h'
      · exact rv_ne_zero _ _ (mem_U h) (mem_U h')
      · exact gv_ne_zero (mem_L h a) (mem_L h' a))
    (by
      rintro (_ | a) c c' c'' y h h' h''
      · exact (rv_mul _ _ _ (mem_U h) (mem_U h') (mem_U h'')).symm
      · exact (gv_mul (F.φ a).isLB (mem_L h a) (mem_L h' a) (mem_L h'' a)).symm)
    F.ph₀
    (by
      rintro (_ | a) c
      · refine ContDiffOn.add (((F.smoothK c.2.1) c.1).mono fun v hv =>
          ⟨hv.1, mem_K ((F.refine.chart c).e.map_target hv)⟩) ?_
        have hm (v) (hv : v ∈ (F.refine.chart c).e.target) := (F.refine.chart c).e.map_target hv
        exact contDiffOn_log_normSq (F.refine.chart c).e.open_target
          (((F.refine.chart c).holo _ _).mono fun v hv =>
            ⟨hv, mem_ptsIn_inf.2 ⟨mem_U (hm v hv), mem_K (hm v hv)⟩⟩)
          fun v hv => rv_ne_zero _ _ (mem_U (hm v hv)) (mem_K (hm v hv))
      · exact ((F.smooth a _) c.1).mono fun v hv =>
          ⟨hv.1, mem_L ((F.refine.chart c).e.map_target hv) a⟩)
    (by
      rintro (_ | a) c c' y h h'
      · have e₁ := rv_mul (R.chart c.1).isFrame (R.chart c'.1).isFrame (F.K.isFrame c'.2.1)
          (mem_U h) (mem_U h') (mem_K h')
        have e₂ := rv_mul (R.chart c.1).isFrame (F.K.isFrame c.2.1) (F.K.isFrame c'.2.1)
          (mem_U h) (mem_K h) (mem_K h')
        have e := (log_normSq_mul (rv_ne_zero _ _ (mem_U h) (mem_U h'))
          (rv_ne_zero _ _ (mem_U h') (mem_K h'))).symm.trans
          ((congrArg (fun z => Real.log (‖z‖ ^ 2)) (e₁.trans e₂.symm)).trans (log_normSq_mul
            (rv_ne_zero _ _ (mem_U h) (mem_K h)) (rv_ne_zero _ _ (mem_K h) (mem_K h'))))
        simp only [ph₀, g₀]
        rw [F.φK.trans _ _ y (mem_K h) (mem_K h'), gv_canon]
        linarith
      · exact (F.φ a).trans _ _ y (mem_L h a) (mem_L h' a))
    none fun c c' y h h' => rv_chart (F.refine.chart c) (F.refine.chart c') h h'

abbrev wt (a : κ) : Option κ → ℤ := Pi.single (some a) 1

theorem atlas_chart (c : F.Idx) : F.atlas.chart c = (F.refine.chart c).e := rfl

theorem atlas_kap : F.atlas.kap = Pi.single none 1 := rfl

theorem atlas_g (m : Option κ → ℤ) (c c' : F.Idx) (y : CxPts p σ) :
    F.atlas.g m c c' y = ∏ o, F.g₀ o c c' y ^ m o := rfl

theorem atlas_ph (m : Option κ → ℤ) (c : F.Idx) (y : CxPts p σ) :
    F.atlas.ph m c y = ∑ o, m o * F.ph₀ o c y := rfl

theorem atlas_g_single (o : Option κ) (c c' : F.Idx) (y : CxPts p σ) :
    F.atlas.g (Pi.single o 1) c c' y = F.g₀ o c c' y := by
  rw [atlas_g, Fintype.prod_eq_single o fun a ha => by rw [Pi.single_eq_of_ne ha, zpow_zero],
    Pi.single_eq_same, zpow_one]

theorem atlas_ph_single (o : Option κ) (c : F.Idx) (y : CxPts p σ) :
    F.atlas.ph (Pi.single o 1) c y = F.ph₀ o c y := by
  simp [atlas_ph, Pi.single_apply]

theorem atlas_g_wt (a : κ) (c c' : F.Idx) (y : CxPts p σ) :
    F.atlas.g (wt a) c c' y = gv p σ (F.L a) (c.2.2 a) (c'.2.2 a) y := F.atlas_g_single _ c c' y

theorem atlas_ph_wt (a : κ) (c : F.Idx) (y : CxPts p σ) :
    F.atlas.ph (wt a) c y = (F.φ a).φ (c.2.2 a) y := F.atlas_ph_single _ c y

theorem pos_wt {a : κ} (h : (F.φ a).SemiPos R) : F.atlas.Pos (wt a) fun _ => 0 :=
  fun c y hy ξ => by
  simp only [WeightedAtlas.leviAt, atlas_ph_wt, add_zero]
  exact h _ c.1 y ⟨hy.1, mem_L hy a⟩ ξ

theorem holoOn_iff_atlas {S : Set (CxPts p σ)} (hS : IsOpen S) {f : CxPts p σ → ℂ} :
    R.HoloOn S f ↔ ∀ c, DifferentiableOn ℂ (f ∘ (F.atlas.chart c).symm)
      ((F.atlas.chart c).target ∩ (F.atlas.chart c).symm ⁻¹' S) := holoOn_iff R F.refine hS

structure Reading (B : LB Y) (m : Option κ → ℤ) where

  isLB : B.IsLB

  u : F.Idx → B.ι → CxPts p σ → ℂ

  holo : ∀ c i, R.HoloOn ((F.atlas.chart c).source ∩ ptsIn p σ (B.U i)) (u c i)

  ne : ∀ c i y, y ∈ (F.atlas.chart c).source → y ∈ ptsIn p σ (B.U i) → u c i y ≠ 0

  compat : ∀ c c' i i' y, y ∈ (F.atlas.chart c).source → y ∈ (F.atlas.chart c').source →
    y ∈ ptsIn p σ (B.U i) → y ∈ ptsIn p σ (B.U i') →
    F.atlas.g m c c' y * u c' i' y = u c i y * gv p σ B i i' y

namespace Reading

variable {F} {A B : LB Y} {m m' : Option κ → ℤ} (r : F.Reading B m) {s t : B.ι → CxPts p σ → ℂ}

def read : (B.ι → CxPts p σ → ℂ) →ₗ[ℂ] (F.Idx → CxPts p σ → ℂ) where
  toFun s c y := r.u c (pick r.isLB y) y * s (pick r.isLB y) y
  map_add' _ _ := funext₂ fun _ _ => mul_add _ _ _
  map_smul' _ _ := funext₂ fun _ _ => mul_left_comm _ _ _

theorem g_self (m : Option κ → ℤ) (h : y ∈ (F.atlas.chart c).source) : F.atlas.g m c c y = 1 :=
  mul_left_cancel₀ (F.atlas.g_ne m c c y h h)
    ((F.atlas.g_cocycle m c c c y h h h).symm.trans (mul_one _).symm)

theorem read_eq (hs : s ∈ fibSec p σ B) (h : y ∈ (F.atlas.chart c).source) {i : B.ι}
    (hi : y ∈ ptsIn p σ (B.U i)) : r.read s c y = r.u c i y * s i y := by
  have e := r.compat c c i _ y h h hi (mem_pick r.isLB y)
  rw [g_self m h, one_mul] at e
  rw [hs.1 i _ y hi (mem_pick r.isLB y), ← mul_assoc, ← e]
  rfl

theorem isSec_read (hs : s ∈ R.holSec B) : F.atlas.IsSec m (r.read s) := by
  refine ⟨fun c => ?_, fun c c' y _ h h' => ?_⟩
  · have : R.HoloOn (F.atlas.chart c).source (r.read s c) :=
      holoOn_of_cover (fun i => isOpen_ptsIn (B.U i)) (fun y _ => ⟨_, mem_pick r.isLB y⟩) fun i =>
        ((r.holo c i).mul ((hs.2 i).mono inter_subset_right)).congr
          fun _ hy => r.read_eq hs.1 hy.1 hy.2
    exact (this.chart (F.atlas.chart c).open_source (F.refine.chart c)).mono
      fun _ hv => ⟨hv.1, (F.atlas.chart c).map_target hv.1⟩
  · have hi := mem_pick r.isLB y
    rw [r.read_eq hs.1 h hi, r.read_eq hs.1 h' hi, ← mul_assoc, r.compat c c' _ _ y h h' hi hi,
      gv_self r.isLB hi, mul_one]

theorem isSec_read_secVal (s : B.Sec) : F.atlas.IsSec m (r.read (secVal p σ s)) :=
  r.isSec_read (R.secVal_mem_holSec s)

theorem isSec_read_val (x : SecC p σ B) : F.atlas.IsSec m (r.read (SecC.val x)) :=
  r.isSec_read (R.valC B x).2

theorem eq_of_read_eq (hs : s ∈ fibSec p σ B) (ht : t ∈ fibSec p σ B)
    (h : ∀ c, ∀ y ∈ (F.atlas.chart c).source, r.read s c y = r.read t c y) : s = t := by
  funext i y
  by_cases hi : y ∈ ptsIn p σ (B.U i)
  · have hc := F.atlas.mem_pick y
    exact mul_left_cancel₀ (r.ne _ i y hc hi)
      ((r.read_eq hs hc hi).symm.trans ((h _ y hc).trans (r.read_eq ht hc hi)))
  · rw [hs.2 i y hi, ht.2 i y hi]

theorem exists_read_eq {G : F.Idx → CxPts p σ → ℂ} (hG : F.atlas.IsSec m G) :
    ∃ s ∈ R.holSec B, ∀ c, ∀ y ∈ (F.atlas.chart c).source, r.read s c y = G c y := by
  classical
  let s (i : B.ι) (y : CxPts p σ) : ℂ := if y ∈ ptsIn p σ (B.U i) then
    (r.u (F.atlas.pick y) i y)⁻¹ * G (F.atlas.pick y) y else 0
  have key {c i j y} (h : y ∈ (F.atlas.chart c).source) (hi : y ∈ ptsIn p σ (B.U i))
      (hj : y ∈ ptsIn p σ (B.U j)) : (r.u c i y)⁻¹ * G c y = gv p σ B i j y * s j y := by
    have hc := F.atlas.mem_pick y
    have e := r.compat c _ i j y h hc hi hj
    have h₁ := r.ne c i y h hi
    have h₂ := r.ne _ j y hc hj
    rw [hG.2 c _ y trivial h hc, (eq_mul_inv_iff_mul_eq₀ h₂).2 e]
    simp only [s, if_pos hj]
    field_simp
  have key' {c i y} (h : y ∈ (F.atlas.chart c).source) (hi : y ∈ ptsIn p σ (B.U i)) :
      s i y = (r.u c i y)⁻¹ * G c y := by rw [key h hi hi, gv_self r.isLB hi, one_mul]
  have hs : s ∈ fibSec p σ B := ⟨fun i j y hi hj =>
    (key' (F.atlas.mem_pick y) hi).trans (key (F.atlas.mem_pick y) hi hj), fun i y h => if_neg h⟩
  refine ⟨s, ⟨hs, fun i => holoOn_of_cover (fun c => (F.atlas.chart c).open_source)
    (fun y _ => ⟨_, F.atlas.mem_pick y⟩) fun c => ?_⟩, fun c y h => ?_⟩
  · rw [inter_comm]
    exact (((r.holo c i).inv fun y hy => r.ne c i y hy.1 hy.2).mul
      ((holoOn_of_chart (F.refine.chart c) (hG.1 c)).mono fun _ hy => ⟨hy.1, trivial⟩)).congr
      fun y hy => key' hy.1 hy.2
  · have hi := mem_pick r.isLB y
    rw [r.read_eq hs h hi, key' h hi, mul_inv_cancel_left₀ (r.ne c _ y h hi)]

def Isometric (φ : Weight p σ B) : Prop :=
  ∀ c i y, y ∈ (F.atlas.chart c).source → y ∈ ptsIn p σ (B.U i) →
    F.atlas.ph m c y = φ.φ i y + Real.log (‖r.u c i y‖ ^ 2)

variable {r} in

theorem Isometric.nsq_read {φ : Weight p σ B} (h : r.Isometric φ) (s : B.ι → CxPts p σ → ℂ)
    (y : CxPts p σ) : F.atlas.nsq m (r.read s) y = φ.nsq s y := by
  have hc := F.atlas.mem_pick y
  have hi := mem_pick r.isLB y
  rw [WeightedAtlas.nsq, h _ _ y hc hi]
  exact normSq_mul_exp (r.ne _ _ y hc hi) _ _

variable (F) in

def ofMem (a : κ) : F.Reading (F.L a) (wt a) where
  isLB := (F.φ a).isLB
  u c i := gv p σ (F.L a) (c.2.2 a) i
  holo _ _ := holoOn_ev_of_subset _ fun _ hy => mem_ptsIn_inf.2 ⟨mem_L hy.1 a, hy.2⟩
  ne _ _ _ h hi := gv_ne_zero (mem_L h a) hi
  compat c c' i i' y h h' hi hi' := by
    rw [atlas_g_wt, gv_mul (F.φ a).isLB (mem_L h a) (mem_L h' a) hi',
      gv_mul (F.φ a).isLB (mem_L h a) hi hi']

theorem read_ofMem {a : κ} {s : (F.L a).ι → CxPts p σ → ℂ} (hs : s ∈ fibSec p σ (F.L a))
    (h : y ∈ (F.atlas.chart c).source) : (ofMem F a).read s c y = s (c.2.2 a) y :=
  (hs.1 _ _ y (mem_L h a) (mem_pick _ y)).symm

theorem isometric_ofMem (a : κ) : (ofMem F a).Isometric (F.φ a) := fun c i y h hi => by
  rw [atlas_ph_wt, (F.φ a).trans _ i y (mem_L h a) hi]
  exact (sub_add_cancel _ _).symm

variable (F) in

def canon (K : CanonLB p D) : F.Reading K.bundle F.atlas.kap where
  isLB := K.isLB
  u c a := rv σ (R.chart c.1).isFrame (K.isFrame a)
  holo _ _ := holoOn_ev_of_subset _ fun _ hy => mem_ptsIn_inf.2 ⟨mem_U hy.1, hy.2⟩
  ne _ _ _ h hi := rv_ne_zero _ _ (mem_U h) hi
  compat c c' i i' y h h' hi hi' := by
    rw [atlas_kap, atlas_g_single, gv_canon, rv_mul _ _ _ (mem_U h) hi hi']
    exact rv_mul _ _ _ (mem_U h) (mem_U h') hi'

theorem isometric_canon : (canon F F.K).Isometric F.φK := fun c i y h hi => by
  have e := (log_normSq_mul (rv_ne_zero (R.chart c.1).isFrame (F.K.isFrame c.2.1) (mem_U h) (mem_K h))
    (rv_ne_zero _ (F.K.isFrame i) (mem_K h) hi)).symm.trans
    (congrArg (fun z => Real.log (‖z‖ ^ 2)) (rv_mul _ _ _ (mem_U h) (mem_K h) hi))
  refine (F.atlas_ph_single none c y).trans ?_
  rw [F.φK.trans _ i y (mem_K h) hi, gv_canon]
  simp only [ph₀, canon]
  linarith

variable (F) in

def triv : F.Reading (LB.triv Y) 0 where
  isLB := LB.isLB_triv Y
  u _ _ _ := 1
  holo _ _ _ := differentiableOn_const (1 : ℂ)
  ne _ _ _ _ _ := one_ne_zero
  compat _ _ _ _ _ _ _ hi _ := by
    rw [gv_self (LB.isLB_triv Y) hi, atlas_g]
    simp

theorem isometric_triv : (triv F).Isometric (Weight.ofFun fun _ => 0) := fun _ _ _ _ _ => by
  simp [atlas_ph, triv, Weight.ofFun]

def cast (h : m = m') : F.Reading B m' :=
  ⟨r.isLB, r.u, r.holo, r.ne, h ▸ r.compat⟩

@[simp] theorem read_cast (h : m = m') : (r.cast h).read = r.read := rfl

variable {r} in

theorem Isometric.cast {φ : Weight p σ B} (h : r.Isometric φ) (e : m = m') :
    (r.cast e).Isometric φ := by
  subst e
  exact h

def tens (r' : F.Reading A m') (r : F.Reading B m) : F.Reading (tens A B) (m' + m) where
  isLB := isLB_tens r'.isLB r.isLB
  u c i y := r'.u c i.1 y * r.u c i.2 y
  holo c i := ((r'.holo c i.1).mono (inter_subset_inter_right _ (ptsIn_mono inf_le_left))).mul
    ((r.holo c i.2).mono (inter_subset_inter_right _ (ptsIn_mono inf_le_right)))
  ne c i y h hi := mul_ne_zero (r'.ne c _ y h (mem_ptsIn_inf.1 hi).1) (r.ne c _ y h (mem_ptsIn_inf.1 hi).2)
  compat c c' i i' y h h' hi hi' := by
    rw [F.atlas.g_add _ _ _ _ _ h h', gv_tens hi hi', mul_mul_mul_comm,
      r'.compat c c' i.1 i'.1 y h h' (mem_ptsIn_inf.1 hi).1 (mem_ptsIn_inf.1 hi').1,
      r.compat c c' i.2 i'.2 y h h' (mem_ptsIn_inf.1 hi).2 (mem_ptsIn_inf.1 hi').2, mul_mul_mul_comm]

variable {r} in

theorem Isometric.tens {r' : F.Reading A m'} {ψ : Weight p σ A} {φ : Weight p σ B}
    (h' : r'.Isometric ψ) (h : r.Isometric φ) : (r'.tens r).Isometric (ψ.tens φ) :=
  fun c i y hc hi => by
  have e := mem_ptsIn_inf.1 hi
  rw [F.atlas.ph_add _ _ _ _ hc, h' c _ y hc e.1, h c _ y hc e.2]
  simp only [Reading.tens, Weight.tens, log_normSq_mul (r'.ne c _ y hc e.1) (r.ne c _ y hc e.2)]
  ring

theorem read_tens (r' : F.Reading A m') {s' : A.ι → CxPts p σ → ℂ} (hs' : s' ∈ fibSec p σ A)
    (hs : s ∈ fibSec p σ B) (h : y ∈ (F.atlas.chart c).source) :
    (r'.tens r).read (secTens s' s) c y = r'.read s' c y * r.read s c y := by
  have e := mem_ptsIn_inf.1 (mem_pick (r'.tens r).isLB y)
  rw [r'.read_eq hs' h e.1, r.read_eq hs h e.2]
  exact mul_mul_mul_comm _ _ _ _

def zpow (n : ℤ) : F.Reading (LB.LinComb B (K := PUnit) (fun _ => 𝟙 Y) fun _ => n) (n • m) where
  isLB := Semi.LB.isLB_linComb r.isLB _ _
  u c j y := r.u c (j PUnit.unit) y ^ n
  holo c j := ((r.holo c _).zpow (fun y hy => r.ne c _ y hy.1 hy.2) n).mono
    fun _ hy => ⟨hy.1, mem_pow_iff.1 hy.2⟩
  ne c j y h hj := zpow_ne_zero _ (r.ne c _ y h (mem_pow_iff.1 hj))
  compat c c' j j' y h h' hj hj' := by
    rw [gv_pow (mem_pow_iff.1 hj) (mem_pow_iff.1 hj'), ← mul_zpow,
      ← r.compat c c' _ _ y h h' (mem_pow_iff.1 hj) (mem_pow_iff.1 hj'), mul_zpow, atlas_g, atlas_g,
      ← Finset.prod_zpow]
    simp only [Pi.smul_apply, smul_eq_mul, mul_comm n, zpow_mul]

abbrev pow (n : ℕ) : F.Reading (lbPow B n) ((n : ℤ) • m) := r.zpow n

variable {r} in

theorem Isometric.zpow {φ : Weight p σ B} (h : r.Isometric φ) (n : ℤ) :
    (r.zpow n).Isometric (φ.zpow n) := fun c j y hc hj => by
  have e := h c _ y hc (mem_pow_iff.1 hj)
  rw [φ.zpow_φ n j y, show (r.zpow n).u c j y = r.u c (j PUnit.unit) y ^ n from rfl, log_normSq_zpow,
    ← mul_add, ← e, atlas_ph, atlas_ph, Finset.mul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, mul_assoc]

theorem u_mul_inv_iso {w : LB.Iso B A} (hw : w.IsGen) (h : y ∈ (F.atlas.chart c).source)
    (h' : y ∈ (F.atlas.chart c').source) {a a' : A.ι} {b b' : B.ι} (ha : y ∈ ptsIn p σ (A.U a))
    (ha' : y ∈ ptsIn p σ (A.U a')) (hb : y ∈ ptsIn p σ (B.U b)) (hb' : y ∈ ptsIn p σ (B.U b')) :
    F.atlas.g m c c' y * (r.u c' b' y * (ev p σ _ (w.s (a', b')).val y)⁻¹) =
      r.u c b y * (ev p σ _ (w.s (a, b)).val y)⁻¹ * gv p σ A a a' y := by
  have e := ev_iso_rel hw hb hb' ha ha'
  have h₁ := ev_iso_ne_zero w hb ha
  have h₂ := ev_iso_ne_zero w hb' ha'
  rw [← mul_assoc, r.compat c c' b b' y h h' hb hb', ← (mul_inv_eq_iff_eq_mul₀ h₂).2 e]
  field_simp

def ofIso (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) : F.Reading A m where
  isLB := hA
  u c a y := r.u c (pick r.isLB y) y * (ev p σ _ (w.s (a, pick r.isLB y)).val y)⁻¹
  holo c a := holoOn_of_cover (fun b => isOpen_ptsIn (B.U b)) (fun y _ => ⟨_, mem_pick r.isLB y⟩)
    fun b => (((r.holo c b).mono fun _ hy => ⟨hy.1.1, hy.2⟩).mul
      ((holoOn_ev_of_subset (w.s (a, b)).val fun _ hy => mem_ptsIn_inf.2 ⟨hy.1.2, hy.2⟩).inv
        fun _ hy => ev_iso_ne_zero w hy.2 hy.1.2)).congr fun y hy => by
      have := r.u_mul_inv_iso hw hy.1.1 hy.1.1 hy.1.2 hy.1.2 hy.2 (mem_pick r.isLB y)
      rwa [g_self m hy.1.1, gv_self hA hy.1.2, one_mul, mul_one] at this
  ne c a y h ha := mul_ne_zero (r.ne c _ y h (mem_pick _ y))
    (inv_ne_zero (ev_iso_ne_zero w (mem_pick _ y) ha))
  compat c c' a a' y h h' ha ha' := r.u_mul_inv_iso hw h h' ha ha' (mem_pick _ y) (mem_pick _ y)

variable {r} in

theorem Isometric.ofIso {φ : Weight p σ B} (h : r.Isometric φ) (hA : A.IsLB) (w : LB.Iso B A)
    (hw : w.IsGen) : (r.ofIso hA w hw).Isometric (φ.ofIso hA w hw) := fun c a y hc ha => by
  have hb := mem_pick r.isLB y
  have e := log_normSq_mul (r.ne c _ y hc hb) (inv_ne_zero (ev_iso_ne_zero w hb ha))
  rw [norm_inv, inv_pow, Real.log_inv] at e
  rw [h c _ y hc hb]
  exact Eq.symm ((congrArg (_ + ·) e).trans (by simp only [Weight.ofIso, Weight.ofPairs]; ring))

variable {r} in

theorem Isometric.topDens_eq {φ : Weight p σ B} (h : r.Isometric φ) (K : CanonLB p D)
    {f : (CechPic.tens K.bundle B).ι → CxPts p σ → ℂ} (hf : f ∈ R.holSec (CechPic.tens K.bundle B))
    (hy : y ∈ (F.atlas.chart c).source) : (F.refine.chart c).topDens K φ f y =
      2 ^ D * (F.atlas.nsq (F.atlas.kap + m) (((canon F K).tens r).read f) y *
        Real.exp (F.atlas.ph F.atlas.kap c y)) := by
  have ha := mem_pick K.isLB y
  have hb := mem_pick φ.isLB y
  rw [F.atlas.nsq_eq_chart (isSec_read _ hf) hy, read_eq _ hf.1 hy (i := (_, _))
    (mem_ptsIn_inf.2 ⟨ha, hb⟩), F.atlas.ph_add _ _ _ _ hy, mul_assoc (_ ^ 2), ← Real.exp_add,
    neg_add_rev, neg_add_cancel_right, h c _ y hy hb, AlgChart.topDens,
    ← normSq_mul_exp (r.ne c _ y hy hb)]
  congr 4
  exact (mul_assoc _ _ _).symm.trans (congrArg (· * _) (mul_comm _ _))

variable {r} in

theorem Isometric.topMeasure_eq {φ : Weight p σ B} (h : r.Isometric φ) (K : CanonLB p D)
    {f : (CechPic.tens K.bundle B).ι → CxPts p σ → ℂ} (hf : f ∈ R.holSec (CechPic.tens K.bundle B)) :
    R.topMeasure K φ f = F.atlas.mu.withDensity fun y =>
      ENNReal.ofReal (2 ^ D * F.atlas.nsq (F.atlas.kap + m) (((canon F K).tens r).read f) y) := by
  refine ext_of_cover _ (fun c => (F.atlas.chart c).open_source)
    (fun y => ⟨_, F.atlas.mem_pick y⟩) fun c A hA hc => ?_
  have hm := (ENNReal.continuous_ofReal.comp ((continuous_const (y := (2 : ℝ) ^ D)).mul
    (F.atlas.continuous_nsq (isSec_read ((canon F K).tens r) hf)))).measurable.indicator hA
  have e := ap_lintegral_chart F.atlas c _ hm
  rw [lintegral_indicator hA, Measure.restrict_restrict hA, inter_eq_left.2 hc] at e
  have hi := measurableSet_image (F.atlas.chart c) hA hc
  rw [withDensity_apply _ hA, R.topMeasure_apply K φ f (F.refine.chart c) hA hc]
  refine Eq.trans ?_ e.symm
  have hsub : F.atlas.chart c '' A ⊆ (F.atlas.chart c).target :=
    image_subset_iff.2 fun _ hz => (F.atlas.chart c).map_source (hc hz)
  rw [← atlas_chart, ← inter_eq_left.2 hsub, ← Measure.restrict_restrict hi, ← lintegral_indicator hi]
  refine setLIntegral_congr_fun (F.atlas.chart c).open_target.measurableSet fun v hv => ?_
  have hv' := (F.atlas.chart c).map_target hv
  by_cases hvA : (F.atlas.chart c).symm v ∈ A
  · rw [indicator_of_mem (show v ∈ _ '' A from ⟨_, hvA, (F.atlas.chart c).right_inv hv⟩)]
    simp only [indicator_of_mem hvA, Function.comp_apply, Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity) (F.atlas.nsq_nonneg _ _ _)), mul_assoc]
    exact congrArg _ (h.topDens_eq K hf hv')
  · rw [indicator_of_notMem, indicator_of_notMem hvA, zero_mul]
    rintro ⟨z, hz, rfl⟩
    exact hvA (((F.atlas.chart c).left_inv (hc hz)).symm ▸ hz)

variable {r} in

theorem Isometric.topInt_eq {φ : Weight p σ B} (h : r.Isometric φ) (K : CanonLB p D)
    {f : (CechPic.tens K.bundle B).ι → CxPts p σ → ℂ} (hf : f ∈ R.holSec (CechPic.tens K.bundle B)) :
    R.topInt K φ f = 2 ^ D * ∫⁻ y, ENNReal.ofReal
      (F.atlas.nsq (F.atlas.kap + m) (((canon F K).tens r).read f) y) ∂F.atlas.mu := by
  rw [topInt, h.topMeasure_eq K hf, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_congr fun y => ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]

end Reading

end WeightFamily

namespace CxPts

variable (σ)

theorem t2Space_cxPts_of_isProjOver (h : IsProjOver p) : T2Space (CxPts p σ) := by
  obtain ⟨N, i, _, rfl⟩ := h
  have := isProper_str k N
  infer_instance

theorem secondCountableTopology_of_isProjOver (h : IsProjOver p) :
    SecondCountableTopology (CxPts p σ) := by
  obtain ⟨N, i, _, rfl⟩ := h
  have := isProper_str k N
  infer_instance

end CxPts

namespace ProjAn

open ProjSpace

variable (k σ) (N : ℕ)

instance smooth : SmoothOfRelativeDimension N (PSpace.str k N) :=
  Adelic.smoothOfRelativeDimension_pspace k N

instance proper : IsProper (PSpace.str k N) := isProper_str k N

instance compact : CompactSpace (CxPts (PSpace.str k N) σ) := compactSpace_pSpace σ N

def fsO1 : Weight (PSpace.str k N) σ (O1 k N) :=
  Weight.fsBasis _ σ (O1_isLB k N) (coord k N) (iSup_nonzeroLocus_coord k N) 1 (by simp)

theorem fubiniStudyWeight_projPoint (v : Unimodular ℂ N) (i : Fin (N + 1)) (hi : v.1 i ≠ 0) :
    (fsO1 k σ N).φ i (projPt σ v) = Real.log (∑ a, ‖v.1 a / v.1 i‖ ^ 2) := by
  refine (Weight.fsBasis_φ _ _ _ _ _ _ _).trans (congrArg _ (Finset.sum_congr rfl fun a _ => ?_))
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rw [div_eq_mul_inv, ← Ring.inverse_eq_inv, ← valR_pt_ratio σ v.1 v.2 hi.isUnit a]
  rfl

variable (K : CanonLB (PSpace.str k N) N)

theorem noCommonZero_jac : Weight.NoCommonZero fun _ : Unit =>
    secVal (PSpace.str k N) σ (K.jacSec (coord k N)) :=
  fun c _ h => ⟨(), ev_ne_zero h (isUnit_jacSec_coord k N K c)⟩

def canonWeight : Weight (PSpace.str k N) σ K.bundle :=
  Weight.cancel K.isLB (Weight.fs (K.isLB_adj (O1_isLB k N) _) _ (fun _ => secVal_mem _)
    (noCommonZero_jac k σ N K)) ((fsO1 k σ N).pow (N + 1))

def family (R : AnRead (PSpace.str k N) σ N) : WeightFamily R Unit where
  K := K
  φK := canonWeight k σ N K
  smoothK := Weight.IsSmooth.cancel _
    (Weight.isSmooth_fs _ (fun _ => R.secVal_mem_holSec _) (noCommonZero_jac k σ N K))
    ((Weight.isSmooth_fsBasis _ _ _ _ _).zpow _)
  L _ := O1 k N
  φ _ := fsO1 k σ N
  smooth _ := Weight.isSmooth_fsBasis _ _ _ _ _

def atlas : WeightedAtlas N (CxPts (PSpace.str k N) σ)
    (family k σ N (.all _ _) (.all _ σ N)).Idx (Option Unit → ℤ) :=
  (family k σ N (.all _ _) (.all _ σ N)).atlas

example (R : AnRead (PSpace.str k N) σ N) (y : CxPts (PSpace.str k N) σ) :
    let F := family k σ N K R
    let w := fun a => (WeightFamily.Reading.ofMem F ()).read (secVal _ σ (coord k N a))
    (∀ a, F.atlas.IsSec (WeightFamily.wt ()) (w a)) ∧ F.atlas.sqn (WeightFamily.wt ()) w y = 1 := by
  intro F w
  refine ⟨fun a => WeightFamily.Reading.isSec_read_secVal _ _, ?_⟩
  have e (a) : Weight.combVal (PSpace.str k N) σ (coord k N) 1 a = secVal _ σ (coord k N a) := by
    simp [Weight.combVal, Matrix.one_apply]
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) (Weight.sum_nsq_fs (hB := O1_isLB k N)
    (he := fun a => e a ▸ secVal_mem _)
    (h := Weight.noCommonZero_combVal (iSup_nonzeroLocus_coord k N) (M := 1) (by simp)) y)
  rw [e]
  exact (WeightFamily.Reading.isometric_ofMem (F := F) ()).nsq_read _ y

example (R : AnRead (PSpace.str k N) σ N) :
    R.topInt K ((fsO1 k σ N).pow (N + 1)) (secVal _ σ (K.jacSec (coord k N))) < ⊤ :=
  AnRead.topInt_lt_top K ((Weight.isSmooth_fsBasis _ _ _ _ _).zpow _) (R.secVal_mem_holSec _)

end ProjAn

example (R : AnRead (CanonLB.affStr k D) σ D) (y : CxPts (CanonLB.affStr k D) σ) :
    ∃ c : AlgChart (CanonLB.affStr k D) σ D, y ∈ c.e.source ∧
      (∀ z ∈ c.e.source, ∀ a, c.e z a = ev _ σ ⊤ (CanonLB.polyFn (MvPolynomial.X a)) z) ∧
      ∀ A, MeasurableSet A → A ⊆ c.e.source →
        R.topMeasure (CanonLB.affineSpace k D) (Weight.ofFun fun _ => 0) (fun _ _ => 1) A =
          2 ^ D * volume (c.e '' A) := by
  have he : MvPolynomial.eval₂Hom (algX (CanonLB.affStr k D) ⊤)
      (fun a => CanonLB.polyFn (MvPolynomial.X a)) = CanonLB.polyFn :=
    MvPolynomial.ringHom_ext (fun a => (MvPolynomial.eval₂Hom_C _ _ a).trans
      (RingHom.congr_fun (CanonLB.polyFn_comp k D) a).symm) fun a => MvPolynomial.eval₂Hom_X' _ _ a
  have het : (MvPolynomial.eval₂Hom (algX (CanonLB.affStr k D) ⊤)
      (fun a => CanonLB.polyFn (MvPolynomial.X a))).Etale := by
    rw [he]
    exact RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin D) k))).inv)
  obtain ⟨⟨e, U, hU, x, hx, h₁, h₂, h₃⟩, hy, hU', hx'⟩ := AlgChart.exists_of_etale
    (isAffineOpen_top _) _ het (mem_ptsIn_top (y := y))
  dsimp only at hU'
  subst hU'
  dsimp only at hx'
  subst hx'
  have : Smooth (CanonLB.affStr k D) := SmoothOfRelativeDimension.smooth D _
  refine ⟨_, hy, h₂, fun A hA h => ?_⟩
  rw [R.topMeasure_apply _ _ _ _ hA h, ← setLIntegral_const]
  refine lintegral_congr fun v => ?_
  have hr (z : CxPts (CanonLB.affStr k D) σ) :
      rv σ (CanonLB.isFrame_dX k D) (CanonLB.isFrame_dX k D) z = 1 :=
    (congrFun (gv_canon (CanonLB.affineSpace k D) PUnit.unit PUnit.unit) z).symm.trans
      (gv_self (CanonLB.affineSpace k D).isLB mem_ptsIn_top)
  have : (2 : ℝ≥0∞) ^ D = ENNReal.ofReal (2 ^ D * (‖(1 : ℂ) * 1‖ ^ 2 * Real.exp (-0))) := by
    simp [ENNReal.ofReal_pow]
  rw [this]
  exact congrArg (fun z : ℂ => ENNReal.ofReal (2 ^ D * (‖z * 1‖ ^ 2 * Real.exp (-0)))) (hr (e.symm v))

end GlobalTheory

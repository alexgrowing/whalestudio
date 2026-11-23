import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSmoothA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.VeryCuspZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffOnInvReal

noncomputable section

open NumberField MeasureTheory Filter Topology Metric Set
open GlobalTheory.CuspRep
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PositivityTheory.Rg.BcB.CG.SmoothIntegrals

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

abbrev gI (v : InfinitePlace E) : GA E n →* G n := Matrix.GeneralLinearGroup.map (PositivityTheory.Rg.BcB.cV v)

theorem continuous_pInf₀ : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_gI (v : InfinitePlace E) : Continuous (gI (n := n) v : GA E n → G n) :=
  Continuous.units_map _ (continuous_id.matrix_map ((continuous_apply v).comp continuous_pInf₀))

theorem continuous_infGL₀ : Continuous (infGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))))

theorem gI_infGL_val (v : InfinitePlace E) (u : GL (Fin n) (Cinf E)) :
    (gI v (infGL E n u)).val = fun i j => u.val i j v := by
  ext i j
  exact congrArg (fun y : GL (Fin n) (Cinf E) => y.val i j v) (pInf_infGL (E := E) (a := n) u)

omit [NumberField E] [IsTotallyComplex E] in
theorem isOpen_GLs₀ : IsOpen (GLs n) :=
  isOpen_ne.preimage (Continuous.matrix_det continuous_id)

omit [NumberField E] [IsTotallyComplex E] in
theorem val_mem_GLs₀ (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

omit [NumberField E] [IsTotallyComplex E] in

def xv (v : InfinitePlace E) (x : Lie E n) : Mat n := fun i j => x i j v

omit [IsTotallyComplex E] in
theorem contDiff_xv (v : InfinitePlace E) : ContDiff ℝ ∞ (xv (n := n) v) :=
  contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
    (contDiff_apply ℝ ℂ v).comp ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ i))

omit [NumberField E] [IsTotallyComplex E] in
theorem contDiffAt_matMul {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {f g : X → Mat n} {x : X}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) : ContDiffAt ℝ ∞ (fun y => f y * g y) x := by
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun k _ =>
    (contDiffAt_pi.1 (contDiffAt_pi.1 hf i) k).mul (contDiffAt_pi.1 (contDiffAt_pi.1 hg k) j)

open Classical in
omit [NumberField E] [IsTotallyComplex E] in

def uOf (x : Lie E n) : GL (Fin n) (Cinf E) := if h : IsUnit (Matrix.of x) then h.unit else 1

omit [NumberField E] [IsTotallyComplex E] in
theorem uOf_val {x : Lie E n} (hx : x ∈ invSet E n) : (uOf x).val = Matrix.of x := by
  have h : IsUnit (Matrix.of x) := hx
  rw [uOf, dif_pos h]
  rfl

theorem chart_eq {φ : GA E n → ℂ} {g : GA E n} {x : Lie E n} (hx : x ∈ invSet E n) :
    chart φ g x = φ (g * infGL E n (uOf x)) := by
  have h : IsUnit (Matrix.of x) := hx
  rw [chart, dif_pos h, uOf, dif_pos h]

omit [IsTotallyComplex E] in
theorem continuousOn_uOf : ContinuousOn (uOf (E := E) (n := n)) (invSet E n) := by
  rw [continuousOn_iff_continuous_domRestrict]
  show Continuous fun x : invSet E n => uOf x.1
  have hv : Continuous fun x : invSet E n => (Matrix.of x.1 : Matrix (Fin n) (Fin n) (Cinf E)) :=
    continuous_subtype_val
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have e : (Units.val ∘ fun x : invSet E n => uOf x.1) = fun x => Matrix.of x.1 :=
      funext fun x => uOf_val x.2
    rw [e]
    exact hv
  · have e : (fun x : invSet E n => ((uOf x.1)⁻¹ : GL (Fin n) (Cinf E)).val) =
        fun x => Ring.inverse (Matrix.of x.1).det • (Matrix.of x.1).adjugate := funext fun x => by
      rw [Matrix.coe_units_inv, uOf_val x.2, Matrix.inv_def]
    rw [e]
    refine Continuous.smul (M := Cinf E) ?_ (Continuous.matrix_adjugate hv)
    refine continuous_iff_continuousAt.2 fun x => ?_
    have hu : IsUnit (Matrix.of x.1).det := (Matrix.isUnit_iff_isUnit_det _).1 x.2
    exact ContinuousAt.comp (f := fun x : invSet E n => (Matrix.of x.1).det) (g := Ring.inverse)
      (NormedRing.inverse_continuousAt (R := Cinf E) hu.unit) (Continuous.matrix_det hv).continuousAt

theorem xv_eq {x : Lie E n} (hx : x ∈ invSet E n) (v : InfinitePlace E) :
    (gI v (infGL E n (uOf x))).val = xv v x := by
  rw [gI_infGL_val, uOf_val hx]
  rfl

theorem xv_mem {x : Lie E n} (hx : x ∈ invSet E n) (v : InfinitePlace E) : xv v x ∈ GLs n := by
  rw [← xv_eq hx v]
  exact val_mem_GLs₀ _

omit [NumberField E] [IsTotallyComplex E] in
theorem inv_mul_mem {A B : Mat n} (hA : A ∈ GLs n) (hB : B ∈ GLs n) : A⁻¹ * B ∈ GLs n := by
  show (A⁻¹ * B).det ≠ 0
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact mul_ne_zero (inv_ne_zero hA) hB

def kerQ (κ : InfinitePlace E → Mat n → ℂ) (q : Lie E n × ((InfinitePlace E → Mat n) × ℂ)) : ℂ :=
  (∏ v, κ v ((xv v q.1)⁻¹ * q.2.1 v)) * q.2.2

def Wset (E : Type) [Field E] [NumberField E] (n : ℕ) : Set ((InfinitePlace E → Mat n) × ℂ) :=
  (Set.univ.pi fun _ => GLs n) ×ˢ Set.univ

omit [IsTotallyComplex E] in
theorem isOpen_Wset : IsOpen (Wset E n) :=
  (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_GLs₀).prod isOpen_univ

theorem contDiffOn_kerQ {κ : InfinitePlace E → Mat n → ℂ} (hκ : ∀ v, ContDiffOn ℝ ∞ (κ v) (GLs n)) :
    ContDiffOn ℝ ∞ (kerQ κ) (invSet E n ×ˢ Wset E n) := by
  rintro ⟨x, m, b⟩ ⟨hx, hm, -⟩
  refine ContDiffAt.contDiffWithinAt ?_
  refine (contDiffAt_prod fun v _ => ?_).mul (contDiff_snd.comp contDiff_snd).contDiffAt
  have hinv : ContDiffAt ℝ ∞ (fun q : Lie E n × ((InfinitePlace E → Mat n) × ℂ) => (xv v q.1)⁻¹) (x, m, b) :=
    ContDiffAt.comp (g := fun A : Mat n => A⁻¹) (f := fun q : Lie E n × ((InfinitePlace E → Mat n) × ℂ) => xv v q.1)
      (x, m, b) (GlobalTheory.CompanionTheory.WaveCp.Rep.Frame.contDiffOn_inv_real.contDiffAt (isOpen_GLs₀.mem_nhds (xv_mem hx v)))
      ((contDiff_xv v).comp contDiff_fst).contDiffAt
  have hmv : ContDiffAt ℝ ∞ (fun q : Lie E n × ((InfinitePlace E → Mat n) × ℂ) => q.2.1 v) (x, m, b) :=
    ((contDiff_apply ℝ (Mat n) v).comp (contDiff_fst.comp contDiff_snd)).contDiffAt
  exact ContDiffAt.comp (g := κ v)
    (f := fun q : Lie E n × ((InfinitePlace E → Mat n) × ℂ) => (xv v q.1)⁻¹ * q.2.1 v) (x, m, b)
    ((hκ v).contDiffAt (isOpen_GLs₀.mem_nhds (inv_mul_mem (xv_mem hx v) (hm v trivial))))
    (contDiffAt_matMul (f := fun q : Lie E n × ((InfinitePlace E → Mat n) × ℂ) => (xv v q.1)⁻¹)
      (g := fun q : Lie E n × ((InfinitePlace E → Mat n) × ℂ) => q.2.1 v) hinv hmv)

variable {T : Type} [TopologicalSpace T] [Group T] [IsTopologicalGroup T] [T2Space T] [MeasurableSpace T]
  [BorelSpace T]

theorem mem_Sm_conv (μ : Measure T) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (ι : GA E n →* T) (hι : Continuous ι) (ρ : T → GA E n) (hρ : Continuous ρ)
    (hρι : ∀ h w, ρ (ι h * w) = h * ρ w)
    (κ : InfinitePlace E → Mat n → ℂ) (hκ : ∀ v, ContDiffOn ℝ ∞ (κ v) (GLs n))
    (C : T → ℂ) (hC : Continuous C) (hCι : ∀ u w, C (ι (infGL E n u) * w) = C w)
    (F : T → ℂ) (hF : Continuous F) (Φ : T → ℂ) (hΦ : ∀ w, Φ w = (∏ v, κ v (gI v (ρ w)).val) * C w)
    (hΦc : HasCompactSupport Φ) (t₀ : T) :
    (fun x' => ∫ y, Φ y * F (t₀ * ι x' * y) ∂μ) ∈ Sm E n := by
  refine fun g => ?_
  let p : T → (InfinitePlace E → Mat n) × ℂ := fun y =>
    (fun v => (gI v (ρ ((t₀ * ι g)⁻¹ * y))).val, C ((t₀ * ι g)⁻¹ * y) * F y)
  have hp : Continuous p := by
    have hl : Continuous fun y : T => (t₀ * ι g)⁻¹ * y := continuous_const.mul continuous_id
    exact (continuous_pi fun v => Units.continuous_val.comp ((continuous_gI v).comp (hρ.comp hl))).prodMk
      ((hC.comp hl).mul hF)
  have hpW : ∀ y, p y ∈ Wset E n := fun y => ⟨fun v _ => val_mem_GLs₀ _, trivial⟩
  have key : ∀ x ∈ invSet E n, ∀ y,
      kerQ κ (x, p y) = Φ ((ι (infGL E n (uOf x)))⁻¹ * ((t₀ * ι g)⁻¹ * y)) * F y := by
    intro x hx y
    rw [hΦ, ← map_inv ι, ← map_inv (infGL E n), hρι, hCι, mul_assoc]
    show (∏ v, κ v ((xv v x)⁻¹ * (gI v (ρ ((t₀ * ι g)⁻¹ * y))).val)) * (C ((t₀ * ι g)⁻¹ * y) * F y) = _
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_mul, map_inv, map_inv, Units.val_mul, Matrix.coe_units_inv, xv_eq hx v]
  have hsupp : ∀ x ∈ invSet E n, ∃ K, IsCompact K ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ K, kerQ κ (x', p y) = 0 := by
    intro x₀ hx₀
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 isOpen_invSet x₀ hx₀
    have hS : closedBall x₀ (r / 2) ⊆ invSet E n := (closedBall_subset_ball (half_lt_self hr)).trans hrU
    let L : Lie E n × T → T := fun q => t₀ * ι g * ι (infGL E n (uOf q.1)) * q.2
    refine ⟨L '' (closedBall x₀ (r / 2) ×ˢ tsupport Φ),
      ((isCompact_closedBall x₀ (r / 2)).prod hΦc).image_of_continuousOn ?_, ?_⟩
    · have hu : ContinuousOn (fun q : Lie E n × T => ι (infGL E n (uOf q.1))) (closedBall x₀ (r / 2) ×ˢ tsupport Φ) :=
        (hι.comp continuous_infGL₀).comp_continuousOn
          (continuousOn_uOf.comp continuous_fst.continuousOn fun q hq => hS hq.1)
      exact (continuousOn_const.mul hu).mul continuous_snd.continuousOn
    · filter_upwards [closedBall_mem_nhds x₀ (half_pos hr)] with x' hx' y hy
      rw [key x' (hS hx') y]
      have hw : (ι (infGL E n (uOf x')))⁻¹ * ((t₀ * ι g)⁻¹ * y) ∉ tsupport Φ := by
        intro hw
        apply hy
        refine ⟨(x', _), ⟨hx', hw⟩, ?_⟩
        simp only [L, mul_assoc, mul_inv_rev, mul_inv_cancel_left]
      rw [image_eq_zero_of_notMem_tsupport hw, zero_mul]
  refine (contDiffOn_integral (μ := μ) isOpen_invSet isOpen_Wset hp hpW (contDiffOn_kerQ hκ) hsupp).congr ?_
  intro x hx
  rw [chart_eq hx]
  have h2 := integral_mul_left_eq_self (μ := μ)
    (fun y => Φ ((t₀ * ι (g * infGL E n (uOf x)))⁻¹ * y) * F y) (t₀ * ι (g * infGL E n (uOf x)))
  simp only [inv_mul_cancel_left] at h2
  rw [h2]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  beta_reduce
  rw [key x hx y]
  simp only [map_mul, mul_inv_rev, mul_assoc]

end PositivityTheory.Rg.BcB.CG.SmoothIntegrals

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt
open GlobalTheory.VBExt (AdaptedChart)
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.MixDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D d : ℕ}

def part (ρ : AlgChart p σ D → CxPts p σ → ℝ) : Measure (CxPts p σ) :=
  ChartGlue.glueMeas (fun c : AlgChart p σ D => c.e) fun c y => ENNReal.ofReal (ρ c y)

def IsDens (ρ : AlgChart p σ D → CxPts p σ → ℝ) : Prop :=
  (∀ (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
    ρ c y = ‖ChartGlue.transDet c.e c'.e y‖ ^ 2 * ρ c' y) ∧
  ∀ c : AlgChart p σ D, ContinuousOn (fun v => ρ c (c.e.symm v)) c.e.target

def total (ρ : AlgChart p σ D → CxPts p σ → ℝ) : ℝ :=
  (part ρ univ).toReal - (part (fun c y => -ρ c y) univ).toReal

theorem total_eq_curve (ρ : AlgChart p σ 1 → CxPts p σ → ℝ) :
    part ρ = CurveDens.part ρ ∧ total ρ = CurveDens.total ρ ∧ (IsDens ρ ↔ CurveDens.IsDens ρ) := ⟨rfl, rfl, Iff.rfl⟩

private theorem chartMeas_congr_source' {n : ℕ} {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z]
    (e : OpenPartialHomeomorph Z (V n)) {f g : Z → ENNReal} (h : ∀ y ∈ e.source, f y = g y) :
    ChartGlue.chartMeas e f = ChartGlue.chartMeas e g := by
  unfold ChartGlue.chartMeas
  congr 1
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem e.open_target.measurableSet] with v hv
  exact h _ (e.map_target hv)

variable {ρ ρ' : AlgChart p σ D → CxPts p σ → ℝ}

theorem part_congr (h : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ρ c y = ρ' c y) : part ρ = part ρ' := by
  unfold part ChartGlue.glueMeas
  exact iSup_congr fun c => chartMeas_congr_source' _ fun y hy => congrArg ENNReal.ofReal (h c y hy)

theorem total_congr (h : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ρ c y = ρ' c y) : total ρ = total ρ' := by
  have h' : part (fun c y => -ρ c y) = part (fun c y => -ρ' c y) :=
    part_congr fun c y hy => by rw [h c y hy]
  unfold total
  rw [part_congr h, h']

theorem part_eq_zero (h : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ρ c y ≤ 0) : part ρ = 0 := by
  have h0 : ∀ c : AlgChart p σ D, ChartGlue.chartMeas c.e (fun y => ENNReal.ofReal (ρ c y)) = 0 := by
    intro c
    rw [chartMeas_congr_source' c.e (g := fun _ => 0) fun y hy => ENNReal.ofReal_eq_zero.2 (h c y hy)]
    show Measure.map _ ((volume.restrict c.e.target).withDensity 0) = 0
    rw [withDensity_zero, Measure.map_zero]
  unfold part ChartGlue.glueMeas
  exact le_antisymm (iSup_le fun c => (h0 c).le) (Measure.zero_le _)

theorem total_zero : total (fun (_ : AlgChart p σ D) _ => 0) = 0 := by
  have h1 : part (fun (_ : AlgChart p σ D) (_ : CxPts p σ) => (0 : ℝ)) = 0 := part_eq_zero fun _ _ _ => le_rfl
  simp [total, h1]

theorem IsDens.part_apply [SecondCountableTopology (CxPts p σ)] (h : IsDens ρ) (c : AlgChart p σ D)
    {T : Set (CxPts p σ)} (hT : MeasurableSet T) (hc : T ⊆ c.e.source) :
    part ρ T = ∫⁻ v in c.e '' T, ENNReal.ofReal (ρ c (c.e.symm v)) := by
  unfold part
  rw [ChartGlue.glueMeas_apply _ _ (fun c c' => AlgChart.holo_trans c c') ?_ c hT hc]
  · exact ChartGlue.chartMeas_apply_of_subset _ _ hT hc
  · intro c c' y hy hy'
    rw [h.1 c c' y hy hy', ENNReal.ofReal_mul (by positivity)]

theorem isDens_zero : IsDens fun (_ : AlgChart p σ D) _ => 0 := ⟨fun _ _ _ _ _ => by simp, fun _ => continuousOn_const⟩

theorem IsDens.add (h : IsDens ρ) (h' : IsDens ρ') : IsDens fun c y => ρ c y + ρ' c y := ⟨fun c c' y hy hy' => by beta_reduce; rw [h.1 c c' y hy hy', h'.1 c c' y hy hy']; ring,
  fun c => (h.2 c).add (h'.2 c)⟩

theorem IsDens.sub (h : IsDens ρ) (h' : IsDens ρ') : IsDens fun c y => ρ c y - ρ' c y := ⟨fun c c' y hy hy' => by beta_reduce; rw [h.1 c c' y hy hy', h'.1 c c' y hy hy']; ring,
  fun c => (h.2 c).sub (h'.2 c)⟩

theorem IsDens.mul (h : IsDens ρ) {f : CxPts p σ → ℝ} (hf : Continuous f) : IsDens fun c y => f y * ρ c y := ⟨fun c c' y hy hy' => by beta_reduce; rw [h.1 c c' y hy hy']; ring,
  fun c => (hf.comp_continuousOn c.e.continuousOn_symm).mul (h.2 c)⟩

theorem IsDens.sum {J : Type} (s : Finset J) {τ : J → AlgChart p σ D → CxPts p σ → ℝ} (h : ∀ j, IsDens (τ j)) :
    IsDens fun c y => ∑ j ∈ s, τ j c y := by
  refine ⟨fun c c' y hy hy' => ?_, fun c => continuousOn_finset_sum s fun j _ => (h j).2 c⟩
  beta_reduce
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => (h j).1 c c' y hy hy'

theorem IsDens.congr (h : IsDens ρ) (e : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ρ' c y = ρ c y) : IsDens ρ' := ⟨fun c c' y hy hy' => by rw [e c y hy, e c' y hy']; exact h.1 c c' y hy hy',
  fun c => (h.2 c).congr fun v hv => e c _ (c.e.map_target hv)⟩

theorem chernPart_eq {B : LB X} (φ : Weight p σ B) :
    φ.chernPart D 1 = part (fun (c : AlgChart p σ D) y => c.chernDens φ y) ∧
      φ.chernPart D (-1) = part fun (c : AlgChart p σ D) y => -c.chernDens φ y := by
  constructor <;> simp [Weight.chernPart, part]

def transMat (c c' : AlgChart p σ D) (y : CxPts p σ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun a b => fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (EuclideanSpace.single b 1) a

theorem det_transMat (c c' : AlgChart p σ D) (y : CxPts p σ) :
    (transMat c c' y).det = ChartGlue.transDet c.e c'.e y := by
  unfold transMat ChartGlue.transDet
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin D) ℂ).toBasis]
  congr 1

def IsForm (M : AlgChart p σ D → CxPts p σ → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  (∀ (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
    M c y = chg (transMat c c' y) (M c' y)) ∧
  (∀ c : AlgChart p σ D, ContinuousOn (fun v => M c (c.e.symm v)) c.e.target) ∧
  ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, (M c y).IsHermitian

def formMat (α : V D → V D → ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun j l => α (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) / kappa

def mix (d : ℕ) (A M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) : ℝ :=
  d.factorial / Real.pi ^ (d + 1) * (A.adjugate * M).trace.re

variable {A M M' J : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}

theorem mix_self : mix d A A = (d + 1).factorial / Real.pi ^ (d + 1) * A.det.re := by
  unfold mix
  rw [Matrix.adjugate_mul, Matrix.trace_smul, Matrix.trace_one]
  simp [Nat.factorial_succ, smul_eq_mul]
  ring

theorem mix_add : mix d A (M + M') = mix d A M + mix d A M' := by
  simp only [mix, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  ring

theorem mix_smul (t : ℝ) : mix d A ((t : ℂ) • M) = t * mix d A M := by
  simp only [mix, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  ring

theorem mix_sum {I : Type} (s : Finset I) (N : I → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    mix d A (∑ i ∈ s, N i) = ∑ i ∈ s, mix d A (N i) := by
  simp only [mix, Finset.mul_sum, Matrix.trace_sum, Complex.re_sum]

theorem mix_chg : mix d (chg J A) (chg J M) = ‖J.det‖ ^ 2 * mix d A M := by
  have h1 : (Jᵀ).adjugate * Jᵀ = J.det • (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
    rw [Matrix.adjugate_mul, Matrix.det_transpose]
  have h2 : Jᴴᵀ * (Jᴴᵀ).adjugate = star J.det • (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
    rw [Matrix.mul_adjugate, Matrix.det_transpose, Matrix.det_conjTranspose]
  have key : ((chg J A).adjugate * chg J M).trace = ((‖J.det‖ ^ 2 : ℝ) : ℂ) * (A.adjugate * M).trace := by
    unfold chg
    rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]
    calc ((Jᴴᵀ).adjugate * (A.adjugate * (Jᵀ).adjugate) * (Jᵀ * M * Jᴴᵀ)).trace
        = ((Jᴴᵀ).adjugate * (A.adjugate * ((Jᵀ).adjugate * Jᵀ) * M) * Jᴴᵀ).trace := by
          simp only [Matrix.mul_assoc]
      _ = (Jᴴᵀ * ((Jᴴᵀ).adjugate * (A.adjugate * ((Jᵀ).adjugate * Jᵀ) * M))).trace :=
          Matrix.trace_mul_comm _ _
      _ = ((Jᴴᵀ * (Jᴴᵀ).adjugate) * (A.adjugate * ((Jᵀ).adjugate * Jᵀ) * M)).trace :=
          congrArg Matrix.trace (Matrix.mul_assoc _ _ _).symm
      _ = ((‖J.det‖ ^ 2 : ℝ) : ℂ) * (A.adjugate * M).trace := by
          rw [h1, h2]
          simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.trace_smul,
            smul_eq_mul]
          rw [← mul_assoc, Complex.ofReal_pow, ← Complex.conj_mul', mul_comm J.det]
          rfl
  unfold mix
  rw [key, Complex.re_ofReal_mul]
  ring

theorem mix_diagonal (a m : Fin (d + 1) → ℝ) :
    mix d (diagonal fun j => (a j : ℂ)) (diagonal fun j => (m j : ℂ)) =
      d.factorial / Real.pi ^ (d + 1) * ∑ j, m j * ∏ l ∈ Finset.univ.erase j, a l := by
  unfold mix
  simp only [Matrix.adjugate_diagonal, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [← Complex.ofReal_prod, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

theorem IsForm.sum {I : Type} (s : Finset I) {N : I → AlgChart p σ D → CxPts p σ → Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ i, IsForm (N i)) : IsForm fun c y => ∑ i ∈ s, N i c y := by
  refine ⟨fun c c' y hy hy' => ?_, fun c => continuousOn_finset_sum s fun i _ => (h i).2.1 c,
    fun c y hy => ?_⟩
  · simp only [chg, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (h i).1 c c' y hy hy'
    simpa [chg] using this
  · show (∑ i ∈ s, N i c y)ᴴ = ∑ i ∈ s, N i c y
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun i _ => (h i).2.2 c y hy

theorem IsForm.isDens_mix {A M : AlgChart p σ (d + 1) → CxPts p σ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hA : IsForm A) (hM : IsForm M) : IsDens fun c y => mix d (A c y) (M c y) := by
  refine ⟨fun c c' y hy hy' => ?_, fun c => ?_⟩
  · have e1 := hA.1 c c' y hy hy'
    have e2 := hM.1 c c' y hy hy'
    show mix d (A c y) (M c y) = ‖ChartGlue.transDet c.e c'.e y‖ ^ 2 * mix d (A c' y) (M c' y)
    rw [← det_transMat, e1, e2]
    exact mix_chg
  · have hc : ContinuousOn (fun v => (A c (c.e.symm v), M c (c.e.symm v))) c.e.target :=
      (hA.2.1 c).prodMk (hM.2.1 c)
    have hg : Continuous fun q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ × Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
        mix d q.1 q.2 := by
      unfold mix
      fun_prop
    have hgc := hg.comp_continuousOn hc
    exact hgc

def chernMat {B : LB X} (φ : Weight p σ B) (c : AlgChart p σ D) (y : CxPts p σ) : Matrix (Fin D) (Fin D) ℂ :=
  c.hess φ (pick φ.isLB y) y

theorem chernMat_congr {L N : HermLB p} (e : L.Isometric N) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : chernMat (L.φ σ) c y = chernMat (N.φ σ) c y := by
  unfold chernMat
  exact (e.hess_eq c hy (mem_pick _ y) (mem_pick _ y)).symm

def bcMat {S : ShortComplex X.Modules} {r s : ℕ} (h : Met p σ S.X₂ (r + s)) (hS : S.ShortExact)
    (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (c : AlgChart p σ D) (y : CxPts p σ) : Matrix (Fin D) (Fin D) ℂ :=
  formMat (h.bcForm (Met.exists_adapted hS h₁ h₃ y).choose c y)

theorem mix_bcMat {S : ShortComplex X.Modules} {r s : ℕ} (h : Met p σ S.X₂ (r + s)) (hS : S.ShortExact)
    (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (c : AlgChart p σ 1) (y : CxPts p σ) (A : Matrix (Fin 1) (Fin 1) ℂ) :
    mix 0 A (bcMat h hS h₁ h₃ c y) = h.bcDens hS h₁ h₃ c y := by
  rw [mix, Matrix.adjugate_fin_one, Matrix.one_mul]
  unfold Met.bcDens bcMat formMat
  rw [Matrix.trace_fin_one]
  simp only [Matrix.of_apply, diagVal, kappa]
  rw [div_div_eq_mul_div, Complex.div_I]
  simp [Complex.mul_re, Complex.mul_im]
  field_simp

section Flag

variable {E : X.Modules} {r : ℕ} (h : VMetric p E r) (fl : Vert.Flag E r)

def flagMat (σ : k →+* ℂ) (c : AlgChart p σ D) (y : CxPts p σ) : Matrix (Fin D) (Fin D) ℂ :=
  ∑ i, bcMat ((h.stepMet fl i).met σ) (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) c y

def flagDens (N : HermLB p) (d : ℕ) (σ : k →+* ℂ) (c : AlgChart p σ (d + 1)) (y : CxPts p σ) : ℝ :=
  mix d (chernMat (N.φ σ) c y) (flagMat h fl σ c y)

def bcPair (N : HermLB p) (d : ℕ) : ℝ := ∑ᶠ σ, total (flagDens h fl N d σ)

theorem bcPair_congr {L N : HermLB p} (e : L.Isometric N) (d : ℕ) : bcPair h fl L d = bcPair h fl N d := by
  unfold bcPair
  refine finsum_congr fun σ => total_congr fun c y hy => ?_
  simp only [flagDens, chernMat_congr e c hy]

end Flag

def Compare [IsIntegral X] {E : X.Modules} {r : ℕ} {h : VMetric p E r} (H : h.IsCInf) (d : ℕ) (fl fl' : Vert.Flag E r) :
    Prop :=
  ∀ (κ : Type) [Fintype κ] (L : κ → HermLB p) (Φ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ), IsArFun L (d + 1) Φ →
    ∀ x x' : Fin r → κ, (∀ i, (L (x i)).Isometric (VMetric.grLB fl i H)) →
      (∀ i, (L (x' i)).Isometric (VMetric.grLB fl' i H)) → ∀ n : κ → ℤ,
        Φ ((∑ i, MvPolynomial.X (x i) ^ 2 - ∑ i, MvPolynomial.X (x' i) ^ 2) * lin (fun j => (n j : ℝ)) ^ d) =
          bcPair h fl (comb L n) d - bcPair h fl' (comb L n) d

section Cell

variable {ι : Type} [Fintype ι] {r : ι → ℕ} (e : Fin (d + 1) ≃ Option (Σ a, Low (r a)))

def base (v : V (d + 1)) : V 1 := EuclideanSpace.single 0 (v (e.symm none))

def fib (v : V (d + 1)) (a : ι) : Low (r a) → ℂ := fun s => v (e.symm (some ⟨a, s⟩))

def pt (z : V 1) (n : ∀ a, Low (r a) → ℂ) : V (d + 1) :=
  WithLp.toLp 2 fun j => (e j).elim (z 0) fun s => n s.1 s.2

omit [Fintype ι] in

theorem base_pt (z : V 1) (n : ∀ a, Low (r a) → ℂ) : base e (pt e z n) = z := by
  unfold base pt
  ext i
  fin_cases i
  simp

omit [Fintype ι] in

theorem fib_pt (z : V 1) (n : ∀ a, Low (r a) → ℂ) : fib e (pt e z n) = n := by
  funext a s
  simp [fib, pt]

def emb {m : ℕ} (i : Fin m) : Fin i ⊕ Fin 1 → Fin m := Sum.elim (Fin.castLE i.isLt.le) fun _ => i

def stepGram (G : ∀ a, V 1 → Matrix (Fin (r a)) (Fin (r a)) ℂ) (a : ι) (i : Fin (r a)) (v : V (d + 1)) :
    Matrix (Fin i ⊕ Fin 1) (Fin i ⊕ Fin 1) ℂ :=
  (chg (uni (fib e v a)) (G a (base e v))).submatrix (emb i) (emb i)

def rootWt (G : ∀ a, V 1 → Matrix (Fin (r a)) (Fin (r a)) ℂ) (z : Σ a, Fin (r a)) (v : V (d + 1)) : ℝ :=
  -Real.log (quotGram (stepGram e G z.1 z.2 v)).det.re

open Classical in

def rootDiag (θ : (Σ a, Fin (r a)) → ℝ) (z : Σ a, Fin (r a)) (s : Option (Σ a, Low (r a))) : ℝ :=
  s.elim (θ z) fun t => (if z = ⟨t.1, t.2.1.1⟩ then 1 else 0) - if z = ⟨t.1, t.2.1.2⟩ then 1 else 0

open Classical in

def bcDiag (a : ι) (s : Option (Σ a, Low (r a))) : ℝ := s.elim 0 fun t => if t.1 = a then 1 else 0

def baseDiag (s : Option (Σ a, Low (r a))) : ℝ := s.elim 1 fun _ => 0

def vdm (r : ι → ℕ) : MvPolynomial (Σ a, Fin (r a)) ℝ :=
  ∏ a, ∏ i : Fin (r a), ∏ i' ∈ Finset.Ioi i,
    (MvPolynomial.X (⟨a, i'⟩ : Σ a, Fin (r a)) - MvPolynomial.X ⟨a, i⟩)

variable {m : ℕ}

def jacDens (G : Matrix (Fin m) (Fin m) ℂ) (n : Low m → ℂ) : ℝ := dens Gᵀ n * G.det.re ^ (m - 1)

def logMinorDer (G K : Matrix (Fin m) (Fin m) ℂ) (n : Low m → ℂ) (j : Fin (m + 1)) : ℝ :=
  (((chg (uni n) G).submatrix (Fin.castLE (Nat.le_of_lt_succ j.isLt)) (Fin.castLE (Nat.le_of_lt_succ j.isLt)))⁻¹ *
    (chg (uni n) K).submatrix (Fin.castLE (Nat.le_of_lt_succ j.isLt)) (Fin.castLE (Nat.le_of_lt_succ j.isLt))).trace.re

def theta (G K : Matrix (Fin m) (Fin m) ℂ) (n : Low m → ℂ) (i : Fin m) : ℝ :=
  logMinorDer G K n i.castSucc - logMinorDer G K n i.succ

variable {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)

def IsCell (c : AlgChart q σ 1) (c' : AlgChart p σ (d + 1)) : Prop :=
  c'.e.source = PtsOver.map π w (spMap σ) ⁻¹' c.e.source ∩ ptsIn p σ c'.U ∧
    c'.e.target = {v | base e v ∈ c.e.target} ∧
    ∀ y ∈ c'.e.source, base e (c'.e y) = c.e (PtsOver.map π w (spMap σ) y)

def IsCellFrame (c' : AlgChart p σ (d + 1)) (a : ι) {E : B.Modules} (h : VMetric q E (r a))
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) (r a)) (cE : Chart E (r a)) : Prop :=
  ∀ i, ∃ ac : AdaptedChart (VMetric.stepSeq fl i) i 1, ∀ y ∈ c'.e.source, y ∈ ptsIn p σ ac.U ∧
    (((h.pull π w).stepMet fl i).met σ).gram ac.frame y =
      (chg (uni (fib e (c'.e y) a)) ((h.met σ).G cE (PtsOver.map π w (spMap σ) y))).submatrix (emb i) (emb i)

end Cell

end GlobalTheory.MixDens

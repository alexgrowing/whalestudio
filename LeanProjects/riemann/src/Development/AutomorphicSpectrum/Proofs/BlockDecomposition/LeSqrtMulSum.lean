import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerToL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LTLTInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsRepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLpTwoOfCpt

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.WaveCp.Rep

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Calculus

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Ld_contDiffOn (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Ld X f) (GLs n) :=
  GlobalTheory.CompanionTheory.RCalc.contDiffOn_fderiv_field GlobalTheory.CompanionTheory.RCalc.isOpen_GLs hf (GlobalTheory.CompanionTheory.RCalc.mulL X)

theorem Lw_contDiffOn (w : List (Bool × Fin n × Fin n)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Lw w f) (GLs n) := by
  induction w with
  | nil => simpa using hf
  | cons p w ih => rw [Lw_cons]; exact Ld_contDiffOn _ ih

theorem Ld_congr (X : Mat n) {f h : Mat n → V} (e : Set.EqOn f h (GLs n)) : Set.EqOn (Ld X f) (Ld X h) (GLs n) := by
  intro g hg
  have : f =ᶠ[nhds g] h := Filter.eventuallyEq_of_mem (GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg) e
  simp [Ld, this.fderiv_eq]

theorem Lw_congr (w : List (Bool × Fin n × Fin n)) {f h : Mat n → V} (e : Set.EqOn f h (GLs n)) :
    Set.EqOn (Lw w f) (Lw w h) (GLs n) := by
  induction w with
  | nil => simpa using e
  | cons p w ih => rw [Lw_cons, Lw_cons]; exact Ld_congr _ ih

theorem Ld_cpt (X : Mat n) {f : Mat n → V} (hf : Cpt f) : Cpt (Ld X f) := by
  obtain ⟨R, hR⟩ := hf
  refine ⟨R, fun y hy hl => ?_⟩
  have hc : ContinuousAt (lg : Mat n → ℝ) y :=
    GlobalTheory.CompanionTheory.KerUniq.continuousOn_lg.continuousAt (GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hy)
  have h1 : ∀ᶠ g in nhds y, g ∈ GLs n ∧ R < lg g :=
    (GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.eventually_mem hy).and (hc.eventually (lt_mem_nhds hl))
  have h2 : f =ᶠ[nhds y] 0 := h1.mono fun g hg => hR g hg.1 hg.2
  simp [Ld, h2.fderiv_eq]

theorem Lw_cpt (w : List (Bool × Fin n × Fin n)) {f : Mat n → V} (hf : Cpt f) : Cpt (Lw w f) := by
  induction w with
  | nil => simpa using hf
  | cons p w ih => rw [Lw_cons]; exact Ld_cpt _ ih

theorem Lw_append (w w' : List (Bool × Fin n × Fin n)) (f : Mat n → V) : Lw (w ++ w') f = Lw w (Lw w' f) := by
  simp [Lw, List.foldr_append]

end Calculus

def co (p : Bool × Fin n × Fin n) : Mat n →L[ℝ] ℝ :=
  (if p.1 then Complex.reCLM else Complex.imCLM).comp
    (LinearMap.toContinuousLinearMap
      ((Matrix.entryLinearMap ℝ ℂ p.2.1 p.2.2 : Mat n →ₗ[ℝ] ℂ)))

theorem sum_co_bs (Y : Mat n) : ∑ p, co p Y • bs p = Y := by
  ext a b
  rw [Matrix.sum_apply, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Fintype.sum_prod_type]
  simp [co, bs, Matrix.single_apply, Finset.sum_add_distrib]
  have e : ∀ F : Fin n → Fin n → ℂ, (∑ x, ∑ x_1, if x = a ∧ x_1 = b then F x x_1 else 0) = F a b := by
    intro F
    rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp
    · intro c _ hc
      simp [hc]
    · simp
    · intro c _ hc
      simp [hc]
    · simp
  rw [e (fun x y => ((Y x y).re : ℂ)), e (fun x y => ((Y x y).im : ℂ) * Complex.I)]
  exact Complex.re_add_im _

section Conv

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

def cvl (φ : Mat n → ℂ) (y : Lp V 2 μ) : Mat n → V :=
  fun x => ∫ z : G n, φ (x * (z⁻¹ : G n).val) • (y : G n → V) z ∂μ

def CB (φ : Mat n → ℂ) (y : Lp V 2 μ) : Lp V 2 μ := ∫ z : G n, φ z.val • LT μ z y ∂μ

end Conv

section Classes

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [MeasurableSpace (G n)] {μ : Measure (G n)}

theorem isRep_congr {b b' : Mat n → V} {y : Lp V 2 μ} (e : Set.EqOn b b' (GLs n)) (h : IsRep μ b y) : IsRep μ b' y := by
  unfold IsRep at *
  filter_upwards [h] with g hg
  rw [hg]
  exact e (GlobalTheory.CompanionTheory.KerUniq.val_mem g)

theorem isRep_memLp {b : Mat n → V} {y : Lp V 2 μ} (h : IsRep μ b y) : MemLp (fun g : G n => b g.val) 2 μ :=
  (memLp_congr_ae h).1 (Lp.memLp y)

theorem isRep_toL {b : Mat n → V} {y : Lp V 2 μ} (h : IsRep μ b y) : toL μ b = y :=
  Lp.ext ((toL_coe (isRep_memLp h)).trans h.symm)

theorem isRep_limit {Y : ℕ → Lp V 2 μ} {Y' : Lp V 2 μ} {h : ℕ → Mat n → V} {h' : Mat n → V}
    (hY : Filter.Tendsto Y Filter.atTop (nhds Y')) (hr : ∀ j, IsRep μ (h j) (Y j))
    (hp : ∀ x ∈ GLs n, Filter.Tendsto (fun j => h j x) Filter.atTop (nhds (h' x))) : IsRep μ h' Y' := by
  have hm : TendstoInMeasure μ (fun j => (Y j : G n → V)) Filter.atTop (Y' : G n → V) :=
    tendstoInMeasure_of_tendsto_Lp hY
  obtain ⟨ns, hmono, hns⟩ := hm.exists_seq_tendsto_ae
  have hall : ∀ᵐ g ∂μ, ∀ j, (Y j : G n → V) g = h j g.val := ae_all_iff.2 hr
  unfold IsRep
  filter_upwards [hns, hall] with g h1 h2
  have h3 := (hp g.val (GlobalTheory.CompanionTheory.KerUniq.val_mem g)).comp hmono.tendsto_atTop
  refine tendsto_nhds_unique h1 (h3.congr fun j => (h2 (ns j)).symm)

end Classes

theorem le_sqrt_mul_sum {ι : Type} {S : Finset ι} {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) {t C : ℝ} (ht : 0 ≤ t)
    (h : t ^ 2 ≤ C * ∑ i ∈ S, a i ^ 2) : t ≤ Real.sqrt (max C 0) * ∑ i ∈ S, a i := by
  have h0 : 0 ≤ ∑ i ∈ S, a i := Finset.sum_nonneg fun i _ => ha i
  have h1 : ∑ i ∈ S, a i ^ 2 ≤ (∑ i ∈ S, a i) ^ 2 := by
    rw [sq (∑ i ∈ S, a i), Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => ha j) hi) (ha i)
  have h2 : t ^ 2 ≤ max C 0 * (∑ i ∈ S, a i) ^ 2 := by
    have h3 : 0 ≤ ∑ i ∈ S, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    calc t ^ 2 ≤ C * ∑ i ∈ S, a i ^ 2 := h
      _ ≤ max C 0 * ∑ i ∈ S, a i ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) h3
      _ ≤ max C 0 * (∑ i ∈ S, a i) ^ 2 := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
  have h4 : (Real.sqrt (max C 0) * ∑ i ∈ S, a i) ^ 2 = max C 0 * (∑ i ∈ S, a i) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_max_right _ _)]
  exact abs_le_of_sq_le_sq' (h4 ▸ h2) (mul_nonneg (Real.sqrt_nonneg _) h0) |>.2

end GlobalTheory.CompanionTheory.WaveCp.Rep

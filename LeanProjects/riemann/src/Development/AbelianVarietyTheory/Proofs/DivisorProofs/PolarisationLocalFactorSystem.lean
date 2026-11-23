import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicLogOnConvexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCocycleCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFactorHolomorphicSolutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveCocycleLocalTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveCocycleNormalizedTrivialStatement

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.FactorThetaChar

theorem per_add {g : ℕ} (t : Matrix (Fin g) (Fin g) ℂ) (x y : Fl g) :
    per t (x + y) = per t x + per t y := by
  ext i
  simp only [per, Pi.add_apply, Matrix.vecMul, dotProduct, Complex.ofReal_add, add_mul,
    Finset.sum_add_distrib]
  ring

theorem transl_transl {g : ℕ} {E : Type} (τ : E → Matrix (Fin g) (Fin g) ℂ) (x y : Fl g)
    (P : Pt E g) : transl τ x (transl τ y P) = transl τ (x + y) P := by
  simp only [transl, per_add]
  congr 1
  abel

theorem differentiableOn_transl {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap U τ) (x : Fl g) :
    DifferentiableOn ℂ (transl τ x) (cov U g) := by
  have hd : ∀ i k, DifferentiableOn ℂ (fun P : Pt E g => τ P.1 i k) (cov U g) := fun i k =>
    (hτ.2.1 i k).comp differentiableOn_fst fun P hP => hP.1
  refine differentiableOn_fst.prodMk (differentiableOn_snd.add ?_)
  refine differentiableOn_pi.2 fun i => ?_
  simp only [per, Pi.add_apply, Matrix.vecMul, dotProduct]
  exact (DifferentiableOn.fun_sum fun k _ => (hd k i).const_mul _).add_const _

theorem core_of {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (QCOB : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ → ∀ H : Fl g → Pt E g → ℂ, (∀ l ∈ stdLat g, DifferentiableOn ℂ (H l) (cov U g)) → (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov U g, H (l + l') P = H l (transl τ l' P) + H l' P) → ∀ b ∈ U, ∃ V : Set E, IsOpen V ∧ b ∈ V ∧ V ⊆ U ∧ ∃ K : Pt E g → ℂ, DifferentiableOn ℂ K (cov V g) ∧ ∀ i : Fin g, ∀ P ∈ cov V g, H (Pi.single (Sum.inr i) (1 : ℝ)) P = K (transl τ (Pi.single (Sum.inr i) (1 : ℝ)) P) - K P) (PCORE : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ → ∀ H : Fl g → Pt E g → ℂ, (∀ l ∈ stdLat g, DifferentiableOn ℂ (H l) (cov U g)) → (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov U g, H (l + l') P = H l (transl τ l' P) + H l' P) → (∀ i : Fin g, ∀ P ∈ cov U g, H (Pi.single (Sum.inr i) (1 : ℝ)) P = 0) → ∀ b ∈ U, ∃ V : Set E, IsOpen V ∧ b ∈ V ∧ V ⊆ U ∧ ∃ K : Pt E g → ℂ, DifferentiableOn ℂ K (cov V g) ∧ ∃ μ : Fl g → E → ℂ, (∀ l ∈ stdLat g, DifferentiableOn ℂ (μ l) V) ∧ (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ b' ∈ V, μ (l + l') b' = μ l b' + μ l' b') ∧ ∀ l ∈ stdLat g, ∀ P ∈ cov V g, H l P = K (transl τ l P) - K P + μ l P.1) : ∀ {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ → ∀ H : Fl g → Pt E g → ℂ, (∀ l ∈ stdLat g, DifferentiableOn ℂ (H l) (cov U g)) → (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov U g, H (l + l') P = H l (transl τ l' P) + H l' P) → ∀ b ∈ U, ∃ V : Set E, IsOpen V ∧ b ∈ V ∧ V ⊆ U ∧ ∃ K : Pt E g → ℂ, DifferentiableOn ℂ K (cov V g) ∧ ∃ μ : Fl g → E → ℂ, (∀ l ∈ stdLat g, DifferentiableOn ℂ (μ l) V) ∧ (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ b' ∈ V, μ (l + l') b' = μ l b' + μ l' b') ∧ ∀ l ∈ stdLat g, ∀ P ∈ cov V g, H l P = K (transl τ l P) - K P + μ l P.1 := by
  intro U τ hτ H hHd hHc b hb
  obtain ⟨V1, hV1o, hbV1, hV1U, K1, hK1d, hK1⟩ := QCOB hτ H hHd hHc b hb
  have hτ1 : IsPeriodMap V1 τ :=
    ⟨hV1o, fun i k => (hτ.2.1 i k).mono hV1U, fun b' hb' => hτ.2.2 b' (hV1U hb')⟩
  have hcov1 : cov V1 g ⊆ cov U g := fun P hP => ⟨hV1U hP.1, trivial⟩
  have hmaps : ∀ l : Fl g, Set.MapsTo (transl τ l) (cov V1 g) (cov V1 g) :=
    fun l P hP => ⟨hP.1, trivial⟩
  obtain ⟨V, hVo, hbV, hVV1, K2, hK2d, μ, hμd, hμa, hK2⟩ := PCORE hτ1
    (fun l P => H l P - (K1 (transl τ l P) - K1 P))
    (fun l hl => ((hHd l hl).mono hcov1).sub
      ((hK1d.comp (differentiableOn_transl hτ1 l) (hmaps l)).sub hK1d))
    (fun l hl l' hl' P hP => by
      have h1 := hHc l hl l' hl' P (hcov1 hP)
      rw [h1, transl_transl]
      ring)
    (fun i P hP => by
      rw [hK1 i P hP]
      ring) b hbV1
  refine ⟨V, hVo, hbV, hVV1.trans hV1U, fun P => K1 P + K2 P, hK1d.mono
    (fun P hP => ⟨hVV1 hP.1, trivial⟩) |>.add hK2d, μ, hμd, hμa, fun l hl P hP => ?_⟩
  have := hK2 l hl P hP
  dsimp only at this ⊢
  linear_combination this

theorem exists_iso_theta_mul_char : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ j : Fl g → Pt E g → ℂ, IsFactor B τ (stdLat g) j → InducesPolarisation B τ (stdLat g) j → ∀ b ∈ B, ∃ U : Set E, IsOpen U ∧ b ∈ U ∧ U ⊆ B ∧ ∃ χ : Fl g → E → ℂ, (∀ l ∈ stdLat g, DifferentiableOn ℂ (χ l) U ∧ ∀ b' ∈ U, χ l b' ≠ 0) ∧ (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ b' ∈ U, χ (l + l') b' = χ l b' * χ l' b') ∧ ∃ φ, IsBundleIso U τ (stdLat g) j (fun l P => Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2) * χ l P.1) φ := by
  intro g E _ _ _ B τ hτ j hj hpol b hb
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hτ.1 b hb
  have hU0o : IsOpen (Metric.ball b r) := Metric.isOpen_ball
  have hU0c : Convex ℝ (Metric.ball b r) := convex_ball b r
  have hbU0 : b ∈ Metric.ball b r := Metric.mem_ball_self hr
  have hcovc : Convex ℝ (cov (Metric.ball b r) g) := hU0c.prod convex_univ
  have hcovo : IsOpen (cov (Metric.ball b r) g) := hU0o.prod isOpen_univ
  have hcovB : cov (Metric.ball b r) g ⊆ cov B g := fun P hP => ⟨hball hP.1, trivial⟩
  have h2pi : (2 * π * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hT := (theta_factor hτ).1.1
  have hL : ∀ l ∈ stdLat g, ∃ G : Pt E g → ℂ, DifferentiableOn ℂ G (cov (Metric.ball b r) g) ∧
      ∀ P ∈ cov (Metric.ball b r) g,
        j l P = Complex.exp (2 * π * Complex.I * (thetaExp (τ P.1) l P.2 + G P)) := by
    intro l hl
    obtain ⟨L, hLd, hLe⟩ := GlobalTheory.T.holomorphic_log_on_convex hcovc hcovo
      (fun P => j l P * (Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2))⁻¹)
      (((hj.1 l hl).1.mul ((hT l hl).1.inv fun P hP => (hT l hl).2 P hP)).mono hcovB)
      (fun P hP => mul_ne_zero ((hj.1 l hl).2 P (hcovB hP)) (inv_ne_zero ((hT l hl).2 P (hcovB hP))))
    refine ⟨fun P => L P * (2 * π * Complex.I)⁻¹, hLd.mul_const _, fun P hP => ?_⟩
    have e := hLe P hP
    have hne := (hT l hl).2 P (hcovB hP)
    rw [show j l P = (j l P * (Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2))⁻¹) *
      Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2) by rw [inv_mul_cancel_right₀ hne],
      e, mul_add, Complex.exp_add, show 2 * π * Complex.I * (L P * (2 * π * Complex.I)⁻¹) = L P by
        field_simp, mul_comm]
  choose! G hGd hGe using hL
  obtain ⟨c, hcs, hcc, hcG⟩ := GlobalTheory.T.theta_factor_holomorphic_solution hτ j hj hpol hU0o hU0c ⟨b, hbU0⟩ hball G
    (fun l hl => ⟨hGd l hl, hGe l hl⟩)
  obtain ⟨a, ha⟩ := GlobalTheory.T.lattice_cocycle_coboundary c hcs hcc
  have hτU0 : IsPeriodMap (Metric.ball b r) τ :=
    ⟨hU0o, fun i k => (hτ.2.1 i k).mono hball, fun b' hb' => hτ.2.2 b' (hball hb')⟩
  obtain ⟨V, hVo, hbV, hVU, K, hKd, μ, hμd, hμa, hHK⟩ := core_of GlobalTheory.T.additive_cocycle_local_trivial GlobalTheory.T.additive_cocycle_normalized_trivial hτU0
    (fun l P => G l P - (a l : ℂ)) (fun l hl => (hGd l hl).sub_const _)
    (fun l hl l' hl' P hP => by
      rw [hcG l hl l' hl' P hP, ha l hl l' hl']
      push_cast
      ring) b hbU0
  have hcovV : cov V g ⊆ cov (Metric.ball b r) g := fun P hP => ⟨hVU hP.1, trivial⟩
  refine ⟨V, hVo, hbV, hVU.trans hball, fun l b' => Complex.exp (2 * π * Complex.I * μ l b'),
    fun l hl => ⟨((hμd l hl).const_mul _).cexp, fun _ _ => Complex.exp_ne_zero _⟩,
    fun l hl l' hl' b' hb' => by dsimp only; rw [hμa l hl l' hl' b' hb', mul_add, Complex.exp_add],
    fun P => Complex.exp (-(2 * π * Complex.I * K P)), ⟨(hKd.const_mul _).neg.cexp,
      fun _ _ => Complex.exp_ne_zero _, fun l hl P hP => ?_⟩⟩
  have e1 := hGe l hl P (hcovV hP)
  have e2 := hHK l hl P hP
  have hG : G l P = K (transl τ l P) - K P + μ l P.1 + (a l : ℂ) := by
    rw [← e2]; ring
  dsimp only
  rw [e1, hG, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
    Complex.exp_eq_exp_iff_exists_int]
  exact ⟨a l, by ring⟩

end GlobalTheory.FactorThetaChar

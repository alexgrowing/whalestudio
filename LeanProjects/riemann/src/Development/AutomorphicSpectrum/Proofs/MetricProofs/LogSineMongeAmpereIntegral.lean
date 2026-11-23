import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffAtFrameEntry
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMongeAmpereNormalizedStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHolomorphicNormalFrameStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalUnitaryNormalFrame2x2Statement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralNormSqMobDMulCompMobStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MobiusChangeOfVariablesPairStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticAtMobiusDetJacobianEqStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MobiusPairAnalyticDetJacobianEqStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

theorem analyticAt_entry {D d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) {T : (Fin D → ℂ) → (Fin d → ℂ)} {z₀ : Fin D → ℂ}
    (hT : AnalyticAt ℂ T z₀) (p q : Fin 2) : AnalyticAt ℂ (fun z => g (T z) p q) z₀ :=
  AnalyticAt.comp' (ReciprocityTheory.AnForm.Osgood.osgood d Set.univ _ isOpen_univ (hg p q).differentiableOn (T z₀) (Set.mem_univ _)) hT

theorem analyticAt_coord {D : ℕ} (i : Fin D) (z₀ : Fin D → ℂ) : AnalyticAt ℂ (fun z : Fin D → ℂ => z i) z₀ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt z₀

theorem analyticAt_den {D d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) {T : (Fin D → ℂ) → (Fin d → ℂ)} {z₀ : Fin D → ℂ}
    (hT : AnalyticAt ℂ T z₀) (i : Fin D) : AnalyticAt ℂ (fun z => den (g (T z)) (z i)) z₀ :=
  (analyticAt_entry g hg hT 0 0).add ((analyticAt_entry g hg hT 0 1).mul (analyticAt_coord i z₀))

theorem analyticAt_det {D d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) {T : (Fin D → ℂ) → (Fin d → ℂ)} {z₀ : Fin D → ℂ}
    (hT : AnalyticAt ℂ T z₀) : AnalyticAt ℂ (fun z => (g (T z)).det) z₀ := by
  simp only [Matrix.det_fin_two]
  exact ((analyticAt_entry g hg hT 0 0).mul (analyticAt_entry g hg hT 1 1)).sub
    ((analyticAt_entry g hg hT 0 1).mul (analyticAt_entry g hg hT 1 0))

theorem analyticAt_mob {D d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) {T : (Fin D → ℂ) → (Fin d → ℂ)} {z₀ : Fin D → ℂ}
    (hT : AnalyticAt ℂ T z₀) (i : Fin D) (hd : den (g (T z₀)) (z₀ i) ≠ 0) :
    AnalyticAt ℂ (fun z => mob (g (T z)) (z i)) z₀ :=
  ((analyticAt_entry g hg hT 1 0).add ((analyticAt_entry g hg hT 1 1).mul (analyticAt_coord i z₀))).div
    (analyticAt_den g hg hT i) hd

theorem analyticAt_mobD {D d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) {T : (Fin D → ℂ) → (Fin d → ℂ)} {z₀ : Fin D → ℂ}
    (hT : AnalyticAt ℂ T z₀) (i : Fin D) (hd : den (g (T z₀)) (z₀ i) ≠ 0) :
    AnalyticAt ℂ (fun z => mobD (g (T z)) (z i)) z₀ :=
  (analyticAt_det g hg hT).div ((analyticAt_den g hg hT i).pow 2) (pow_ne_zero 2 hd)

theorem xiPot_frame (G g : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) (hg : IsUnit g.det) (a : ℂ) (hd : den g a ≠ 0) :
    xiPot (gᴴ * G * g) a = xiPot G (mob g a) + Real.log ‖mobD g a‖ := by
  have h := (GlobalTheory.T.log_sine_mobius_transform G g hG hg).2.1 a hd
  have hn : ‖g.det‖ ≠ 0 := norm_ne_zero_iff.2 hg.ne_zero
  have hn2 : ‖den g a‖ ≠ 0 := norm_ne_zero_iff.2 hd
  have e : Real.log ‖mobD g a‖ = Real.log ‖g.det‖ - 2 * Real.log ‖den g a‖ := by
    rw [mobD, norm_div, norm_pow, Real.log_div hn (pow_ne_zero 2 hn2), Real.log_pow]
    norm_num
  rw [h, e]
  simp only [mob, den]
  ring

theorem hess_xi {D d : ℕ} (G g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) {T : (Fin D → ℂ) → (Fin d → ℂ)}
    {z₀ : Fin D → ℂ} (hT : AnalyticAt ℂ T z₀) (i : Fin D) (hG : ∀ᶠ y' in 𝓝 (T z₀), (G y').PosDef)
    (hC : ∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) (T z₀)) (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q)
    (hu : IsUnit (g (T z₀)).det) (hd : den (g (T z₀)) (z₀ i) ≠ 0) :
    ContDiffAt ℝ 2 (fun z => xiPot ((g (T z))ᴴ * G (T z) * g (T z)) (z i)) z₀ ∧
    ContDiffAt ℝ 2 (fun z => xiPot (G (T z)) (mob (g (T z)) (z i))) z₀ ∧
    hessC (fun z => xiPot ((g (T z))ᴴ * G (T z) * g (T z)) (z i)) z₀ =
      hessC (fun z => xiPot (G (T z)) (mob (g (T z)) (z i))) z₀ := by
  have hT2 : ContDiffAt ℝ 2 T z₀ := (hT.contDiffAt (n := 2)).restrict_scalars ℝ
  have hco : ContDiffAt ℝ 2 (fun z : Fin D → ℂ => z i) z₀ := ((analyticAt_coord i z₀).contDiffAt (n := 2)).restrict_scalars ℝ
  have hm2 : ContDiffAt ℝ 2 (fun z => mob (g (T z)) (z i)) z₀ :=
    ((analyticAt_mob g hg hT i hd).contDiffAt (n := 2)).restrict_scalars ℝ
  have hpd0 : (G (T z₀)).PosDef := hG.self_of_nhds
  have hCT : ∀ p q, ContDiffAt ℝ 2 (fun z => G (T z) p q) z₀ := fun p q => (hC p q).comp z₀ hT2
  have h2 : ContDiffAt ℝ 2 (fun z => xiPot (G (T z)) (mob (g (T z)) (z i))) z₀ :=
    contDiffAt_xiPot (fun z => G (T z)) _ z₀ hpd0 hCT hm2
  have h1 : ContDiffAt ℝ 2 (fun z => xiPot ((g (T z))ᴴ * G (T z) * g (T z)) (z i)) z₀ := by
    refine contDiffAt_xiPot (fun z => (g (T z))ᴴ * G (T z) * g (T z)) _ z₀ (GlobalTheory.T.log_sine_mobius_transform _ _ hpd0 hu).1 ?_ hco
    intro p q
    exact (contDiffAt_frame_entry G g (T z₀) hC hg p q).comp z₀ hT2
  refine ⟨h1, h2, ?_⟩
  have hmd : mobD (g (T z₀)) (z₀ i) ≠ 0 := div_ne_zero hu.ne_zero (pow_ne_zero 2 hd)
  rw [← ReciprocityTheory.AnForm.A.hessC_add_log_norm _ _ z₀ h2 (analyticAt_mobD g hg hT i hd) hmd]
  apply ReciprocityTheory.AnForm.A.hessC_congr'
  have e1 : ∀ᶠ z in 𝓝 z₀, (G (T z)).PosDef := hT.continuousAt.eventually hG
  have e2 : ∀ᶠ z in 𝓝 z₀, (g (T z)).det ≠ 0 := (analyticAt_det g hg hT).continuousAt.eventually_ne hu.ne_zero
  have e3 : ∀ᶠ z in 𝓝 z₀, den (g (T z)) (z i) ≠ 0 := (analyticAt_den g hg hT i).continuousAt.eventually_ne hd
  filter_upwards [e1, e2, e3] with z h1 h2 h3
  exact xiPot_frame _ _ h1 (isUnit_iff_ne_zero.2 h2) _ h3

theorem maDens_congr_hess {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ r, hessC (φ r) z = hessC (ψ r) z) : maDens φ z = maDens ψ z := by
  simp only [maDens, h]

theorem analyticAt_tail {d : ℕ} (z₀ : Fin (d + 1) → ℂ) : AnalyticAt ℂ (fun z : Fin (d + 1) → ℂ => Fin.tail z) z₀ :=
  (ContinuousLinearMap.pi (R := ℂ) fun i : Fin d =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i.succ).analyticAt z₀

theorem analyticAt_tail2 {d : ℕ} (z₀ : Fin (d + 2) → ℂ) :
    AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => Fin.tail (Fin.tail z)) z₀ :=
  AnalyticAt.comp' (analyticAt_tail (Fin.tail z₀)) (analyticAt_tail z₀)

end GlobalTheory.CompanionTheory.Ar.PB.FibPt

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

theorem contDiffAt_xi_coord {D d : ℕ} (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) {T : (Fin D → ℂ) → (Fin d → ℂ)}
    {z₀ : Fin D → ℂ} (hT : AnalyticAt ℂ T z₀) (i : Fin D) (hpd : (G (T z₀)).PosDef)
    (hC : ∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) (T z₀)) :
    ContDiffAt ℝ 2 (fun z => xiPot (G (T z)) (z i)) z₀ := by
  have hT2 : ContDiffAt ℝ 2 T z₀ := (hT.contDiffAt (n := 2)).restrict_scalars ℝ
  exact contDiffAt_xiPot (fun z => G (T z)) _ z₀ hpd (fun p q => (hC p q).comp z₀ hT2)
    (((analyticAt_coord i z₀).contDiffAt (n := 2)).restrict_scalars ℝ)

theorem contDiffAt_base {D d : ℕ} (α : (Fin d → ℂ) → ℝ) {T : (Fin D → ℂ) → (Fin d → ℂ)}
    {z₀ : Fin D → ℂ} (hT : AnalyticAt ℂ T z₀) (hα : ContDiffAt ℝ 2 α (T z₀)) :
    ContDiffAt ℝ 2 (fun z => α (T z)) z₀ :=
  hα.comp z₀ ((hT.contDiffAt (n := 2)).restrict_scalars ℝ)

theorem hess_lin {D : ℕ} {f₀ f₁ h₀ h₁ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (c₀ c₁ : ℝ)
    (hf₀ : ContDiffAt ℝ 2 f₀ z) (hf₁ : ContDiffAt ℝ 2 f₁ z) (hh₀ : ContDiffAt ℝ 2 h₀ z) (hh₁ : ContDiffAt ℝ 2 h₁ z)
    (e₀ : hessC f₀ z = hessC h₀ z) (e₁ : hessC f₁ z = hessC h₁ z) :
    hessC (fun w => c₀ * f₀ w + c₁ * f₁ w) z = hessC (fun w => c₀ * h₀ w + c₁ * h₁ w) z := by
  rw [ReciprocityTheory.AnForm.A.hessC_add _ _ z (contDiffAt_const.mul hf₀) (contDiffAt_const.mul hf₁),
    ReciprocityTheory.AnForm.A.hessC_add _ _ z (contDiffAt_const.mul hh₀) (contDiffAt_const.mul hh₁),
    ReciprocityTheory.AnForm.M.hessC_const_mul', ReciprocityTheory.AnForm.M.hessC_const_mul',
    ReciprocityTheory.AnForm.M.hessC_const_mul', ReciprocityTheory.AnForm.M.hessC_const_mul', e₀, e₁]

theorem dens1 : ∀ (d m : ℕ) (G g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ContDiffAt ℝ 2 α y → (∀ p q, Differentiable ℂ fun y' => g y' p q) → IsUnit (g y).det → ∀ a : ℂ, GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a ≠ 0 → maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < m then xiPot ((g (Fin.tail z))ᴴ * G (Fin.tail z) * g (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) = Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a) * maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < m then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob (g y) a) y) := by
  intro d m G g α y hG hC hα hg hu a ha
  obtain ⟨han, hjac⟩ := GlobalTheory.T.analyticAt_mobius_det_jacobian_eq d g hg y a ha
  have hτ : mob1 g (Fin.cons a y) = Fin.cons (mob (g y) a) y := by simp [mob1]
  let T : (Fin (d + 1) → ℂ) → (Fin d → ℂ) := fun z => Fin.tail z
  have hTa : ∀ z₀, AnalyticAt ℂ T z₀ := fun z₀ => analyticAt_tail z₀
  have hTc : ∀ b : ℂ, T (Fin.cons b y) = y := fun b => by simp [T]
  let φ : Fin (d + 1) → (Fin (d + 1) → ℂ) → ℝ :=
    fun r z => if (r : ℕ) < m then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)
  have hφ : ∀ r, ContDiffAt ℝ 2 (φ r) (mob1 g (Fin.cons a y)) := by
    intro r
    rw [hτ]
    by_cases h : (r : ℕ) < m
    · simp only [φ, h, if_true]
      exact contDiffAt_xi_coord G (hTa _) 0 (by rw [hTc]; exact hG.self_of_nhds) (by rw [hTc]; exact hC)
    · simp only [φ, h, if_false]
      exact contDiffAt_base α (T := T) (hTa _) (by rw [hTc]; exact hα)
  have step := ReciprocityTheory.AnForm.A.maDens_comp φ (mob1 g) _ han hφ
  rw [hjac, hτ] at step
  rw [mul_comm, ← step]
  apply maDens_congr_hess
  intro r
  by_cases h : (r : ℕ) < m
  · have e : φ r ∘ mob1 g = fun z => xiPot (G (T z)) (mob (g (T z)) (z 0)) := by
      funext z
      simp [φ, h, mob1, T]
    rw [e]
    simp only [h, if_true]
    exact (hess_xi G g (hTa _) 0 (by rw [hTc]; exact hG) (by rw [hTc]; exact hC) hg (by rw [hTc]; exact hu)
      (by simpa [hTc] using ha)).2.2
  · have e : φ r ∘ mob1 g = fun z => α (Fin.tail z) := by
      funext z
      simp [φ, h, mob1]
    rw [e]
    simp only [h, if_false]

theorem dens2 : ∀ (d m : ℕ) (u : ℕ → Fin 2 → ℝ) (G g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ContDiffAt ℝ 2 α y → (∀ p q, Differentiable ℂ fun y' => g y' p q) → IsUnit (g y).det → ∀ a₀ a₁ : ℂ, GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₀ ≠ 0 → GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₁ ≠ 0 → maDens (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < m then u r 0 * xiPot ((g (Fin.tail (Fin.tail z)))ᴴ * G (Fin.tail (Fin.tail z)) * g (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot ((g (Fin.tail (Fin.tail z)))ᴴ * G (Fin.tail (Fin.tail z)) * g (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z))) (Fin.cons a₀ (Fin.cons a₁ y)) = (Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₀) * Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₁)) * maDens (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < m then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z))) (Fin.cons (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob (g y) a₀) (Fin.cons (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob (g y) a₁) y)) := by
  intro d m u G g α y hG hC hα hg hu a₀ a₁ h₀ h₁
  obtain ⟨han, hjac⟩ := GlobalTheory.T.mobius_pair_analytic_det_jacobian_eq d g hg y a₀ a₁ h₀ h₁
  have c0 : ∀ b₀ b₁ : ℂ, (Fin.cons b₀ (Fin.cons b₁ y) : Fin (d + 2) → ℂ) 0 = b₀ := fun _ _ => rfl
  have c1 : ∀ b₀ b₁ : ℂ, (Fin.cons b₀ (Fin.cons b₁ y) : Fin (d + 2) → ℂ) 1 = b₁ := fun _ _ => rfl
  let T : (Fin (d + 2) → ℂ) → (Fin d → ℂ) := fun z => Fin.tail (Fin.tail z)
  have hTa : ∀ z₀, AnalyticAt ℂ T z₀ := fun z₀ => analyticAt_tail2 z₀
  have hTc : ∀ b₀ b₁ : ℂ, T (Fin.cons b₀ (Fin.cons b₁ y)) = y := fun b₀ b₁ => by simp [T]
  have hτ : mob2 g (Fin.cons a₀ (Fin.cons a₁ y)) = Fin.cons (mob (g y) a₀) (Fin.cons (mob (g y) a₁) y) := by
    have ht : Fin.tail (Fin.tail (Fin.cons a₀ (Fin.cons a₁ y) : Fin (d + 2) → ℂ)) = y := hTc a₀ a₁
    simp only [mob2, ht, c0, c1]
  let φ : Fin (d + 2) → (Fin (d + 2) → ℂ) → ℝ :=
    fun r z => if (r : ℕ) < m then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) +
      u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z))
  have hφ : ∀ r, ContDiffAt ℝ 2 (φ r) (mob2 g (Fin.cons a₀ (Fin.cons a₁ y))) := by
    intro r
    rw [hτ]
    by_cases h : (r : ℕ) < m
    · simp only [φ, h, if_true]
      exact (contDiffAt_const.mul (contDiffAt_xi_coord G (hTa _) 0 (by rw [hTc]; exact hG.self_of_nhds)
        (by rw [hTc]; exact hC))).add (contDiffAt_const.mul (contDiffAt_xi_coord G (hTa _) 1
          (by rw [hTc]; exact hG.self_of_nhds) (by rw [hTc]; exact hC)))
    · simp only [φ, h, if_false]
      exact contDiffAt_base α (T := T) (hTa _) (by rw [hTc]; exact hα)
  have step := ReciprocityTheory.AnForm.A.maDens_comp φ (mob2 g) _ han hφ
  rw [hjac, hτ, Complex.normSq_mul] at step
  rw [mul_comm, ← step]
  apply maDens_congr_hess
  intro r
  by_cases h : (r : ℕ) < m
  · have e : φ r ∘ mob2 g = fun z => u r 0 * xiPot (G (T z)) (mob (g (T z)) (z 0)) +
        u r 1 * xiPot (G (T z)) (mob (g (T z)) (z 1)) := by
      funext z
      have e0 : mob2 g z 0 = mob (g (T z)) (z 0) := rfl
      have e1 : mob2 g z 1 = mob (g (T z)) (z 1) := rfl
      have e2 : Fin.tail (Fin.tail (mob2 g z)) = T z := by simp [mob2, T]
      simp only [Function.comp, φ, h, if_true, e0, e1, e2, T]
    rw [e]
    simp only [h, if_true]
    have x0 := hess_xi G g (hTa (Fin.cons a₀ (Fin.cons a₁ y))) 0 (by rw [hTc]; exact hG) (by rw [hTc]; exact hC) hg
      (by rw [hTc]; exact hu) (by rw [hTc, c0]; exact h₀)
    have x1 := hess_xi G g (hTa (Fin.cons a₀ (Fin.cons a₁ y))) 1 (by rw [hTc]; exact hG) (by rw [hTc]; exact hC) hg
      (by rw [hTc]; exact hu) (by rw [hTc, c1]; exact h₁)
    exact hess_lin _ _ x0.1 x1.1 x0.2.1 x1.2.1 x0.2.2 x1.2.2
  · have e : φ r ∘ mob2 g = fun z => α (Fin.tail (Fin.tail z)) := by
      funext z
      have e2 : Fin.tail (Fin.tail (mob2 g z)) = Fin.tail (Fin.tail z) := by simp [mob2]
      simp only [Function.comp, φ, h, if_false, e2]
    rw [e]
    simp only [h, if_false]

end GlobalTheory.CompanionTheory.Ar.PB.FibPt

open GlobalTheory.CompanionTheory.Ar.PB.FibPt in

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.ae_den_ne (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : IsUnit g.det) : ∀ᵐ a : ℂ, den g a ≠ 0 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
    have := hg.ne_zero
    rwa [Matrix.det_fin_two] at this
  by_cases h : g 0 1 = 0
  · refine Eventually.of_forall fun a => ?_
    have h0 : g 0 0 ≠ 0 := by
      rintro h0
      apply hdet
      simp [h, h0]
    simpa [den, h] using h0
  · have hsub : {a : ℂ | ¬ den g a ≠ 0} ⊆ {-(g 0 0) / g 0 1} := by
      intro a ha
      have ha' : den g a = 0 := by simpa using ha
      simp only [Set.mem_singleton_iff]
      unfold den at ha'
      field_simp
      linear_combination ha'
    exact measure_mono_null hsub (by simp)

open GlobalTheory.CompanionTheory.Ar.PB.FibPt in

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.fibre_integral_any_frame : GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (d k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → ∀ (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ContDiffAt ℝ 2 α y → (∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y))) = 2 * ReciprocityTheory.ChartRestriction.G.AI.kappa k * ∫ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) := by
  intro hF d k hk hkd G α y hG hC hα
  obtain ⟨g, hgd, hgu, hpd, hc2, h1, hf0⟩ := GlobalTheory.T.local_unitary_normal_frame_2x2 d G y hG hC
  have key := GlobalTheory.T.log_sine_monge_ampere_normalized hF d k hk hkd (fun y' => (g y')ᴴ * G y' * g y') α y hpd hc2 hα h1 hf0
  have hae := ae_den_ne (g y) hgu
  have hR : ∫ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot ((g (Fin.tail z))ᴴ * G (Fin.tail z) * g (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) = ∫ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) := by
    refine Eq.trans (integral_congr_ae (hae.mono fun a ha => ?_)) (GlobalTheory.T.integral_normSq_mobD_mul_comp_mob' (g y) hgu (fun b : ℂ => maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons b y)))
    exact dens1 d (2 * k - 1) G g α y hG hC hα hgd hgu a ha
  have hL : ∀ u : ℕ → Fin 2 → ℝ, ∫ p : ℂ × ℂ, logSin ((g y)ᴴ * G y * g y) p.1 p.2 * maDens (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot ((g (Fin.tail (Fin.tail z)))ᴴ * G (Fin.tail (Fin.tail z)) * g (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot ((g (Fin.tail (Fin.tail z)))ᴴ * G (Fin.tail (Fin.tail z)) * g (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z))) (Fin.cons p.1 (Fin.cons p.2 y)) = ∫ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z))) (Fin.cons p.1 (Fin.cons p.2 y)) := by
    intro u
    have hae2 : ∀ᵐ p : ℂ × ℂ, den (g y) p.1 ≠ 0 ∧ den (g y) p.2 ≠ 0 := by
      have h1' : ∀ᵐ p : ℂ × ℂ, den (g y) p.1 ≠ 0 :=
        (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))).ae hae
      have h2' : ∀ᵐ p : ℂ × ℂ, den (g y) p.2 ≠ 0 :=
        (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))).ae hae
      exact h1'.and h2'
    refine Eq.trans (integral_congr_ae (hae2.mono fun p hp => ?_)) (GlobalTheory.T.mobius_change_of_variables_pair (g y) hgu (fun p : ℂ × ℂ => logSin (G y) p.1 p.2 * maDens (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z))) (Fin.cons p.1 (Fin.cons p.2 y))))
    have hpdy : (G y).PosDef := hG.self_of_nhds
    have hs := (GlobalTheory.T.log_sine_mobius_transform (G y) (g y) hpdy hgu).2.2 p.1 p.2 hp.1 hp.2
    simp only []
    rw [hs, dens2 d (2 * k) u G g α y hG hC hα hgd hgu p.1 p.2 hp.1 hp.2]
    simp only [mob, den]
    ring
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (key.trans ?_)
  · exact (hL (fun (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c)).symm
  · exact congrArg _ hR

end

import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveClosedOneFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluriharmonicIsRealPartHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplyConnectedCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMetricTranslationInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMetricChernFlatAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcSubOfContDiffOnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCharacterEqExpRiemannFormStatement

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.FlatRigidity

variable {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def thF (τ : E → Matrix (Fin g) (Fin g) ℂ) (x : Fl g) (P : Pt E g) : ℂ :=
  Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) x P.2)

def thM (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : ℝ :=
  Real.exp (-2 * π * ((fun i => (P.2 i).im) ⬝ᵥ ((((τ P.1).map Complex.im)⁻¹) *ᵥ fun i => (P.2 i).im)))

theorem per_add (t : Matrix (Fin g) (Fin g) ℂ) (x y : Fl g) : per t (x + y) = per t x + per t y := by
  ext i
  simp only [per, Pi.add_apply, Complex.ofReal_add, Matrix.vecMul, dotProduct, add_mul,
    Finset.sum_add_distrib]
  ring

theorem transl_transl (τ : E → Matrix (Fin g) (Fin g) ℂ) (x y : Fl g) (P : Pt E g) :
    transl τ x (transl τ y P) = transl τ (x + y) P := by
  simp only [transl, per_add]
  ext <;> simp [add_comm, add_assoc]

theorem transl_mem {B : Set E} (τ : E → Matrix (Fin g) (Fin g) ℂ) (x : Fl g) {P : Pt E g}
    (hP : P ∈ cov B g) : transl τ x P ∈ cov B g :=
  ⟨hP.1, Set.mem_univ _⟩

theorem diff_entries {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) (i j : Fin g) :
    DifferentiableOn ℂ (fun P : Pt E g => τ P.1 i j) (cov B g) :=
  (hτ.2.1 i j).comp differentiableOn_fst fun _ hP => hP.1

theorem differentiableOn_transl {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) (x : Fl g) : DifferentiableOn ℂ (transl τ x) (cov B g) := by
  have hp : DifferentiableOn ℂ (fun P : Pt E g => per (τ P.1) x) (cov B g) := by
    refine differentiableOn_pi.2 fun i => ?_
    simp only [per, Pi.add_apply, Matrix.vecMul, dotProduct]
    exact (DifferentiableOn.fun_sum fun k _ => (diff_entries hτ k i).const_mul _).add
      (differentiableOn_const _)
  exact differentiableOn_fst.prodMk (differentiableOn_snd.add hp)

theorem differentiableOn_thF {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) (x : Fl g) : DifferentiableOn ℂ (thF τ x) (cov B g) := by
  have hd := diff_entries hτ (g := g)
  unfold thF
  simp only [thetaExp, dotProduct, Matrix.vecMul, div_eq_mul_inv]
  have hz : ∀ i, DifferentiableOn ℂ (fun P : Pt E g => P.2 i) (cov B g) := fun i =>
    Differentiable.differentiableOn (by fun_prop)
  exact DifferentiableOn.cexp (DifferentiableOn.const_mul (DifferentiableOn.sub
    (DifferentiableOn.mul_const (DifferentiableOn.neg (DifferentiableOn.fun_sum fun i _ =>
      DifferentiableOn.mul_const (DifferentiableOn.fun_sum fun k _ =>
        (hd k i).const_mul _) _)) _)
    (DifferentiableOn.fun_sum fun i _ => (hz i).const_mul _)) _)

theorem thF_ne (τ : E → Matrix (Fin g) (Fin g) ℂ) (x : Fl g) (P : Pt E g) : thF τ x P ≠ 0 :=
  Complex.exp_ne_zero _

theorem thF_transl {τ : E → Matrix (Fin g) (Fin g) ℂ} (x l : Fl g) (P : Pt E g)
    (hs : (τ P.1).IsSymm) :
    thF τ x (transl τ l P) * thF τ l P =
      thF τ l (transl τ x P) * thF τ x P * Complex.exp (2 * π * Complex.I * riem x l) := by
  simp only [thF, transl, ← Complex.exp_add]
  congr 1
  have e1 := thetaExp_add hs x l P.2
  have e2 := thetaExp_add hs l x P.2
  rw [add_comm l x] at e2
  have e3 : (riem x l : ℂ) = ∑ i, (l (Sum.inl i) : ℂ) * (x (Sum.inr i) : ℂ) -
      ∑ i, (x (Sum.inl i) : ℂ) * (l (Sum.inr i) : ℂ) := by
    simp [riem, mul_comm, Finset.sum_sub_distrib]
  rw [e3]
  linear_combination (2 * π * Complex.I) * (e2 - e1)

end GlobalTheory.FlatRigidity

end

noncomputable section

namespace GlobalTheory.FlatRigidity

variable {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eq_const_of_norm_eq_one {B : Set E} (hB : IsOpen B) (hc : IsPreconnected B)
    (f : Pt E g → ℂ) (hf : DifferentiableOn ℂ f (cov B g)) (h1 : ∀ P ∈ cov B g, ‖f P‖ = 1) :
    ∃ c : ℂ, ∀ P ∈ cov B g, f P = c := by
  rcases (cov B g).eq_empty_or_nonempty with he | ⟨P₀, hP₀⟩
  · exact ⟨0, fun P hP => by simp [he] at hP⟩
  refine ⟨f P₀, fun P hP => ?_⟩
  have hpc : IsPreconnected (cov B g) := hc.prod isPreconnected_univ
  have hm : IsMaxOn (norm ∘ f) (cov B g) P₀ := fun P hP => by
    simp [Function.comp, h1 P hP, h1 P₀ hP₀]
  exact Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hpc (hB.prod isOpen_univ) hf hP₀ hm hP

theorem nonempty_of_sc {B : Set E} (hB : SimplyConnectedSpace B) : ∃ b, b ∈ B := by
  obtain ⟨⟨b, hb⟩⟩ := (inferInstance : Nonempty B)
  exact ⟨b, hb⟩

theorem preconnected_of_sc {B : Set E} (hB : SimplyConnectedSpace B) : IsPreconnected B :=
  isPreconnected_iff_preconnectedSpace.2 inferInstance

end GlobalTheory.FlatRigidity

end

noncomputable section

namespace GlobalTheory.FlatRigidity

variable {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem normal_form [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) (hB : SimplyConnectedSpace B) {M : Submodule ℤ (Fl g)}
    {j : Fl g → Pt E g → ℂ} {h : Pt E g → ℝ} (hj : IsFactor B τ M j) (hh : IsMetric B τ M j h)
    (hc : ChernIsFlat B τ h) :
    ∃ (φ : Pt E g → ℂ) (κ : Fl g → ℂ), IsBundleIso B τ M j (fun l P => κ l * thF τ l P) φ ∧
      IsIsometry B h (thM τ) φ ∧ ∀ l ∈ M, ‖κ l‖ = 1 := by
  have hU : IsOpen (cov B g) := hτ.1.prod isOpen_univ
  obtain ⟨hθm, hθc⟩ := GlobalTheory.T.chernIsFlat_exp_neg_im_quadratic (E := E) hτ
  have hθs : ContDiffOn ℝ ∞ (thM τ) (cov B g) := hθm.1
  have hθp : ∀ P ∈ cov B g, 0 < thM τ P := fun P _ => Real.exp_pos _
  have hθi : ∀ x : Fl g, ∀ P ∈ cov B g, thM τ (transl τ x P) * ‖thF τ x P‖ ^ 2 = thM τ P :=
    GlobalTheory.T.theta_metric_translation_invariant hτ
  have hl1 : ContDiffOn ℝ ∞ (fun Q => Real.log (h Q)) (cov B g) :=
    hh.1.log fun P hP => (hh.2.1 P hP).ne'
  have hl2 : ContDiffOn ℝ ∞ (fun Q => Real.log (thM τ Q)) (cov B g) :=
    hθs.log fun P hP => (hθp P hP).ne'
  set u : Pt E g → ℝ := fun Q => Real.log (h Q) - Real.log (thM τ Q) with hu
  have hus : ContDiffOn ℝ ∞ u (cov B g) := hl1.sub hl2
  have hddc : ∀ P ∈ cov B g, ∀ v w : Pt E g, ddc u P v w = 0 := by
    intro P hP v w
    rw [hu, GlobalTheory.T.ddc_sub_of_contDiffOn' _ _ hU (hl1.of_le (WithTop.coe_le_coe.2 le_top))
      (hl2.of_le (WithTop.coe_le_coe.2 le_top)) P hP v w]
    have e1 := hc P hP v w
    have e2 := hθc P hP v w
    change -ddc (fun Q => Real.log (thM τ Q)) P v w = om0 τ P ![v, w] at e2
    linarith
  obtain ⟨F, hFd, hFr⟩ := GlobalTheory.T.pluriharmonic_is_real_part_holomorphic u hU (GlobalTheory.T.simply_connected_cover hB) hus hddc
  set φ : Pt E g → ℂ := fun P => Complex.exp (F P / 2) with hφ
  have hφd : DifferentiableOn ℂ φ (cov B g) := DifferentiableOn.cexp (by simpa only [div_eq_mul_inv] using hFd.mul_const (2⁻¹ : ℂ))
  have hφn : ∀ P, φ P ≠ 0 := fun P => Complex.exp_ne_zero _
  have hφs : ∀ P ∈ cov B g, thM τ P * ‖φ P‖ ^ 2 = h P := by
    intro P hP
    rw [hφ, Complex.norm_exp, ← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (F P / 2).re = u P := by
      rw [← hFr P hP]; simp; ring
    rw [this, hu, Real.exp_sub, Real.exp_log (hh.2.1 P hP), Real.exp_log (hθp P hP)]
    field_simp [(hθp P hP).ne']
  set k : Fl g → Pt E g → ℂ := fun l P => φ (transl τ l P) * j l P / (thF τ l P * φ P) with hk
  have hk1 : ∀ l ∈ M, ∀ P ∈ cov B g, ‖k l P‖ = 1 := by
    intro l hl P hP
    have A := hφs _ (transl_mem τ l hP)
    have Bq := hφs P hP
    have C := hh.2.2 l hl P hP
    have D := hθi l P hP
    have key : thM τ (transl τ l P) * (‖φ (transl τ l P)‖ ^ 2 * ‖j l P‖ ^ 2) =
        thM τ (transl τ l P) * (‖thF τ l P‖ ^ 2 * ‖φ P‖ ^ 2) := by
      linear_combination ‖j l P‖ ^ 2 * A + C - ‖φ P‖ ^ 2 * D - Bq
    have key' := mul_left_cancel₀ (hθp _ (transl_mem τ l hP)).ne' key
    have hpos : 0 < ‖thF τ l P‖ ^ 2 * ‖φ P‖ ^ 2 := by
      have := norm_pos_iff.2 (thF_ne τ l P)
      have := norm_pos_iff.2 (hφn P)
      positivity
    have hsq : ‖k l P‖ ^ 2 = 1 := by
      simp only [hk, norm_div, norm_mul, div_pow, mul_pow]
      rw [key', div_self hpos.ne']
    have := norm_nonneg (k l P)
    nlinarith [sq_nonneg (‖k l P‖ - 1), sq_nonneg (‖k l P‖ + 1)]
  have hkc : ∀ l ∈ M, ∃ c : ℂ, ∀ P ∈ cov B g, k l P = c := by
    intro l hl
    refine eq_const_of_norm_eq_one hτ.1 (preconnected_of_sc hB) (k l) ?_ (hk1 l hl)
    simp only [hk, div_eq_mul_inv]
    exact ((hφd.comp (differentiableOn_transl hτ l) fun P hP => transl_mem τ l hP).mul
      ((hj.1 l hl).1)).mul (((differentiableOn_thF hτ l).mul hφd).inv fun P _ =>
      mul_ne_zero (thF_ne _ _ _) (hφn P))
  choose! κ hκ using hkc
  obtain ⟨b₀, hb₀⟩ := nonempty_of_sc hB
  have hP₀ : ((b₀, 0) : Pt E g) ∈ cov B g := ⟨hb₀, Set.mem_univ _⟩
  refine ⟨φ, κ, ⟨hφd, fun P _ => hφn P, fun l hl P hP => ?_⟩, hφs, fun l hl => ?_⟩
  · show φ (transl τ l P) * j l P = κ l * thF τ l P * φ P
    have := hκ l hl P hP
    simp only [hk] at this
    rw [← this]
    field_simp [thF_ne τ l P, hφn P]
  · rw [← hκ l hl _ hP₀]
    exact hk1 l hl _ hP₀

end GlobalTheory.FlatRigidity

end

noncomputable section

namespace GlobalTheory.FlatRigidity

variable {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem kappa_add {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)}
    {j : Fl g → Pt E g → ℂ} {φ : Pt E g → ℂ} {κ : Fl g → ℂ} (hj : IsFactor B τ M j)
    (hi : IsBundleIso B τ M j (fun l P => κ l * thF τ l P) φ) {l l' : Fl g} (hl : l ∈ M)
    (hl' : l' ∈ M) {P : Pt E g} (hP : P ∈ cov B g) :
    κ (l + l') * thF τ (l + l') P = κ l * κ l' * (thF τ l (transl τ l' P) * thF τ l' P) := by
  have e1 := hi.2.2 (l + l') (M.add_mem hl hl') P hP
  have e2 := hj.2 l hl l' hl' P hP
  have e3 := hi.2.2 l hl (transl τ l' P) (transl_mem τ l' hP)
  have e4 := hi.2.2 l' hl' P hP
  simp only at e1 e3 e4
  rw [transl_transl] at e3
  have hφ := hi.2.1 P hP
  apply mul_right_cancel₀ hφ
  rw [← e1, e2]
  linear_combination j l' P * e3 + κ l * thF τ l (transl τ l' P) * e4

theorem rigidity : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ},
    IsPeriodMap B τ → RigidityProps B τ := by
  intro g E _ _ _ B τ hτ hB M hM _ j₁ j₂ h₁ h₂ hj₁ hh₁ hc₁ hj₂ hh₂ hc₂
  obtain ⟨φ₁, κ₁, hi₁, hs₁, hn₁⟩ := normal_form hτ hB hj₁ hh₁ hc₁
  obtain ⟨φ₂, κ₂, hi₂, hs₂, hn₂⟩ := normal_form hτ hB hj₂ hh₂ hc₂
  obtain ⟨b₀, hb₀⟩ := nonempty_of_sc hB
  have hP₀ : ((b₀, 0) : Pt E g) ∈ cov B g := ⟨hb₀, Set.mem_univ _⟩
  have hne : ∀ l ∈ M, κ₂ l ≠ 0 := fun l hl h0 => by simpa [h0] using hn₂ l hl
  set χ : Fl g → ℂ := fun l => κ₁ l / κ₂ l with hχ
  have hχ1 : ∀ l ∈ M, ‖χ l‖ = 1 := fun l hl => by simp [hχ, norm_div, hn₁ l hl, hn₂ l hl]
  have hχm : ∀ l ∈ M, ∀ l' ∈ M, χ (l + l') = χ l * χ l' := by
    intro l hl l' hl'
    have e1 := kappa_add hj₁ hi₁ hl hl' hP₀
    have e2 := kappa_add hj₂ hi₂ hl hl' hP₀
    set T := thF τ (l + l') ((b₀, 0) : Pt E g)
    set X := thF τ l (transl τ l' ((b₀, 0) : Pt E g)) * thF τ l' ((b₀, 0) : Pt E g)
    have hT : T ≠ 0 := thF_ne _ _ _
    have hX : X ≠ 0 := mul_ne_zero (thF_ne _ _ _) (thF_ne _ _ _)
    have e1' : κ₁ (l + l') = κ₁ l * κ₁ l' * X / T := by
      field_simp; linear_combination e1
    have e2' : κ₂ (l + l') = κ₂ l * κ₂ l' * X / T := by
      field_simp; linear_combination e2
    simp only [hχ, e1', e2']
    field_simp [hne l hl, hne l' hl']
  obtain ⟨x, hx⟩ := GlobalTheory.T.lattice_character_eq_exp_riemann_form hM χ hχ1 hχm
  refine ⟨x, fun P => φ₂ P * thF τ x P / φ₁ (transl τ x P), ⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [div_eq_mul_inv]
    exact (hi₂.1.mul (differentiableOn_thF hτ x)).mul
      ((hi₁.1.comp (differentiableOn_transl hτ x) fun P hP => transl_mem τ x hP).inv
        fun P hP => hi₁.2.1 _ (transl_mem τ x hP))
  · intro P hP
    exact div_ne_zero (mul_ne_zero (hi₂.2.1 P hP) (thF_ne _ _ _)) (hi₁.2.1 _ (transl_mem τ x hP))
  · intro l hl P hP
    simp only [translPullFactor]
    have A := hi₂.2.2 l hl P hP
    have Bf := hi₁.2.2 l hl (transl τ x P) (transl_mem τ x hP)
    have Cf := thF_transl (τ := τ) x l P (hτ.2.2 P.1 hP.1).1
    have Df := hx l hl
    simp only at A Bf
    simp only [hχ] at Df
    have hcomm : transl τ x (transl τ l P) = transl τ l (transl τ x P) := by
      rw [transl_transl, transl_transl, add_comm]
    rw [hcomm]
    have hV := hi₁.2.1 _ (transl_mem τ x hP)
    have hW := hi₁.2.1 _ (transl_mem τ l (transl_mem τ x hP))
    have hk1 : κ₁ l = κ₂ l * Complex.exp (2 * π * Complex.I * riem x l) := by
      rw [← Df]; field_simp [hne l hl]
    rw [div_mul_eq_mul_div, mul_div_assoc', div_eq_div_iff hW hV]
    first
      | linear_combination (thF τ x (transl τ l P) * φ₁ (transl τ x P)) * A + κ₂ l * φ₂ P * φ₁ (transl τ x P) * Cf - φ₂ P * thF τ x P * Bf - φ₂ P * thF τ x P * thF τ l (transl τ x P) * φ₁ (transl τ x P) * hk1
      | linear_combination -((thF τ x (transl τ l P) * φ₁ (transl τ x P)) * A + κ₂ l * φ₂ P * φ₁ (transl τ x P) * Cf - φ₂ P * thF τ x P * Bf - φ₂ P * thF τ x P * thF τ l (transl τ x P) * φ₁ (transl τ x P) * hk1)
  · intro P hP
    have e1 := hs₁ _ (transl_mem τ x hP)
    have e2 := hs₂ P hP
    have e3 := GlobalTheory.T.theta_metric_translation_invariant hτ x P hP
    change thM τ (transl τ x P) * ‖thF τ x P‖ ^ 2 = thM τ P at e3
    have hV := norm_pos_iff.2 (hi₁.2.1 _ (transl_mem τ x hP))
    show h₁ (transl τ x P) * ‖φ₂ P * thF τ x P / φ₁ (transl τ x P)‖ ^ 2 = h₂ P
    rw [← e1, ← e2, norm_div, norm_mul, div_pow, mul_pow]
    field_simp
    linear_combination ‖φ₂ P‖ ^ 2 * e3

end GlobalTheory.FlatRigidity

end

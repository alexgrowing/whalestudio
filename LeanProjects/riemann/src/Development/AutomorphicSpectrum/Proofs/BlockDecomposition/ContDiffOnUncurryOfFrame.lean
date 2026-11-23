import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerToL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.WaveCp.Frame

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def eps (p : Bool × Fin n × Fin n) (A : Mat n) : ℝ :=
  if p.1 then (A p.2.1 p.2.2).re else (A p.2.1 p.2.2).im

theorem contDiff_eps (p : Bool × Fin n × Fin n) : ContDiff ℝ ∞ (eps p : Mat n → ℝ) := by
  obtain ⟨b, i, j⟩ := p
  cases b
  · have e : (eps (false, i, j) : Mat n → ℝ) = Complex.imCLM ∘ fun y : Mat n => y i j := by
      funext A; simp [eps]
    rw [e]
    exact Complex.imCLM.contDiff.comp (GlobalTheory.CompanionTheory.LengthGL.contDiff_ent i j)
  · have e : (eps (true, i, j) : Mat n → ℝ) = Complex.reCLM ∘ fun y : Mat n => y i j := by
      funext A; simp [eps]
    rw [e]
    exact Complex.reCLM.contDiff.comp (GlobalTheory.CompanionTheory.LengthGL.contDiff_ent i j)

theorem sum_eps (A : Mat n) : ∑ p, eps p A • (bs p : Mat n) = A := by
  ext a b
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, eps, bs, Matrix.sum_apply, Matrix.smul_apply]
  simp [Matrix.single_apply, Finset.sum_add_distrib, ite_and]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem fderiv_frame (f : Mat n → V) {x : Mat n} (hx : x ∈ GLs n) (ξ : Mat n) :
    fderiv ℝ f x ξ = ∑ p, eps p (ξ * x⁻¹) • fderiv ℝ f x (bs p * x) := by
  have hu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have e : ξ = ∑ p, eps p (ξ * x⁻¹) • (bs p * x) := by
    have : ξ * x⁻¹ * x = ξ := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    conv_lhs => rw [← this, ← sum_eps (ξ * x⁻¹), Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => smul_mul_assoc _ _ _
  conv_lhs => rw [e, map_sum]
  exact Finset.sum_congr rfl fun p _ => map_smul _ _ _

theorem contDiffOn_coeff (p : Bool × Fin n × Fin n) (ξ : Mat n) :
    ContDiffOn ℝ ∞ (fun x : Mat n => eps p (ξ * x⁻¹)) (GLs n) :=
  (contDiff_eps p).comp_contDiffOn
    ((GlobalTheory.CompanionTheory.RCalc.mulL ξ).contDiff.comp_contDiffOn GlobalTheory.CompanionTheory.LengthGL.contDiffOn_inv)

theorem contDiffOn_coeff' (p : Bool × Fin n × Fin n) (ξ : Mat n) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Mat n => eps p (ξ * z.2⁻¹)) (Set.univ ×ˢ GLs n) :=
  (contDiffOn_coeff p ξ).comp contDiff_snd.contDiffOn fun _ hz => hz.2

theorem isOpen_dom : IsOpen (Set.univ ×ˢ GLs n : Set (ℝ × Mat n)) :=
  isOpen_univ.prod GlobalTheory.CompanionTheory.LengthGL.isOpen_GLs

theorem hasFDerivAt_uncurry {h h₀ : ℝ → Mat n → V} {hp : (Bool × Fin n × Fin n) → ℝ → Mat n → V}
    (c₀ : ContinuousOn (Function.uncurry h₀) (Set.univ ×ˢ GLs n))
    (cp : ∀ p, ContinuousOn (Function.uncurry (hp p)) (Set.univ ×ˢ GLs n))
    (ht : ∀ t, ∀ x ∈ GLs n, HasDerivAt (fun s => h s x) (h₀ t x) t)
    (hd : ∀ t, DifferentiableOn ℝ (h t) (GLs n))
    (hf : ∀ p t, ∀ x ∈ GLs n, fderiv ℝ (h t) x (bs p * x) = hp p t x)
    {t : ℝ} {x : Mat n} (hx : x ∈ GLs n) :
    HasFDerivAt (Function.uncurry h)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (h₀ t x)).coprod (fderiv ℝ (h t) x)) (t, x) := by
  have hn : (Set.univ ×ˢ GLs n : Set (ℝ × Mat n)) ∈ nhds ((t, x) : ℝ × Mat n) :=
    isOpen_dom.mem_nhds ⟨trivial, hx⟩
  have c1 : ContinuousOn (Function.uncurry fun (t : ℝ) (x : Mat n) => (1 : ℝ →L[ℝ] ℝ).smulRight (h₀ t x))
      (Set.univ ×ˢ GLs n) := by
    rw [continuousOn_clm_apply]
    intro y
    refine ContinuousOn.congr (f := fun z : ℝ × Mat n => y • Function.uncurry h₀ z)
      ((continuousOn_const (c := y)).smul c₀) ?_
    rintro ⟨s, w⟩ -
    simp [Function.uncurry_def]
  have c2 : ContinuousOn (Function.uncurry fun (t : ℝ) (x : Mat n) => fderiv ℝ (h t) x)
      (Set.univ ×ˢ GLs n) := by
    refine continuousOn_clm_apply.2 fun ξ => ?_
    have h1 : ContinuousOn (fun z : ℝ × Mat n => ∑ p, eps p (ξ * z.2⁻¹) • hp p z.1 z.2)
        (Set.univ ×ˢ GLs n) :=
      continuousOn_finset_sum _ fun p _ => (contDiffOn_coeff' p ξ).continuousOn.smul (cp p)
    refine h1.congr ?_
    rintro ⟨s, y⟩ ⟨-, hy⟩
    have hy' : y ∈ GLs n := hy
    exact (fderiv_frame (h s) hy' ξ).trans (Finset.sum_congr rfl fun p _ => by rw [hf p s y hy'])
  have key := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := ((t, x) : ℝ × Mat n)) (f := h)
    (f₁ := fun t x => (1 : ℝ →L[ℝ] ℝ).smulRight (h₀ t x)) (f₂ := fun t x => fderiv ℝ (h t) x)
    ?_ ?_ (c1.continuousAt hn) (c2.continuousAt hn)
  · exact key.hasFDerivAt
  · filter_upwards [hn] with v hv
    exact (ht v.1 v.2 hv.2).hasFDerivAt
  · filter_upwards [hn] with v hv
    exact ((hd v.1 v.2 hv.2).differentiableAt (GlobalTheory.CompanionTheory.LengthGL.isOpen_GLs.mem_nhds hv.2)).hasFDerivAt

theorem contDiffOn_step (F : Set (ℝ → Mat n → V))
    (hc : ∀ h ∈ F, ContinuousOn (Function.uncurry h) (Set.univ ×ˢ GLs n))
    (hdt : ∀ h ∈ F, ∃ h' ∈ F, ∀ t, ∀ x ∈ GLs n, HasDerivAt (fun s => h s x) (h' t x) t)
    (hd : ∀ h ∈ F, ∀ t, DifferentiableOn ℝ (h t) (GLs n))
    (hfr : ∀ h ∈ F, ∀ p, ∃ h' ∈ F, ∀ t, ∀ x ∈ GLs n, fderiv ℝ (h t) x (bs p * x) = h' t x)
    (k : ℕ) (ih : ∀ h ∈ F, ContDiffOn ℝ k (Function.uncurry h) (Set.univ ×ˢ GLs n)) :
    ∀ h ∈ F, ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry h) (Set.univ ×ˢ GLs n) := by
  intro h hh
  obtain ⟨h₀, h₀F, ht⟩ := hdt h hh
  choose hp hpF hf using hfr h hh
  have hD : ∀ z ∈ (Set.univ ×ˢ GLs n : Set (ℝ × Mat n)), HasFDerivAt (Function.uncurry h)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (h₀ z.1 z.2)).coprod (fderiv ℝ (h z.1) z.2)) z := fun z hz =>
    hasFDerivAt_uncurry (hc _ h₀F) (fun p => hc _ (hpF p)) ht (hd h hh) hf hz.2
  have e : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by norm_cast
  rw [e, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_dom]
  refine ⟨fun z hz => (hD z hz).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_clm_apply]
  rintro ⟨τ, ξ⟩
  have h1 : ContDiffOn ℝ k (fun z : ℝ × Mat n =>
      τ • h₀ z.1 z.2 + ∑ p, eps p (ξ * z.2⁻¹) • hp p z.1 z.2) (Set.univ ×ˢ GLs n) := by
    refine ContDiffOn.add (contDiffOn_const.smul (ih _ h₀F)) (ContDiffOn.sum fun p _ => ?_)
    exact ((contDiffOn_coeff' p ξ).of_le (by exact_mod_cast le_top)).smul (ih _ (hpF p))
  refine h1.congr ?_
  rintro ⟨s, y⟩ hz
  have e1 : fderiv ℝ (Function.uncurry h) (s, y) = _ := (hD _ hz).fderiv
  refine (congrArg (fun L => L (τ, ξ)) e1).trans ?_
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.smulRight_apply]
  rw [fderiv_frame _ hz.2]
  simp only [ContinuousLinearMap.one_apply]
  congr 1
  exact Finset.sum_congr rfl fun p _ => by rw [hf p s y hz.2]

theorem contDiffOn_uncurry_of_frame : ∀ {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (F : Set (ℝ → Mat n → V)), (∀ h ∈ F, ContinuousOn (Function.uncurry h) (Set.univ ×ˢ GLs n)) →
    (∀ h ∈ F, ∃ h' ∈ F, ∀ t, ∀ x ∈ GLs n, HasDerivAt (fun s => h s x) (h' t x) t) →
    (∀ h ∈ F, ∀ t, DifferentiableOn ℝ (h t) (GLs n)) →
    (∀ h ∈ F, ∀ p, ∃ h' ∈ F, ∀ t, ∀ x ∈ GLs n, fderiv ℝ (h t) x (bs p * x) = h' t x) →
    ∀ h ∈ F, ContDiffOn ℝ ∞ (Function.uncurry h) (Set.univ ×ˢ GLs n) := by
  intro n V _ _ F hc hdt hd hfr h hh
  rw [contDiffOn_infty]
  intro k
  induction k generalizing h with
  | zero =>
    have h0 : ContDiffOn ℝ 0 (Function.uncurry h) (Set.univ ×ˢ GLs n) := contDiffOn_zero.2 (hc h hh)
    simpa using h0
  | succ k ih => exact contDiffOn_step F hc hdt hd hfr k (fun h hh => ih h hh) h hh

end GlobalTheory.CompanionTheory.WaveCp.Frame

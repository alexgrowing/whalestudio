import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartHolomorphicOnCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartFormEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFormPullbackClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCubicalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesFormType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartTransitionHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartTransitionDifferentiableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannFormClosedStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0 dflat herm)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas IsType IsReal Alt delAt dbarAt)
open GlobalTheory.ConjChart (conjCoord conjPts conjChart)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (riem flat)
open scoped ComplexConjugate

namespace GlobalTheory.FlatGlue

section Point

variable {n m : ℕ}

def pairForm (x : Fin n → Fin n → ℂ) : Alt n := ∑ a, ∑ b, x a b • (CxForm.dz a * CxForm.dzb b)

def coef (α : Alt n) (a b : Fin n) : ℂ := (bas n).repr α {a.castAdd n, b.natAdd n}

theorem coef_pairForm (x : Fin n → Fin n → ℂ) : coef (pairForm x) = x :=
  funext fun a => funext fun b => TotalPos.repr_pair_sum x a b

theorem eq_pairForm {α : Alt n} (h : IsType 1 1 α) : α = pairForm (coef α) := TotalPos.eq_sum_of_isType h

theorem repr_pairForm (x : Fin n → Fin n → ℂ) (S : Finset (Fin (n + n))) :
    (bas n).repr (pairForm x) S = ∑ a, ∑ b, if {a.castAdd n, b.natAdd n} = S then x a b else 0 := by
  simp only [pairForm, ← CxForm.bas_pair, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, MulOneClass.mul_one, MulZeroClass.mul_zero]

theorem isType_pairForm (x : Fin n → Fin n → ℂ) : IsType 1 1 (pairForm x) := by
  intro S hS
  rw [repr_pairForm] at hS
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  have e : ({a.castAdd n, b.natAdd n} : Finset (Fin (n + n))) = S := by
    by_contra h
    exact hb (if_neg h)
  subst e
  constructor
  · refine Finset.card_eq_one.2 ⟨a.castAdd n, ?_⟩
    ext t
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_castAdd,
      Fin.val_natAdd]
    have := a.2
    omega
  · refine Finset.card_eq_one.2 ⟨b.natAdd n, ?_⟩
    ext t
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_castAdd,
      Fin.val_natAdd]
    have := a.2
    omega

theorem swap_pairForm (x : Fin n → Fin n → ℂ) : CxForm.swap (pairForm x) = pairForm fun a b => -x b a := by
  simp only [pairForm, map_sum, map_smul, map_mul, (CxForm.swap_dz _).1, (CxForm.swap_dz _).2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [CxForm.dz, CxForm.dzb, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _), neg_smul, smul_neg]

theorem isReal_pairForm {x : Fin n → Fin n → ℂ} (h : ∀ a b, conj (x a b) = -x b a) : IsReal (pairForm x) := by
  intro S
  rw [swap_pairForm, repr_pairForm, repr_pairForm]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · exact (h a b).symm
  · exact (map_zero _).symm

theorem eval₂_eq (α : Alt n) (ξ ζ : V n) :
    eval₂ α ξ ζ = ∑ a, ∑ b, coef α a b * (ξ a * conj (ζ b) - ζ a * conj (ξ b)) := by
  simp only [eval₂, HermFrame.form, dotProduct, mulVec, hermMat, of_apply, coef, Pi.star_apply, Complex.star_def,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  linear_combination (-((bas n).repr α {a.castAdd n, b.natAdd n} * (ξ a * conj (ζ b) - ζ a * conj (ξ b)))) *
    Complex.I_mul_I

theorem coef_eq (α : Alt n) (a b : Fin n) : coef α a b =
    (eval₂ α (coordVec a) (coordVec b) + Complex.I * eval₂ α (coordVec a) (Complex.I • coordVec b)) / 2 := by
  have h1 : eval₂ α (coordVec a) (coordVec b) = coef α a b - coef α b a := by
    simp [eval₂_eq, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, apply_ite (starRingEnd ℂ)]
  have h2 : eval₂ α (coordVec a) (Complex.I • coordVec b) = -Complex.I * coef α a b - Complex.I * coef α b a := by
    simp [eval₂_eq, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, apply_ite (starRingEnd ℂ)]
    ring
  rw [h1, h2]
  linear_combination ((coef α a b + coef α b a) / 2) * Complex.I_mul_I

theorem eq_of_eval₂ {α β : Alt n} (hα : IsType 1 1 α) (hβ : IsType 1 1 β)
    (h : ∀ ξ ζ, eval₂ α ξ ζ = eval₂ β ξ ζ) : α = β := by
  rw [eq_pairForm hα, eq_pairForm hβ]
  congr 1
  funext a b
  rw [coef_eq, coef_eq, h, h]

theorem eval₂_pull (L : V n →L[ℂ] V m) {β : Alt m} (h : IsType 1 1 β) (ξ ζ : V n) :
    eval₂ (CxForm.pull L β) ξ ζ = eval₂ β (L ξ) (L ζ) := by
  have e (u : V n) : u.ofLp ᵥ* (Matrix.of fun c a => L (coordVec c) a) = (L u).ofLp := by
    have hu : u = ∑ c, u c • coordVec c := by
      ext i; simp [Pi.single_apply]
    conv_rhs => rw [hu]
    ext a
    simp [vecMul, dotProduct, map_sum, map_smul]
  have f (M : Matrix (Fin n) (Fin m) ℂ) (K : Matrix (Fin m) (Fin m) ℂ) (u w : Fin n → ℂ) :
      HermFrame.form (M * K * Mᴴ) u w = HermFrame.form K (u ᵥ* M) (w ᵥ* M) := by
    rw [HermFrame.form, HermFrame.form, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_vecMul]
  rw [eval₂, eval₂, TotalPos.hermMat_pull L h, f, f, e, e]

theorem eval₂_swap {β : Alt n} (h : IsType 1 1 β) (ξ ζ : V n) :
    eval₂ (CxForm.swap β) ξ ζ = eval₂ β (conjCoord n ξ) (conjCoord n ζ) := by
  conv_lhs => rw [eq_pairForm h, swap_pairForm]
  rw [eval₂_eq, eval₂_eq, coef_pairForm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have e (u : V n) (i : Fin n) : conjCoord n u i = conj (u i) := rfl
  simp only [e, Complex.conj_conj]
  ring

theorem eval₂_neg (β : Alt n) (ξ ζ : V n) : eval₂ (-β) ξ ζ = -eval₂ β ξ ζ := by
  simp [eval₂_eq, coef]

theorem exists_form (β : V n →ₗ[ℝ] V n →ₗ[ℝ] ℝ) (ha : ∀ ξ ζ, β ζ ξ = -β ξ ζ)
    (hI : ∀ ξ ζ, β (Complex.I • ξ) (Complex.I • ζ) = β ξ ζ) :
    ∃ α : Alt n, IsType 1 1 α ∧ IsReal α ∧ ∀ ξ ζ, eval₂ α ξ ζ = (β ξ ζ : ℝ) := by
  have hII (ξ : V n) : Complex.I • Complex.I • ξ = -ξ := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have hI' (ξ ζ) : β (Complex.I • ξ) ζ = -β ξ (Complex.I • ζ) := by
    rw [← hI, hII, map_neg, LinearMap.neg_apply]
  let H : V n → V n → ℂ := fun ξ ζ => ((β ξ ζ : ℝ) + Complex.I * (β ξ (Complex.I • ζ) : ℝ)) / 2
  have hs (c : ℂ) (ξ : V n) : c • ξ = c.re • ξ + c.im • Complex.I • ξ := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  have hl (c : ℂ) (ξ ζ) : H (c • ξ) ζ = c * H ξ ζ := by
    simp only [H]
    rw [hs c ξ]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hI, hI' ξ ζ]
    push_cast
    conv_rhs => rw [← Complex.re_add_im c]
    linear_combination (-(c.im * (β ξ (Complex.I • ζ) : ℝ) / 2)) * Complex.I_mul_I
  have hc (ξ ζ) : conj (H ξ ζ) = -H ζ ξ := by
    simp only [H, map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    rw [ha ξ ζ, ha (Complex.I • ξ) ζ, hI']
    push_cast
    ring
  have hr (c : ℂ) (ξ ζ) : H ξ (c • ζ) = conj c * H ξ ζ := by
    apply (starRingEnd ℂ).injective
    rw [hc, hl, map_mul, Complex.conj_conj, hc, mul_neg]
  have hsum (ξ ζ : V n) : ∑ a, ∑ b, H (coordVec a) (coordVec b) * (ξ a * conj (ζ b)) = H ξ ζ := by
    have hu (u : V n) : u = ∑ c, u c • coordVec c := by
      ext i; simp [Pi.single_apply]
    have s1 (f : Fin n → V n) (w) : H (∑ a, f a) w = ∑ a, H (f a) w := by
      simp only [H, map_sum, LinearMap.sum_apply, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        Finset.sum_div]
    have s2 (f : Fin n → V n) (w) : H w (∑ a, f a) = ∑ a, H w (f a) := by
      simp only [H, map_sum, Finset.smul_sum, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        Finset.sum_div]
    conv_rhs => rw [hu ξ, hu ζ, s1]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [s2]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hl, hr]
    ring
  refine ⟨pairForm fun a b => H (coordVec a) (coordVec b), isType_pairForm _, isReal_pairForm fun a b => hc _ _,
    fun ξ ζ => ?_⟩
  simp only [eval₂_eq, coef_pairForm, mul_sub, Finset.sum_sub_distrib, hsum]
  simp only [H]
  rw [ha ξ ζ, ha (Complex.I • ξ) ζ, hI']
  push_cast
  ring

theorem contDiffAt_repr {α : V n → Alt n} {v : V n} {β : V n → V n → V n → ℝ}
    (hβ : ∀ ξ ζ, ContDiffAt ℝ ∞ (fun u => β u ξ ζ) v)
    (h : ∀ᶠ u in 𝓝 v, IsType 1 1 (α u) ∧ ∀ ξ ζ, eval₂ (α u) ξ ζ = (β u ξ ζ : ℝ)) (S : Finset (Fin (n + n))) :
    ContDiffAt ℝ ∞ (fun u => (bas n).repr (α u) S) v := by
  have hc (ξ ζ) : ContDiffAt ℝ ∞ (fun u => (β u ξ ζ : ℂ)) v := Complex.ofRealCLM.contDiff.contDiffAt.comp v (hβ ξ ζ)
  have : ContDiffAt ℝ ∞ (fun u => ∑ a : Fin n, ∑ b : Fin n, if {a.castAdd n, b.natAdd n} = S then
      ((β u (coordVec a) (coordVec b) : ℂ) + Complex.I * (β u (coordVec a) (Complex.I • coordVec b) : ℂ)) / 2
      else 0) v := by
    refine ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => ?_
    split_ifs
    · exact ((hc _ _).add (contDiffAt_const.mul (hc _ _))).div_const _
    · exact contDiffAt_const
  refine this.congr_of_eventuallyEq ?_
  filter_upwards [h] with u hu
  rw [eq_pairForm hu.1, repr_pairForm]
  simp only [coef_eq, hu.2]

end Point

section Charts

variable {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {A : Over S} [GrpObj A] {g D D' : ℕ}
  {w : VMetric p (omega A) g} {σ : k →+* ℂ} {c c' : AlgChart p σ D} {τ τ' : V D → Matrix (Fin g) (Fin g) ℂ}
  {ex ex' : Pt (V D) g → CxPts (A.hom ≫ p) σ}

theorem eventually_chart (H : IsPeriodChart w c τ ex) (a : AlgChart (A.hom ≫ p) σ D') {Q : Pt (V D) g}
    (hQ : Q ∈ cov c.e.target g) (ha : ex Q ∈ a.e.source) :
    ∀ᶠ R in 𝓝 Q, R ∈ cov c.e.target g ∧ ex R ∈ a.e.source ∧ DifferentiableAt ℂ (fun x => a.e (ex x)) R := by
  have hB : IsOpen (cov c.e.target g) := c.e.open_target.prod isOpen_univ
  have h1 : ∀ᶠ R in 𝓝 Q, ex R ∈ a.e.source :=
    ((GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo H.2.1).continuousAt (hB.mem_nhds hQ)).preimage_mem_nhds
      (a.e.open_source.mem_nhds ha)
  filter_upwards [h1, hB.mem_nhds hQ] with R h₁ h₂
  exact ⟨h₂, h₁, GlobalTheory.TrueCx.TorHolo.differentiableAt_chart hB H.2.1 a h₂ h₁⟩

theorem exists_section [QuasiSeparated A.hom] (hg : SmoothOfRelativeDimension g A.hom) (H : IsPeriodChart w c τ ex)
    (a : AlgChart (A.hom ≫ p) σ D') {Q : Pt (V D) g} (hQ : Q ∈ cov c.e.target g) (ha : ex Q ∈ a.e.source) :
    ∃ s : V D' → Pt (V D) g, s (a.e (ex Q)) = Q ∧ ∀ᶠ ξ in 𝓝 (a.e (ex Q)), ContDiffAt ℂ ω s ξ ∧ ξ ∈ a.e.target ∧
      s ξ ∈ cov c.e.target g ∧ ex (s ξ) = a.e.symm ξ ∧
      ∀ u, fderiv ℂ (fun x => a.e (ex x)) (s ξ) (fderiv ℂ s ξ u) = u := by
  have hev := eventually_chart H a hQ ha
  let Φ : Pt (V D) g → V D' := fun x => a.e (ex x)
  have hf : ContDiffAt ℂ ω Φ Q := SCV.contDiffAt_of_differentiableOn
    (s := {R | R ∈ cov c.e.target g ∧ ex R ∈ a.e.source ∧ DifferentiableAt ℂ (fun x => a.e (ex x)) R})
    (fun R hR => hR.2.2.differentiableWithinAt) hev _
  have hb := PeriodChartOnto.fderiv_bijective k S p A g hg w σ D D' c τ ex H a Q hQ ha
  let f' : Pt (V D) g ≃L[ℂ] V D' := (LinearEquiv.ofBijective (fderiv ℂ Φ Q).toLinearMap hb).toContinuousLinearEquiv
  have hf' : HasFDerivAt Φ (f' : Pt (V D) g →L[ℂ] V D') Q := by
    have : (f' : Pt (V D) g →L[ℂ] V D') = fderiv ℂ Φ Q := ContinuousLinearMap.ext fun _ => rfl
    rw [this]
    exact hev.self_of_nhds.2.2.hasFDerivAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  let s := hf.localInverse hf' hn
  have hs0 : s (Φ Q) = Q := hf.localInverse_apply_image hf' hn
  have hs : ContDiffAt ℂ ω s (Φ Q) := hf.to_localInverse hf' hn
  have hr : ∀ᶠ ξ in 𝓝 (Φ Q), Φ (s ξ) = ξ := (hf.hasStrictFDerivAt' hf' hn).eventually_right_inverse
  have ht : Tendsto s (𝓝 (Φ Q)) (𝓝 Q) := by
    have := hs.continuousAt.tendsto
    rwa [hs0] at this
  refine ⟨s, hs0, ?_⟩
  filter_upwards [hs.eventually (by simp), a.e.open_target.mem_nhds (a.e.map_source ha), ht.eventually hev,
    hr.eventually_nhds] with ξ h₁ h₂ h₃ h₄
  refine ⟨h₁, h₂, h₃.1, ?_, fun u => ?_⟩
  · rw [← a.e.left_inv h₃.2.1]
    exact congrArg a.e.symm h₄.self_of_nhds
  · have d := (h₃.2.2.hasFDerivAt.comp ξ (h₁.differentiableAt hn).hasFDerivAt).congr_of_eventuallyEq
      (f₁ := id) (h₄.mono fun _ h => h.symm)
    exact congrArg (· u) (d.unique (hasFDerivAt_id ξ))

theorem flat_form_chart_independent [QuasiSeparated A.hom] (hg : SmoothOfRelativeDimension g A.hom) (H : IsPeriodChart w c τ ex)
    (H' : IsPeriodChart w c' τ' ex') (a : AlgChart (A.hom ≫ p) σ D') {P P' : Pt (V D) g}
    (hP : P ∈ cov c.e.target g) (hP' : P' ∈ cov c'.e.target g) (e : ex' P' = ex P) (ha : ex P ∈ a.e.source)
    {u v u' v' : Pt (V D) g}
    (hu : fderiv ℂ (fun x => a.e (ex x)) P u = fderiv ℂ (fun x => a.e (ex' x)) P' u')
    (hv : fderiv ℂ (fun x => a.e (ex x)) P v = fderiv ℂ (fun x => a.e (ex' x)) P' v') :
    om0 τ P ![u, v] = om0 τ' P' ![u', v'] := by
  have ha' : ex' P' ∈ a.e.source := e ▸ ha
  obtain ⟨s, hs0, hs⟩ := exists_section hg H' a hP' ha'
  rw [e] at hs0 hs
  have hev := eventually_chart H a hP ha
  have hΦ := hev.self_of_nhds.2.2
  let ψ : Pt (V D) g → Pt (V D) g := fun x => s (a.e (ex x))
  have hψ0 : ψ P = P' := hs0
  have hsd := (hs.self_of_nhds.1.differentiableAt (by simp)).hasFDerivAt
  have hψd : HasFDerivAt ψ ((fderiv ℂ s (a.e (ex P))).comp (fderiv ℂ (fun x => a.e (ex x)) P)) P :=
    HasFDerivAt.comp (g := s) (f := fun x => a.e (ex x)) P hsd hΦ.hasFDerivAt
  have hψ : ∀ᶠ Q in 𝓝 P, ContinuousAt ψ Q ∧ ψ Q ∈ cov c'.e.target g ∧ ex' (ψ Q) = ex Q := by
    filter_upwards [hev, hΦ.continuousAt.tendsto.eventually hs] with Q h₁ h₂
    exact ⟨ContinuousAt.comp (g := s) (f := fun x => a.e (ex x)) h₂.1.continuousAt h₁.2.2.continuousAt,
      h₂.2.2.1, h₂.2.2.2.1.trans (a.e.left_inv h₁.2.1)⟩
  have hinj := (PeriodChartOnto.fderiv_bijective k S p A g hg w σ D D' c' τ' ex' H' a P' hP' ha').1
  have hd (x x' : Pt (V D) g)
      (h : fderiv ℂ (fun x => a.e (ex x)) P x = fderiv ℂ (fun x => a.e (ex' x)) P' x') : x' = fderiv ℂ ψ P x := by
    apply hinj
    have := hs.self_of_nhds.2.2.2.2 (fderiv ℂ (fun x => a.e (ex x)) P x)
    rw [hs0] at this
    rw [hψd.fderiv, ContinuousLinearMap.comp_apply, this, h]
  have hor := GlobalTheory.T.period_chart_transition_holomorphic k S p A g w σ D c c' τ τ' ex ex' H H' P hP ψ hψd.differentiableAt hψ
  have vert := GlobalTheory.T.period_chart_transition_differentiable k S p A g w σ D c c' τ τ' ex ex' H H' P hP ψ hψd.differentiableAt hψ
  rw [hψ0] at hor vert
  obtain ⟨-, -, -, -, -, -, -, hh, -, -, -, -, -, -, -, hker⟩ :=
    ((FlatCubicalProof.flatCubical g).1 (V D) c.e.target τ H.1).1
  obtain ⟨-, -, -, -, -, -, -, hh', -⟩ := ((FlatCubicalProof.flatCubical g).1 (V D) c'.e.target τ' H'.1).1
  have dec (x : Pt (V D) g) : ∃ t : Fin g → ℂ, dflat τ P x = dflat τ P (0, t) ∧
      dflat τ' P' (fderiv ℂ ψ P x) = dflat τ' P' (0, (fderiv ℂ ψ P (0, t)).2) := by
    obtain ⟨w0, hw0, -⟩ := (hker P hP).2 x.1
    have hx : x = (x.1, w0) + (0, x.2 - w0) := Prod.ext (by simp) (by simp)
    refine ⟨x.2 - w0, ?_, ?_⟩
    · conv_lhs => rw [hx, map_add, hw0, zero_add]
    · conv_lhs => rw [hx, map_add, map_add, hor _ hw0, zero_add]
      exact congrArg _ (Prod.ext (vert _ 0).1 rfl)
  obtain ⟨s₁, a₁, b₁⟩ := dec u
  obtain ⟨s₂, a₂, b₂⟩ := dec v
  rw [hd u u' hu, hd v v' hv]
  change riem (dflat τ P u) (dflat τ P v) = riem (dflat τ' P' (fderiv ℂ ψ P u)) (dflat τ' P' (fderiv ℂ ψ P v))
  rw [a₁, a₂, b₁, b₂]
  exact (hh P hP s₁ s₂).trans (by rw [← (vert s₁ s₂).2]; exact (hh' P' hP' _ _).symm)

end Charts

section Glue

variable {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {A : Over S} [GrpObj A] {g D' : ℕ}
  {σ : k →+* ℂ}

def IsFlatAt (w : VMetric p (omega A) g) (D : ℕ) (a : AlgChart (A.hom ≫ p) σ D') (y : CxPts (A.hom ≫ p) σ)
    (α : Alt D') : Prop :=
  IsType 1 1 α ∧ IsReal α ∧ ∀ (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ)
    (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex → ∀ P ∈ cov c.e.target g, y = ex P →
      ∀ u v : Pt (V D) g, eval₂ α (fderiv ℂ (fun x => a.e (ex x)) P u) (fderiv ℂ (fun x => a.e (ex x)) P v) =
        om0 τ P ![u, v]

variable {w : VMetric p (omega A) g} {D : ℕ}

theorem exists_lift (hch : ∀ y : CxPts p σ, ∃ (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ)
      (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), y ∈ c.e.source ∧ IsPeriodChart w c τ ex) (y : CxPts (A.hom ≫ p) σ) :
    ∃ (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ),
      IsPeriodChart w c τ ex ∧ ∃ P ∈ cov c.e.target g, y = ex P := by
  let b : CxPts p σ := Points.PtsOver.map A.hom rfl _ y
  obtain ⟨c, τ, ex, hy, H⟩ := hch b
  have hv : c.e b ∈ c.e.target := c.e.map_source hy
  obtain ⟨z, hz⟩ := (H.isUnifChart.2.2 _ hv).2.1 y (by rw [c.e.left_inv hy]; rfl)
  exact ⟨c, τ, ex, H, (c.e b, z), ⟨hv, trivial⟩, hz.symm⟩

def riemB (g : ℕ) : Fl g →ₗ[ℝ] Fl g →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ riem
    (fun x y z => by simp only [riem, Pi.add_apply, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun t x y => by simp only [riem, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun x y z => by simp only [riem, Pi.add_apply, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun t x y => by simp only [riem, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring)

theorem exists_isFlatAt [QuasiSeparated A.hom] (hg : SmoothOfRelativeDimension g A.hom) {c : AlgChart p σ D}
    {τ : V D → Matrix (Fin g) (Fin g) ℂ} {ex : Pt (V D) g → CxPts (A.hom ≫ p) σ} (H : IsPeriodChart w c τ ex)
    (a : AlgChart (A.hom ≫ p) σ D') {P : Pt (V D) g} (hP : P ∈ cov c.e.target g) (ha : ex P ∈ a.e.source) :
    ∃ α, IsFlatAt w D a (ex P) α := by
  have hb := PeriodChartOnto.fderiv_bijective k S p A g hg w σ D D' c τ ex H a P hP ha
  let f' : Pt (V D) g ≃ₗ[ℂ] V D' := LinearEquiv.ofBijective (fderiv ℂ (fun x => a.e (ex x)) P).toLinearMap hb
  let T : V D' →ₗ[ℝ] Fl g := (dflat τ P).toLinearMap ∘ₗ (f'.symm.toLinearMap.restrictScalars ℝ)
  have hβ (ξ ζ) : (riemB g).compl₁₂ T T ξ ζ = om0 τ P ![f'.symm ξ, f'.symm ζ] := rfl
  obtain ⟨-, -, -, -, -, -, hI, -⟩ := ((FlatCubicalProof.flatCubical g).1 (V D) c.e.target τ H.1).1
  obtain ⟨α, h₁, h₂, h₃⟩ := exists_form ((riemB g).compl₁₂ T T) (fun ξ ζ => by
    change riem _ _ = -riem _ _
    simp only [riem, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring) (fun ξ ζ => by
    rw [hβ, hβ, map_smul, map_smul, hI P hP])
  refine ⟨α, h₁, h₂, fun c' τ' ex' H' P' hP' e u v => ?_⟩
  rw [h₃, hβ, flat_form_chart_independent hg H H' a hP hP' e.symm ha (f'.apply_symm_apply _) (f'.apply_symm_apply _)]

theorem IsFlatAt.compat [QuasiSeparated A.hom] (hg : SmoothOfRelativeDimension g A.hom) {c : AlgChart p σ D}
    {τ : V D → Matrix (Fin g) (Fin g) ℂ} {ex : Pt (V D) g → CxPts (A.hom ≫ p) σ} (H : IsPeriodChart w c τ ex)
    {a a' : AlgChart (A.hom ≫ p) σ D'} {P : Pt (V D) g} (hP : P ∈ cov c.e.target g) (ha : ex P ∈ a.e.source)
    (ha' : ex P ∈ a'.e.source) {α α' : Alt D'} (h : IsFlatAt w D a (ex P) α) (h' : IsFlatAt w D a' (ex P) α') :
    α = CxForm.pull (fderiv ℂ (a'.e ∘ a.e.symm) (a.e (ex P))) α' := by
  have hb := PeriodChartOnto.fderiv_bijective k S p A g hg w σ D D' c τ ex H a P hP ha
  have hev := eventually_chart H a hP ha
  have hd : DifferentiableAt ℂ (a'.e ∘ a.e.symm) (a.e (ex P)) :=
    (a.holo_trans a').differentiableAt ((a.e.isOpen_inter_preimage_symm a'.e.open_source).mem_nhds
      ⟨a.e.map_source ha, by rw [mem_preimage, a.e.left_inv ha]; exact ha'⟩)
  have hc := (HasFDerivAt.comp (f := fun x => a.e (ex x)) P hd.hasFDerivAt
    hev.self_of_nhds.2.2.hasFDerivAt).congr_of_eventuallyEq (f₁ := fun x => a'.e (ex x)) (by
      filter_upwards [hev] with R hR
      simp only [Function.comp_apply, a.e.left_inv hR.2.1])
  refine eq_of_eval₂ h.1 (CxForm.isType_pull_linear _ _ _ _ _ _ h'.1) fun ξ ζ => ?_
  obtain ⟨u, rfl⟩ := hb.2 ξ
  obtain ⟨v, rfl⟩ := hb.2 ζ
  rw [eval₂_pull _ h'.1, h.2.2 c τ ex H P hP rfl, ← h'.2.2 c τ ex H P hP rfl, hc.fderiv]
  rfl

theorem exists_local [QuasiSeparated A.hom] (hg : SmoothOfRelativeDimension g A.hom) {c : AlgChart p σ D}
    {τ : V D → Matrix (Fin g) (Fin g) ℂ} {ex : Pt (V D) g → CxPts (A.hom ≫ p) σ} (H : IsPeriodChart w c τ ex)
    {a : AlgChart (A.hom ≫ p) σ D'} {P : Pt (V D) g} (hP : P ∈ cov c.e.target g) (ha : ex P ∈ a.e.source)
    {α : V D' → Alt D'} (hα : ∀ ξ ∈ a.e.target, IsFlatAt w D a (a.e.symm ξ) (α ξ)) :
    ∃ X : V D' → Fl g, ContDiffAt ℝ ∞ X (a.e (ex P)) ∧ ∀ᶠ ξ in 𝓝 (a.e (ex P)), IsType 1 1 (α ξ) ∧
      ∀ u v, eval₂ (α ξ) u v = (riem (fderiv ℝ X ξ u) (fderiv ℝ X ξ v) : ℝ) := by
  obtain ⟨s, hs0, hs⟩ := exists_section hg H a hP ha
  obtain ⟨-, hA, -⟩ := ((FlatCubicalProof.flatCubical g).1 (V D) c.e.target τ H.1).1
  refine ⟨flat τ ∘ s, ContDiffAt.comp _ (by rw [hs0]; exact (hA P hP).contDiffAt)
    ((hs.self_of_nhds.1.of_le le_top).restrict_scalars ℝ), ?_⟩
  filter_upwards [hs] with ξ ⟨h₁, h₂, h₃, h₄, h₅⟩
  refine ⟨(hα ξ h₂).1, fun u v => ?_⟩
  have d := (hA _ h₃).differentiableAt.hasFDerivAt.comp ξ
    ((h₁.differentiableAt (by simp)).hasFDerivAt.restrictScalars ℝ)
  have := (hα ξ h₂).2.2 c τ ex H (s ξ) h₃ h₄.symm (fderiv ℂ s ξ u) (fderiv ℂ s ξ v)
  rw [h₅, h₅] at this
  rw [this, d.fderiv]
  rfl

theorem IsFlatAt.swap [QuasiSeparated A.hom] (hg : SmoothOfRelativeDimension g A.hom) {c : AlgChart p σ D}
    {τ : V D → Matrix (Fin g) (Fin g) ℂ} {ex : Pt (V D) g → CxPts (A.hom ≫ p) σ} (H : IsPeriodChart w c τ ex)
    {a : AlgChart (A.hom ≫ p) σ D'} {a' : AlgChart (A.hom ≫ p) ((starRingEnd ℂ).comp σ) D'} {P : Pt (V D) g}
    (hP : P ∈ cov c.e.target g) (ha : ex P ∈ a.e.source)
    (ha' : conjPts (A.hom ≫ p) rfl (ex P) ∈ a'.e.source)
    (hch : ∀ z ∈ a.e.source, ∀ z' ∈ a'.e.source, z'.1 = spMap (starRingEnd ℂ) ≫ z.1 →
      ∀ i, a'.e z' i = conj (a.e z i))
    {α α' : Alt D'} (h : IsFlatAt w D a (ex P) α) (h' : IsFlatAt w D a' (conjPts (A.hom ≫ p) rfl (ex P)) α') :
    CxForm.swap α' = -α := by
  have H' := GlobalTheory.T.period_chart_conjugate k S p A g w σ D c τ ex H
  set ex' : Pt (V D) g → CxPts (A.hom ≫ p) ((starRingEnd ℂ).comp σ) :=
    fun P => conjPts (A.hom ≫ p) rfl (ex (conjCoord D P.1, star P.2)) with hex'
  have cc (m : ℕ) (v : V m) : conjCoord m (conjCoord m v) = v := (conjCoord m).left_inv v
  let J : Pt (V D) g →L[ℝ] Pt (V D) g :=
    (ShFam.conjV D).toContinuousLinearEquiv.toContinuousLinearMap.prodMap (starL' ℝ).toContinuousLinearMap
  have hJ (Q) : J Q = (conjCoord D Q.1, star Q.2) := rfl
  have hJJ (Q) : J (J Q) = Q := Prod.ext (cc _ _) (star_star _)
  have e (Q) : ex' (J Q) = conjPts (A.hom ≫ p) rfl (ex Q) :=
    congrArg (fun R => conjPts (A.hom ≫ p) rfl (ex R)) (hJJ Q)
  have hP' : J P ∈ cov (conjChart (σ := (starRingEnd ℂ).comp σ) rfl c).e.target g := by
    refine ⟨?_, trivial⟩
    change conjCoord D (conjCoord D P.1) ∈ c.e.target
    rw [cc]
    exact hP.1
  have hev := eventually_chart H a hP ha
  have hev' := eventually_chart H' a' hP' (by rw [e]; exact ha')
  let K : V D' →L[ℝ] V D' := (ShFam.conjV D').toContinuousLinearEquiv.toContinuousLinearMap
  have d₁ : HasFDerivAt (fun x => a'.e (ex' (J x)))
      (((fderiv ℂ (fun x => a'.e (ex' x)) (J P)).restrictScalars ℝ).comp J) P :=
    HasFDerivAt.comp (g := fun x => a'.e (ex' x)) P (hev'.self_of_nhds.2.2.hasFDerivAt.restrictScalars ℝ)
      J.hasFDerivAt
  have d₂ : HasFDerivAt (fun x => K (a.e (ex x)))
      (K.comp ((fderiv ℂ (fun x => a.e (ex x)) P).restrictScalars ℝ)) P :=
    HasFDerivAt.comp (g := K) P K.hasFDerivAt (hev.self_of_nhds.2.2.hasFDerivAt.restrictScalars ℝ)
  have d₃ := d₁.unique (d₂.congr_of_eventuallyEq (by
    filter_upwards [hev, J.continuous.continuousAt.tendsto.eventually hev'] with R h₁ h₂
    ext i
    exact hch _ h₁.2.1 _ h₂.2.1 (congrArg (·.1) (e R)) i))
  have d (u) : fderiv ℂ (fun x => a'.e (ex' x)) (J P) (J u) =
      conjCoord D' (fderiv ℂ (fun x => a.e (ex x)) P u) := congrArg (· u) d₃
  have hb := PeriodChartOnto.fderiv_bijective k S p A g hg w σ D D' c τ ex H a P hP ha
  have t₁ : IsType 1 1 (CxForm.swap α') := by
    rw [eq_pairForm h'.1, swap_pairForm]
    exact isType_pairForm _
  have t₂ : IsType 1 1 (-α) := fun T hT => h.1 T (by simpa using hT)
  refine eq_of_eval₂ t₁ t₂ fun ξ ζ => ?_
  obtain ⟨u, rfl⟩ := hb.2 ξ
  obtain ⟨v, rfl⟩ := hb.2 ζ
  rw [eval₂_swap h'.1, eval₂_neg, ← d, ← d, h.2.2 c τ ex H P hP rfl, h'.2.2 _ _ _ H' (J P) hP' (e P).symm,
    ← Complex.ofReal_neg, ← GlobalTheory.T.flat_form_conj D g τ P u v]
  rfl

end Glue

theorem exists_flatForm : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (A : Over S) [GrpObj A] (D' : ℕ) (h' : IsRegVar (A.hom ≫ p) D') (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ w : VMetric p (omega A) g, (∀ σ (y : CxPts p σ), ∃ (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), y ∈ c.e.source ∧ IsPeriodChart w c τ ex) → ∃ Ω₀ : h'.Fld, h'.IsArForm 1 Ω₀ ∧ ∀ σ, (h'.atlas σ).del (Ω₀ σ) = 0 ∧ (h'.atlas σ).dbar (Ω₀ σ) = 0 ∧ ∀ (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex → IsFlatOn h' (Ω₀ σ) c.e.target τ ex := by
  intro k _ S p D _ A _ D' h' g hA hg w hch
  haveI : IsProper A.hom := hA.proper
  have ex0 (σ) (x : (h'.atlas σ).Pt) : ∃ α, IsFlatAt w D (show AlgChart (A.hom ≫ p) σ D' from x.1.1) x.pt α := by
    obtain ⟨c, τ, ex, H, P, hP, e⟩ := exists_lift (hch σ) x.pt
    rw [e]
    exact exists_isFlatAt hg H _ hP (e ▸ x.2)
  choose Ω hΩ using ex0
  have loc (σ) (a : AlgChart (A.hom ≫ p) σ D') (ξ) (hξ : ξ ∈ a.e.target) : ∃ X : V D' → Fl g,
      ContDiffAt ℝ ∞ X ξ ∧ ∀ᶠ ζ in 𝓝 ξ, IsType 1 1 ((h'.atlas σ).loc (Ω σ) a ζ) ∧ ∀ u v,
        eval₂ ((h'.atlas σ).loc (Ω σ) a ζ) u v = (riem (fderiv ℝ X ζ u) (fderiv ℝ X ζ v) : ℝ) := by
    obtain ⟨c, τ, ex, H, P, hP, e⟩ := exists_lift (hch σ) (a.e.symm ξ)
    have := exists_local hg H hP (e ▸ a.e.map_target hξ) (α := (h'.atlas σ).loc (Ω σ) a) fun ζ hζ => by
      have e' : (h'.atlas σ).loc (Ω σ) a ζ = Ω σ ⟨(a, a.e.symm ζ), a.e.map_target hζ⟩ := dif_pos hζ
      rw [e']
      exact hΩ σ ⟨(a, a.e.symm ζ), a.e.map_target hζ⟩
    rwa [← e, a.e.right_inv hξ] at this
  have closed (σ) (x : (h'.atlas σ).Pt) : delAt ((h'.atlas σ).loc (Ω σ) x.1.1) x.crd = 0 ∧
      dbarAt ((h'.atlas σ).loc (Ω σ) x.1.1) x.crd = 0 := by
    obtain ⟨X, h₁, h₂⟩ := loc σ x.1.1 x.crd (x.ch.map_source x.2)
    exact GlobalTheory.T.riemann_form_closed _ _ X _ _ h₁ h₂
  refine ⟨Ω, ⟨fun σ => ⟨⟨fun a T ξ hξ => ?_, ?_⟩, fun x => ⟨(hΩ σ x).1, (hΩ σ x).2.1⟩⟩, ?_⟩, fun σ =>
    ⟨funext fun x => (closed σ x).1, funext fun x => (closed σ x).2,
      fun c τ ex H P hP x e => (hΩ σ x).2.2 c τ ex H P hP e⟩⟩
  · obtain ⟨X, h₁, h₂⟩ := loc σ a ξ hξ
    refine (contDiffAt_repr (β := fun ζ u v => riem (fderiv ℝ X ζ u) (fderiv ℝ X ζ v)) (fun u v => ?_) h₂
      T).contDiffWithinAt
    have hd (u) (i) : ContDiffAt ℝ ∞ (fun ζ => fderiv ℝ X ζ u i) ξ :=
      contDiffAt_pi.1 ((h₁.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const) i
    exact ContDiffAt.sum fun i _ => ((hd _ _).mul (hd _ _)).sub ((hd _ _).mul (hd _ _))
  · rintro ⟨⟨a, y⟩, hy⟩ ⟨⟨a', y'⟩, hy'⟩ (rfl : y = y')
    obtain ⟨c, τ, ex, H, P, hP, rfl⟩ := exists_lift (hch σ) y
    exact IsFlatAt.compat hg H hP hy hy' (hΩ σ ⟨(a, _), hy⟩) (hΩ σ ⟨(a', _), hy'⟩)
  · rintro σ σ' ⟨⟨a, y⟩, hy⟩ ⟨⟨a', y'⟩, hy'⟩ e hc
    obtain rfl := PullArForm.emb_eq_conj y y' e
    obtain ⟨c, τ, ex, H, P, hP, rfl⟩ := exists_lift (hch σ) y
    obtain rfl : y' = conjPts (A.hom ≫ p) rfl (ex P) := Subtype.ext e
    rw [pow_one, neg_one_smul]
    exact IsFlatAt.swap hg H hP hy hy' hc (hΩ σ ⟨(a, _), hy⟩) (hΩ _ ⟨(a', _), hy'⟩)

end GlobalTheory.FlatGlue

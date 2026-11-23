import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDbarQuotientFormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDbarFormSubLogMetricLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtTraceNonnegOfPosFrame
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.MixDens
open GlobalTheory.CurveDens ComplexConjugate

theorem sum_formMat_eq {D : ℕ} (T : V D → V D → ℂ) (hT : IsSesq T) (ξ : V D) :
    ∑ j, ∑ l, ξ j * formMat T j l * starRingEnd ℂ (ξ l) = T ξ ξ / kappa := by
  have hv : ξ = ∑ j, ξ j • EuclideanSpace.single j (1 : ℂ) := by
    ext i; simp [EuclideanSpace.single_apply, Pi.single_apply]
  have hl : ∀ (s : Finset (Fin D)) (f : Fin D → V D) (y : V D), T (∑ i ∈ s, f i) y = ∑ i ∈ s, T (f i) y := by
    intro s f y
    induction s using Finset.induction_on with
    | empty => simpa using hT.add_left 0 0 y
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hT.add_left, ih]
  have hr : ∀ (s : Finset (Fin D)) (f : Fin D → V D) (x : V D), T x (∑ i ∈ s, f i) = ∑ i ∈ s, T x (f i) := by
    intro s f x
    induction s using Finset.induction_on with
    | empty => simpa using hT.add_right x 0 0
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hT.add_right, ih]
  have e : T ξ ξ = ∑ j, ∑ l, ξ j * T (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) *
      conj (ξ l) := by
    have h1 : T ξ ξ = T (∑ j, ξ j • EuclideanSpace.single j (1 : ℂ))
        (∑ l, ξ l • EuclideanSpace.single l (1 : ℂ)) := by rw [← hv]
    rw [h1, hl]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT.smul_left, hr, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hT.smul_right, smul_eq_mul]; ring
  rw [e, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [formMat, of_apply]
  ring

theorem isSesq_extTrace {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    {K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E} (h : MContDiffAt 1 K z)
    (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) : IsSesq (extTrace K z) := by
  have e : ∀ ξ η, extTrace K z ξ η = kappa * (secondForm K z ξ * secondFormAdj K z η).trace :=
    extTrace_eq h hp
  refine ⟨fun x x' y => ?_, fun c x y => ?_, fun x y y' => ?_, fun c x y => ?_⟩
  · simp only [e, secondForm_add_vec, Matrix.add_mul, trace_add, mul_add]
  · simp only [e, secondForm_smul_vec, Matrix.smul_mul, trace_smul, smul_eq_mul]; ring
  · simp only [e, secondFormAdj, adj, secondForm_add_vec, conjTranspose_add, Matrix.mul_add,
      Matrix.add_mul, trace_add, mul_add]
  · simp only [e, secondFormAdj, adj, secondForm_smul_vec, conjTranspose_smul, Matrix.mul_smul,
      Matrix.smul_mul, trace_smul, smul_eq_mul, Complex.star_def]; ring

theorem re_div_kappa {W : Type} (α : W → W → ℂ) (ξ : W) :
    (α ξ ξ / kappa).re = Real.pi * (2 * diagVal α ξ) := by
  have e (z : ℂ) : z / kappa = ((2 * Real.pi : ℝ) : ℂ) * (-Complex.I * z) := by
    rw [kappa]
    have := Complex.I_ne_zero
    have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    push_cast
    field_simp
    simp
  rw [e, Complex.re_ofReal_mul, diagVal]
  ring

theorem norm_dbar_projection_sq_bcMat : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ)
    (S : ShortComplex X.Modules) (h : Met p σ S.X₂ (1 + 1)) (hS : S.ShortExact) (h₁ : IsVB S.X₁ 1)
    (h₃ : IsVB S.X₃ 1), h.IsCInf → ∀ (U : X.Opens) (t : Γ(S.X₁, U)) (w : Γ(S.X₂, U)),
    IsFrame (fun _ : Fin 1 => t) → ∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source, y ∈ ptsIn p σ U → ∀ ξ : V D,
    ‖dbar (fun v => h.form w (S.f.app U t) (c.e.symm v)) (c.e y) ξ -
        h.form w (S.f.app U t) y *
          dbar (fun v => (Real.log (h.form (S.f.app U t) (S.f.app U t) (c.e.symm v)).re : ℂ)) (c.e y) ξ‖ ^ 2 =
      ((h.form (S.f.app U t) (S.f.app U t) y).re * (h.form w w y).re - ‖h.form w (S.f.app U t) y‖ ^ 2) *
        (∑ j, ∑ l, ξ j * bcMat h hS h₁ h₃ c y j l * starRingEnd ℂ (ξ l)).re := by
  intro k _ X p σ D S h hS h₁ h₃ H U t w ht c y hy hU ξ
  obtain ⟨a', ha'⟩ := Met.exists_adapted (p := p) (σ := σ) hS h₁ h₃ y
  set a := adaptedOf a' t ht with a_def
  have ha : y ∈ ptsIn p σ a.U := mem_ptsIn_inf.2 ⟨hU, ha'⟩
  set G : V D → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
    fun v => h.gram a.frame (c.e.symm v) with G_def
  set s : V D → Fin 1 ⊕ Fin 1 → ℂ :=
    fun v i => (a.mid hS).crd p σ w (c.e.symm v) (finSumFinEquiv i) with s_def
  have hs : ∀ i, DifferentiableAt ℂ (fun x => s x i) (c.e y) := fun i =>
    c.differentiableAt_ev _ hy (mem_ptsIn_inf.2 ⟨hU, ha⟩)
  have hG : MContDiffAt 1 G (c.e y) :=
    ((H.gram a.frame ha).mContDiffAt c hy).of_le (by norm_cast)
  have hp := h.eventually_posDef hS a c hy ha
  have hn : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn p σ (U ⊓ a'.U) :=
    eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn (U ⊓ a'.U))).mem_nhds
      (ChartGlue.mem_over c.e hy ha)) fun _ hv => hv.2
  have e₀ : c.e.symm (c.e y) = y := c.e.left_inv hy
  have key (v : V D) (hv : c.e.symm v ∈ ptsIn p σ (U ⊓ a'.U)) :
      h.form w (S.f.app U t) (c.e.symm v) = form (G v) (s v) (Pi.single (Sum.inl 0) 1) ∧
      h.form (S.f.app U t) (S.f.app U t) (c.e.symm v) = G v (Sum.inl 0) (Sum.inl 0) ∧
      h.form w w (c.e.symm v) = form (G v) (s v) (s v) := by
    have hv' : c.e.symm v ∈ ptsIn p σ U := (mem_ptsIn_inf.1 hv).1
    have hc := crd_adaptedOf hS a' t ht hv
    refine ⟨?_, ?_, form_eq_gram_frame h hS a w w hv hv'⟩
    · rw [form_eq_gram_frame h hS a w _ hv hv', hc]
    · rw [form_eq_gram_frame h hS a _ _ hv hv', hc, form_single]
  have k₀ := key _ (e₀.symm ▸ ha)
  rw [e₀] at k₀
  have e₁ : dbar (fun v => h.form w (S.f.app U t) (c.e.symm v)) (c.e y) =
      dbar (fun v => form (G v) (s v) (Pi.single (Sum.inl 0) 1)) (c.e y) :=
    dbar_congr (hn.mono fun v hv => (key v hv).1)
  have e₂ : dbar (fun v => (Real.log (h.form (S.f.app U t) (S.f.app U t) (c.e.symm v)).re : ℂ))
        (c.e y) = dbar (fun v => (Real.log (G v (Sum.inl 0) (Sum.inl 0)).re : ℂ)) (c.e y) :=
    dbar_congr (hn.mono fun v hv => by simp only [(key v hv).2.1])
  have main := norm_sq_dbar_proj_rank_two _ G s ξ (c.e y) hG hp hs
  have hb : bcMat h hS h₁ h₃ c y = formMat (extTrace G (c.e y)) := by
    rw [bcMat, Met.bcForm_eq hS a _ c H hy ha (Met.exists_adapted hS h₁ h₃ y).choose_spec]
    rfl
  rw [e₁, e₂, k₀.1, k₀.2.1, k₀.2.2, main, hb, sum_formMat_eq _ (isSesq_extTrace hG hp), re_div_kappa]

end GlobalTheory.MixDens

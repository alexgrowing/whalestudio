import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDbarFormSubLogMetricLeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveDens

open GlobalTheory.VBExt (AdaptedChart)
open GlobalTheory.Twist (resM app_resM)

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {S : ShortComplex X.Modules}

theorem form_eq_gram_frame {r s : ℕ} (h : Met p σ S.X₂ (r + s)) (hS : S.ShortExact)
    (a : AdaptedChart S r s) {V : X.Opens} (u w : Γ(S.X₂, V)) {x : CxPts p σ}
    (hx : x ∈ ptsIn p σ a.U) (hV : x ∈ ptsIn p σ V) :
    h.form u w x = HermFrame.form (h.gram a.frame x)
      (fun i => (a.mid hS).crd p σ u x (finSumFinEquiv i))
      (fun i => (a.mid hS).crd p σ w x (finSumFinEquiv i)) := by
  rw [h.form_eq (a.mid hS) hx u w hV, Met.gram_frame h hS a hx, form_eq_sum, form_eq_sum,
    ← finSumFinEquiv.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← finSumFinEquiv.sum_comp]
  rfl

def adaptedOf (a : AdaptedChart S 1 1) {U : X.Opens} (t : Γ(S.X₁, U))
    (ht : IsFrame fun _ : Fin 1 => t) : AdaptedChart S 1 1 where
  U := U ⊓ a.U
  e := fun _ => resM S.X₁ inf_le_left t
  t := fun i => resM S.X₂ inf_le_right (a.t i)
  he := ht.res inf_le_left
  ht := by
    simp only [app_resM]
    exact a.ht.res inf_le_right

theorem crd_adaptedOf (hS : S.ShortExact) (a : AdaptedChart S 1 1) {U : X.Opens} (t : Γ(S.X₁, U))
    (ht : IsFrame fun _ : Fin 1 => t) {x : CxPts p σ} (hx : x ∈ ptsIn p σ (adaptedOf a t ht).U) :
    (fun i => ((adaptedOf a t ht).mid hS).crd p σ (S.f.app U t) x (finSumFinEquiv i)) =
      Pi.single (Sum.inl 0) 1 := by
  have e : (adaptedOf a t ht).frame (.inl 0) = resM S.X₂ inf_le_left (S.f.app U t) :=
    app_resM _ _ _
  funext i
  rw [← Chart.crd_resM _ (S.f.app U t) (inf_le_left : (adaptedOf a t ht).U ≤ U) hx, ← e]
  refine (AdaptedChart.crd_frame hS (adaptedOf a t ht) hx i (.inl 0)).trans ?_
  rw [Matrix.one_apply, Pi.single_apply]

theorem norm_dbar_projection_sq (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (S : ShortComplex X.Modules) (h : Met p σ S.X₂ (1 + 1)) (hS : S.ShortExact) (h₁ : IsVB S.X₁ 1)
    (h₃ : IsVB S.X₃ 1) (H : h.IsCInf) (U : X.Opens) (t : Γ(S.X₁, U)) (w : Γ(S.X₂, U))
    (ht : IsFrame (fun _ : Fin 1 => t)) (c : AlgChart p σ 1) (y : CxPts p σ) (hy : y ∈ c.e.source)
    (hU : y ∈ ptsIn p σ U) :
    ‖dbar (fun v => h.form w (S.f.app U t) (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1) -
        h.form w (S.f.app U t) y *
          dbar (fun v => (Real.log (h.form (S.f.app U t) (S.f.app U t) (c.e.symm v)).re : ℂ)) (c.e y)
            (EuclideanSpace.single 0 1)‖ ^ 2 =
      ((h.form (S.f.app U t) (S.f.app U t) y).re * (h.form w w y).re -
        ‖h.form w (S.f.app U t) y‖ ^ 2) * (Real.pi * h.bcDens hS h₁ h₃ c y) := by
  obtain ⟨a', ha'⟩ := Met.exists_adapted (p := p) (σ := σ) hS h₁ h₃ y
  set a := adaptedOf a' t ht with a_def
  have ha : y ∈ ptsIn p σ a.U := mem_ptsIn_inf.2 ⟨hU, ha'⟩
  set G : ReciprocityTheory.L2DbarEstimates.V 1 → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
    fun v => h.gram a.frame (c.e.symm v) with G_def
  set s : ReciprocityTheory.L2DbarEstimates.V 1 → Fin 1 ⊕ Fin 1 → ℂ :=
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
  have key (v : ReciprocityTheory.L2DbarEstimates.V 1) (hv : c.e.symm v ∈ ptsIn p σ (U ⊓ a'.U)) :
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
  have e₃ : G (c.e y) = h.gram a.frame y := by rw [G_def]; simp only [e₀]
  have main := GlobalTheory.T.norm_dbar_form_sub_log_metric_le _ G s (EuclideanSpace.single 0 1) (c.e y) hG hp hs
  rw [e₁, e₂, k₀.1, k₀.2.1, k₀.2.2, Met.bcDens_eq hS h₁ h₃ a c H hy ha]
  exact main

end GlobalTheory.CurveDens

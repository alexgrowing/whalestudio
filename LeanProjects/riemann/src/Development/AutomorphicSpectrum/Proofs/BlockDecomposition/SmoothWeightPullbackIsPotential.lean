import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

open Set Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.MixZ

theorem isPotential_pullback_locPot : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → IsPotential A (φ.locPot.pullback F hF) := by
  intro k _ X q σ D T _ A F hF hol B φ hφ
  refine ⟨fun x j v hv => ?_, fun x x' y hy => ?_⟩
  · have hv1 : v ∈ (A.chart j).target := hv.1
    have hv2 : F ((A.chart j).symm v) ∈ ptsIn q σ (B.U (pick φ.isLB (F x))) := hv.2
    obtain ⟨W, ι, _, g, Fn, O, h₁, h₂, h₃, h₄, h₅⟩ := hφ _ _ hv2
    have hcs : ContinuousAt (fun w => F ((A.chart j).symm w)) v :=
      hF.continuousAt.comp ((A.chart j).continuousAt_symm hv1)
    have hop : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (F ⁻¹' ptsIn q σ W)) :=
      (A.chart j).isOpen_inter_preimage_symm ((isOpen_ptsIn W).preimage hF)
    have hg : ContDiffAt ℝ ∞ (fun w a => ev q σ W (g a) (F ((A.chart j).symm w))) v :=
      contDiffAt_pi.2 fun a =>
        ((hol W (g a) j v ⟨hv1, h₁⟩).restrictScalars (𝕜 := ℝ)).contDiffAt.of_le le_top
    have hc : ContDiffAt ℝ ∞ (fun w => Fn fun a => ev q σ W (g a) (F ((A.chart j).symm w))) v :=
      (h₄.contDiffAt (h₂.mem_nhds h₃)).comp v hg
    have hc' : ContDiffAt ℝ ∞ (fun w => φ.φ (pick φ.isLB (F x)) (F ((A.chart j).symm w))) v :=
      hc.congr_of_eventuallyEq (hcs.eventually h₅)
    exact (hc'.div_const 2).contDiffWithinAt
  · set i := pick φ.isLB (F x) with hi
    set i' := pick φ.isLB (F x') with hi'
    have hyi : F y ∈ ptsIn q σ (B.U i) := hy.1
    have hyi' : F y ∈ ptsIn q σ (B.U i') := hy.2
    set S : Set T := F ⁻¹' ptsIn q σ (B.U i ⊓ B.U i') with hS
    have hSo : IsOpen S := (isOpen_ptsIn _).preimage hF
    have hyS : y ∈ S := mem_ptsIn_inf.2 ⟨hyi, hyi'⟩
    set g : T → ℂ := ev q σ (B.U i ⊓ B.U i') (B.g i i').val ∘ F with hg
    have hgh : A.HoloOn S g := hol _ _
    have hgc : ContinuousOn g S :=
      (continuousOn_ev (B.g i i').val).comp hF.continuousOn fun _ h => h
    have h0 : g y ≠ 0 := gv_ne_zero hyi hyi'
    refine ⟨S ∩ (fun z => g z * (g y)⁻¹) ⁻¹' Complex.slitPlane,
      (hgc.mul continuousOn_const).isOpen_inter_preimage hSo Complex.isOpen_slitPlane,
      ⟨hyS, ?_⟩, fun z => Complex.log (g z * (g y)⁻¹) + (Real.log ‖g y‖ : ℂ),
      fun j v hv => ?_, fun z hz => ?_⟩
    · simp [mul_inv_cancel₀ h0]
    · have ha : AnalyticAt ℂ (g ∘ (A.chart j).symm) v := hgh j v ⟨hv.1, hv.2.1⟩
      exact ((ha.mul analyticAt_const).clog hv.2.2).add analyticAt_const
    · have hzS : F z ∈ ptsIn q σ (B.U i ⊓ B.U i') := hz.1.1.1
      have hz0 : g z ≠ 0 := left_ne_zero_of_mul (Complex.slitPlane_ne_zero hz.1.1.2)
      have e := φ.half_eq (mem_ptsIn_inf.1 hzS).1 (mem_ptsIn_inf.1 hzS).2
      have e' : Real.log ‖gv q σ B i i' (F z)‖ = Real.log ‖g z‖ := rfl
      change φ.φ i (F z) / 2 - φ.φ i' (F z) / 2 = _
      rw [e, e', Complex.add_re, Complex.log_re, Complex.ofReal_re, ← div_eq_mul_inv, norm_div,
        Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 h0), sub_add_cancel,
        add_sub_cancel_left]

end GlobalTheory.CompanionTheory.MixZ

import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothPullbackToFrameDomainStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondDerivComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

namespace GlobalTheory.KaeLaws

theorem ddc_inv_loc {ι : Type} [Fintype ι] {p q : ℕ} {f : Pt ι p q → ℝ} {U : Set (ι × Fin p × Fin q → ℂ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ (fun v => f (unflat v)) U) {g : ι → GL (Fin p ⊕ Fin q) ℂ}
    (hg : g ∈ UpqI ι p q) (hinv : ∀ z ∈ DomI ι p q, f (moebI g z) = f z) {z : Pt ι p q} (hz : z ∈ DomI ι p q)
    (hzU : flat (moebI g z) ∈ U) (ξ : Pt ι p q) :
    ddc f (moebI g z) (fun τ => tanAct (g τ) (z τ) (ξ τ)) = ddc f z ξ := by
  obtain ⟨ho, H⟩ := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_and_fderiv_moebI ι p q
  obtain ⟨hd, hD⟩ := H g hg
  have hz' : flat z ∈ DomFlat ι p q := hz
  have han := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn ho hd _ hz'
  have hF : ContDiffAt ℝ 2 (fun v => (f (unflat v) : ℂ)) (flat (moebI g z)) :=
    ((Complex.ofRealCLM.contDiff.contDiffAt).comp _ (hf.contDiffAt (hU.mem_nhds hzU))).of_le
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have h2 : ((fun v => (f (unflat v) : ℂ)) ∘ fun v => flat (moebI g (unflat v))) =ᶠ[nhds (flat z)]
      fun v => (f (unflat v) : ℂ) := by
    filter_upwards [ho.mem_nhds hz'] with v hv
    rw [Function.comp_apply, GlobalTheory.BetaInv.unflat_flat', hinv _ hv]
  have h3 := hD z hz ξ
  have h4 : (fun v => flat (moebI g (unflat v))) (flat z) = flat (moebI g z) := by
    simp only [GlobalTheory.BetaInv.unflat_flat']
  rw [← h4] at hF
  have h5 := GlobalTheory.BetaInv.levi_comp (φ := fun v => flat (moebI g (unflat v))) (x := flat z) hF han (flat ξ)
  rw [h3, GlobalTheory.BetaInv.levi_congr h2] at h5
  simp only [GlobalTheory.BetaInv.unflat_flat'] at h5
  rw [GlobalTheory.BetaInv.ddc_eq, GlobalTheory.BetaInv.ddc_eq, h5]

theorem inv_and_bound : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (x : ToroidalCompactificationData s) (a : Pt D.what₂.Tau j (N - j) → Pt D.what₂.Tau j (N - j) →ₗ[ℂ] Pt D.what₂.Tau j (N - j) →ₗ⋆[ℂ] ℂ), (∀ z ∈ DomI D.what₂.Tau j (N - j), ∀ ξ ζ, a z ζ ξ = starRingEnd ℂ (a z ξ ζ)) → (∀ W φ, IsPotential (manifold s.T.Z κ.σ₀) (x.kae κ.σ₀) W φ → ∀ z ∈ DomI D.what₂.Tau j (N - j), s.toCpt L k z ∈ W → ∀ ξ, (a z ξ ξ).re = ddc (φ ∘ s.toCpt L k) z ξ) → (∀ g ∈ gammaU (s.fd k) s.j_le (s.lab L k), ∀ z ∈ DomI D.what₂.Tau j (N - j), ∀ ξ ζ, a (moebI g z) (fun t => tanAct (g t) (z t) (ξ t)) (fun t => tanAct (g t) (z t) (ζ t)) = a z ξ ζ) ∧ ∀ i, ∀ z ∈ DomI D.what₂.Tau j (N - j), ∀ ξ, 2 * x.m * x.cst * |ddc (fun w => Real.exp 1 - Real.log (x.nrm κ.σ₀ i (s.toCpt L k w) ^ 2)) z ξ| ≤ Real.exp 1 * (a z ξ ξ).re := by
  intro D A N j S κ s L k x a hherm hkae
  have hT := GlobalTheory.T.smooth_pullback_to_frame_domain D A N j S κ s L k
  constructor
  · intro g hg z hz ξ ζ
    have hgU : g ∈ UpqI D.what₂.Tau j (N - j) := gammaU_le _ _ _ (s.p0_eq k) hg
    have hmz : moebI g z ∈ DomI D.what₂.Tau j (N - j) := fun t => moeb_mem (hgU t (Set.mem_univ _)) (hz t)
    obtain ⟨W, φ, hyW, hpot⟩ := (x.kae_kaehler κ.σ₀).1 (s.toCpt L k z)
    have hmW : s.toCpt L k (moebI g z) ∈ W := by rwa [s.toCpt_moeb L k hg hz]
    obtain ⟨hUo, hsm, -⟩ := hT W φ hpot.1 hpot.2.1
    let Tl : Pt D.what₂.Tau j (N - j) →ₗ[ℂ] Pt D.what₂.Tau j (N - j) :=
      { toFun := fun v t => tanAct (g t) (z t) (v t)
        map_add' := fun u v => funext fun t => by simp [tanAct, Matrix.mul_add, Matrix.add_mul]
        map_smul' := fun c v => funext fun t => by simp [tanAct, Matrix.mul_smul, Matrix.smul_mul] }
    have hdiag : ∀ v, a (moebI g z) (Tl v) (Tl v) = a z v v := by
      intro v
      refine Complex.ext ?_ ((Complex.conj_eq_iff_im.1 (hherm _ hmz (Tl v) (Tl v)).symm).trans
        (Complex.conj_eq_iff_im.1 (hherm _ hz v v).symm).symm)
      rw [hkae W φ hpot _ hmz hmW, hkae W φ hpot z hz hyW]
      exact ddc_inv_loc hUo hsm hgU (fun w hw => by simp only [Function.comp_apply, s.toCpt_moeb L k hg hw]) hz
        ⟨hmz, hmW⟩ v
    let b := ((a (moebI g z)).comp Tl).compl₂ Tl - a z
    have e : ∀ v, b v v = 0 := fun v => sub_eq_zero.2 (hdiag v)
    have e1 := e (ξ + ζ)
    have e2 := e (ξ + Complex.I • ζ)
    simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, e, smul_eq_mul, Complex.conj_I,
      RingHom.id_apply] at e1 e2
    have : b ξ ζ = 0 := by
      linear_combination (1 / 2) * e1 + (Complex.I / 2) * e2 + ((b ξ ζ - b ζ ξ) / 2) * Complex.I_mul_I
    exact sub_eq_zero.1 this
  · intro i z hz ξ
    obtain ⟨W, φ, hyW, hpot⟩ := (x.kae_kaehler κ.σ₀).1 (s.toCpt L k z)
    obtain ⟨c, hc⟩ := (manifold s.T.Z κ.σ₀).cover (s.toCpt L k z)
    have hc' : s.toCpt L k z ∈ (c : AlgChart (genStr s.T.Z) κ.σ₀ S.Dw.dim).e.source := hc
    have hnot : ¬ LiesIn (s.toCpt L k z) (x.cpt i) := fun h =>
      s.not_liesIn_toCpt L k z ((x.liesIn_genBd_iff _).2 ⟨i, h⟩)
    have h1 := hkae W φ hpot z hz hyW ξ
    have h2 := (hT W φ hpot.1 hpot.2.1).2.2 c z hz hyW hc' ξ
    have h3 := hpot.2.2 c _ hc' hyW
      (fderiv ℂ (fun v => c.e (s.toCpt L k (unflat v))) (flat z) (flat ξ)).ofLp
    have hψ : (manifold s.T.Z κ.σ₀).SmoothOn {y | ¬ LiesIn y (x.cpt i)}
        (fun y => Real.exp 1 - Real.log (x.nrm κ.σ₀ i y ^ 2)) :=
      fun c => contDiffOn_const.sub ((x.nrm_div κ.σ₀ i).smoothOn_log c)
    have h4 := (hT _ _ (isOpen_not_liesIn _) hψ).2.2 c z hz hnot hc' ξ
    have h5 := x.cst_small κ.σ₀ i c _ hc' hnot
      (fderiv ℂ (fun v => c.e (s.toCpt L k (unflat v))) (flat z) (flat ξ)).ofLp
    rw [h1, h2, ← h3]
    exact (congrArg (fun t => 2 * (x.m : ℝ) * x.cst * |t|) h4).le.trans h5

end GlobalTheory.KaeLaws

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatDetNeZeroOfSymplectic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelActionPreservesFlatForm
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaRR.RatDense

open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Sp Sp.mat den moeb)

variable {g : ℕ}

abbrev Par (g : ℕ) : Type := (Fin g ⊕ Fin g) → (Fin g ⊕ Fin g) → ℂ

def numC (Γ : Par g) (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (Matrix.of Γ).toBlocks₁₁ * τ + (Matrix.of Γ).toBlocks₁₂

def denC (Γ : Par g) (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (Matrix.of Γ).toBlocks₂₁ * τ + (Matrix.of Γ).toBlocks₂₂

def quotC (x : Par g × symMat g) : Fin g → Fin g → ℂ :=
  numC x.1 (tauU x.2) * (denC x.1 (tauU x.2))⁻¹

def actC (Γ : Par g) (s : symMat g) : symMat g := symPart (quotC (Γ, s))

def ofSp (γ : Sp g) : Par g := fun i j => ((γ.1 i j : ℝ) : ℂ)

theorem continuous_ofSp : Continuous (ofSp (g := g)) :=
  continuous_pi fun i => continuous_pi fun j => Complex.continuous_ofReal.comp
    ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))

section Smooth

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {m : ℕ}

theorem contDiff_det_of_entries' {M : X → Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ i j, ContDiff ℂ ∞ fun x => M x i j) : ContDiff ℂ ∞ fun x => (M x).det := by
  have e : (fun x => (M x).det) = fun x =>
      ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, M x (σ j) j := by
    funext x; rw [Matrix.det_apply']
  rw [e]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun j _ => h _ _)

theorem contDiff_adjugate_of_entries {M : X → Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ i j, ContDiff ℂ ∞ fun x => M x i j) (i j : Fin m) :
    ContDiff ℂ ∞ fun x => (M x).adjugate i j := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det_of_entries' fun a b => ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact h a b

theorem contDiffAt_inv_of_entries {M : X → Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ i j, ContDiff ℂ ∞ fun x => M x i j) {x₀ : X} (h₀ : (M x₀).det ≠ 0) (i j : Fin m) :
    ContDiffAt ℂ ∞ (fun x => (M x)⁻¹ i j) x₀ := by
  have e : (fun x => (M x)⁻¹ i j) = fun x => ((M x).det)⁻¹ * (M x).adjugate i j := by
    funext x
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [e]
  exact ((contDiff_det_of_entries' h).contDiffAt.inv h₀).mul
    (contDiff_adjugate_of_entries h i j).contDiffAt

end Smooth

theorem contDiff_par_apply (i j : Fin g ⊕ Fin g) :
    ContDiff ℂ ∞ fun x : Par g × symMat g => x.1 i j :=
  (contDiff_apply_apply ℂ ℂ i j).comp contDiff_fst

theorem contDiff_tauU_apply (i j : Fin g) :
    ContDiff ℂ ∞ fun x : Par g × symMat g => tauU x.2 i j :=
  (contDiff_apply_apply ℂ ℂ i j).comp ((symMat g).subtypeL.contDiff.comp contDiff_snd)

theorem contDiff_numC (i j : Fin g) :
    ContDiff ℂ ∞ fun x : Par g × symMat g => numC x.1 (tauU x.2) i j := by
  simp only [numC, Matrix.add_apply, Matrix.mul_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
    Matrix.of_apply]
  exact (ContDiff.sum fun k _ => (contDiff_par_apply _ _).mul (contDiff_tauU_apply _ _)).add
    (contDiff_par_apply _ _)

theorem contDiff_denC (i j : Fin g) :
    ContDiff ℂ ∞ fun x : Par g × symMat g => denC x.1 (tauU x.2) i j := by
  simp only [denC, Matrix.add_apply, Matrix.mul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
    Matrix.of_apply]
  exact (ContDiff.sum fun k _ => (contDiff_par_apply _ _).mul (contDiff_tauU_apply _ _)).add
    (contDiff_par_apply _ _)

theorem contDiffAt_quotC {x₀ : Par g × symMat g} (h₀ : (denC x₀.1 (tauU x₀.2)).det ≠ 0) :
    ContDiffAt ℂ ∞ quotC x₀ := by
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  simp only [quotC, Matrix.mul_apply]
  exact ContDiffAt.sum fun k _ => (contDiff_numC i k).contDiffAt.mul
    (contDiffAt_inv_of_entries (M := fun x : Par g × symMat g => denC x.1 (tauU x.2))
      contDiff_denC h₀ k j)

theorem contDiffAt_actC {x₀ : Par g × symMat g} (h₀ : (denC x₀.1 (tauU x₀.2)).det ≠ 0) :
    ContDiffAt ℂ ∞ (Function.uncurry actC) x₀ :=
  (GlobalTheory.UnivAction.symPartL g).contDiff.contDiffAt.comp x₀ (contDiffAt_quotC h₀)

theorem det_denC_ne_zero (γ : Sp g) {s : symMat g} (hs : s ∈ siegel g) :
    (denC (ofSp γ) (tauU s)).det ≠ 0 := by
  have h := ((GlobalTheory.UnivAction.univAct g γ).2.2 (s, 0) ⟨hs, Set.mem_univ _⟩).1
  exact ((Matrix.isUnit_iff_isUnit_det _).1 h).ne_zero

theorem actB_mem_siegel (γ : Sp g) {s : symMat g} (hs : s ∈ siegel g) : actB γ s ∈ siegel g :=
  ((GlobalTheory.UnivAction.univAct g γ).1.1 (show ((s, 0) : Pt (symMat g) g) ∈ cov (siegel g) g from
    ⟨hs, Set.mem_univ _⟩)).1

theorem continuous_act_fderiv {s : symMat g} (hs : s ∈ siegel g) (v : symMat g) :
    Continuous fun γ : Sp g => (actB γ s, fderiv ℂ (actB γ) s v) := by
  refine continuous_iff_continuousAt.2 fun γ => ?_
  have h₀ := det_denC_ne_zero γ hs
  have hcd : ContDiffAt ℂ ∞ (Function.uncurry actC) (ofSp γ, s) := contDiffAt_actC h₀
  have h1 : ContinuousAt (fun Γ : Par g => actC Γ s) (ofSp γ) :=
    hcd.continuousAt.comp (f := fun Γ : Par g => (Γ, s))
      (continuous_id.prodMk continuous_const).continuousAt
  have h2 : ContDiffAt ℂ 0 (fun Γ : Par g => fderiv ℂ (actC Γ) ((fun _ => s) Γ)) (ofSp γ) :=
    ContDiffAt.fderiv (f := actC) (g := fun _ => s)
      hcd contDiffAt_const (by simp)
  have h3 : ContinuousAt (fun Γ : Par g => fderiv ℂ (actC Γ) s v) (ofSp γ) :=
    h2.continuousAt.clm_apply continuousAt_const
  exact (h1.comp continuous_ofSp.continuousAt).prodMk (h3.comp continuous_ofSp.continuousAt)

end GlobalTheory.ThetaRR.RatDense

namespace GlobalTheory.ThetaRR

theorem isInvFun_of_rat : ∀ (g : ℕ) (F : symMat g → symMat g → Ext (1 + 1)), IsHermFun g F → (∀ γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g, (∀ i l, ∃ r : ℚ, γ.mat i l = r) → IsInvFun F γ) → ∀ γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g, IsInvFun F γ := by
  intro g F hF hrat γ s hs v
  have hΦ := RatDense.continuous_act_fderiv hs v
  have hmem : ∀ δ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g,
      (actB δ s, fderiv ℂ (actB δ) s v) ∈ siegel g ×ˢ (univ : Set (symMat g)) :=
    fun δ => ⟨RatDense.actB_mem_siegel δ hs, mem_univ _⟩
  have hc := hF.1.comp_continuous hΦ hmem
  have hcl : IsClosed {δ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g | F (actB δ s) (fderiv ℂ (actB δ) s v) = F s v} :=
    isClosed_eq hc continuous_const
  have hsub : {δ : Matrix.symplecticGroup (Fin g) ℝ |
      ∀ i j, ∃ q : ℚ, (δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) i j = q} ⊆
      {δ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g | F (actB δ s) (fderiv ℂ (actB δ) s v) = F s v} :=
    fun δ hδ => hrat δ hδ s hs v
  exact hcl.closure_subset_iff.2 hsub (GlobalTheory.dense_rat_symplecticGroup_fin g γ)

end GlobalTheory.ThetaRR

import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff
namespace GlobalTheory.ChernReg.JetSmooth

variable {E X F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

theorem contDiffOn_del_apply {f : X → F} {S : Set X} (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S)
    {W : Set E} {p g : E → X} (hp : ContDiffOn ℝ ∞ p W) (hg : ContDiffOn ℝ ∞ g W)
    (hpW : Set.MapsTo p W S) :
    ContDiffOn ℝ ∞ (fun q => del f (p q) (g q)) W := by
  simp only [del_apply]
  have hD : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y) S := hf.fderiv_of_isOpen hS (by simp)
  have hDp := hD.comp hp hpW
  have h1 := hDp.clm_apply hg
  have h2 := hDp.clm_apply (hg.const_smul Complex.I)
  exact (h1.sub (h2.const_smul Complex.I)).const_smul _

end GlobalTheory.ChernReg.JetSmooth

namespace GlobalTheory.ChernReg.JetSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}

theorem contDiffOn_det {A : E → Matrix (Fin d) (Fin d) ℂ} {S : Set E}
    (hA : ∀ k l, ContDiffOn ℝ ∞ (fun z => A z k l) S) :
    ContDiffOn ℝ ∞ (fun z => (A z).det) S := by
  simp only [Matrix.det_apply']
  refine ContDiffOn.sum fun σ _ => ?_
  exact contDiffOn_const.mul (contDiffOn_prod fun i _ => hA _ _)

theorem contDiffOn_inv_apply {A : E → Matrix (Fin d) (Fin d) ℂ} {S : Set E}
    (hA : ∀ k l, ContDiffOn ℝ ∞ (fun z => A z k l) S) (hdet : ∀ z ∈ S, IsUnit (A z).det) (k l : Fin d) :
    ContDiffOn ℝ ∞ (fun z => (A z)⁻¹ k l) S := by
  have hadj : ContDiffOn ℝ ∞ (fun z => (A z).adjugate k l) S := by
    simp only [Matrix.adjugate_apply]
    refine contDiffOn_det fun i j => ?_
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiffOn_const
    · exact hA _ _
  have hinv : ContDiffOn ℝ ∞ (fun z => ((A z).det)⁻¹) S :=
    (contDiffOn_det hA).inv fun z hz => (hdet z hz).ne_zero
  refine (hinv.mul hadj).congr fun z hz => ?_
  simp [Matrix.inv_def, Ring.inverse_eq_inv']

end GlobalTheory.ChernReg.JetSmooth

namespace GlobalTheory.ChernReg.JetSmooth

variable {d : ℕ}

theorem contDiffOn_coord (j : Fin d) :
    ContDiff ℝ ∞ (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => q.2 j) := by
  have : ContDiff ℝ ∞ (fun ξ : ReciprocityTheory.L2DbarEstimates.V d => ξ j) :=
    (EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ |>.contDiff
  exact this.comp contDiff_snd

theorem contDiffOn_chris {U : Set (ReciprocityTheory.L2DbarEstimates.V d)} {b : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin d) (Fin d) ℂ}
    (hU : IsOpen U) (hb : ∀ k l, ContDiffOn ℝ ∞ (fun v => b v k l) U) (hdet : ∀ v ∈ U, IsUnit (b v).det) :
    ContDiffOn ℝ ∞ (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => christoffel b q.1 q.2) (U ×ˢ Set.univ) := by
  refine contDiffOn_piLp' 2 fun i => ?_
  simp only [christoffel, Matrix.vecMul, dotProduct]
  refine ContDiffOn.sum fun k _ => ?_
  refine (ContDiffOn.sum fun j _ => ((contDiffOn_coord j).contDiffOn).mul ?_).mul ?_
  · simp only [Matrix.of_apply]
    exact contDiffOn_del_apply hU (hb j k) contDiffOn_fst contDiffOn_snd (fun q hq => hq.1)
  · exact (contDiffOn_inv_apply hb hdet k i).comp contDiffOn_fst (fun q hq => hq.1)

end GlobalTheory.ChernReg.JetSmooth

namespace GlobalTheory.ChernReg.JetSmooth

variable {d : ℕ}

theorem contDiffOn_jet {U : Set (ReciprocityTheory.L2DbarEstimates.V d)} {b : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin d) (Fin d) ℂ}
    (hU : IsOpen U) (hb : ∀ k l, ContDiffOn ℝ ∞ (fun v => b v k l) U) (hdet : ∀ v ∈ U, IsUnit (b v).det)
    (n : ℕ) : ContDiffOn ℝ ∞ (jet b n) (U ×ˢ Set.univ) := by
  induction n with
  | zero => rw [jet_zero]; exact contDiffOn_fst
  | succ n ih =>
    have h : jet b (n + 1) = fun q => del (jet b n) (id q) (q.2, -christoffel b q.1 q.2) := by
      funext q; exact jet_succ b n q
    rw [h]
    exact contDiffOn_del_apply (hU.prod isOpen_univ) ih contDiffOn_id
      (contDiffOn_snd.prodMk (contDiffOn_chris hU hb hdet).neg) (fun q hq => hq)

theorem chris_smul (b : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin d) (Fin d) ℂ) (z ξ : ReciprocityTheory.L2DbarEstimates.V d) (t : ℂ) :
    christoffel b z (t • ξ) = t ^ 2 • christoffel b z ξ := by
  simp only [christoffel]
  have hM : (Matrix.of fun k l => del (fun v => b v k l) z (t • ξ)) =
      t • Matrix.of fun k l => del (fun v => b v k l) z ξ := by
    ext k l; simp
  simp only [hM, WithLp.ofLp_smul, Matrix.vecMul_smul, Matrix.smul_vecMul, smul_smul, WithLp.toLp_smul, pow_two]

end GlobalTheory.ChernReg.JetSmooth

namespace GlobalTheory.ChernReg.JetSmooth

variable {d : ℕ}

theorem del_scale {U : Set (ReciprocityTheory.L2DbarEstimates.V d)} {f : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ)) (t : ℂ) (n : ℕ)
    (hom : ∀ z ∈ U, ∀ ξ, f (z, t • ξ) = t ^ n • f (z, ξ)) {z : ReciprocityTheory.L2DbarEstimates.V d} (hz : z ∈ U)
    (ξ a v : ReciprocityTheory.L2DbarEstimates.V d) :
    del f (z, t • ξ) (a, t • v) = t ^ n • del f (z, ξ) (a, v) := by
  let L : (ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d) →L[ℂ] (ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d) :=
    (ContinuousLinearMap.fst ℂ (ReciprocityTheory.L2DbarEstimates.V d) (ReciprocityTheory.L2DbarEstimates.V d)).prod
      (t • ContinuousLinearMap.snd ℂ (ReciprocityTheory.L2DbarEstimates.V d) (ReciprocityTheory.L2DbarEstimates.V d))
  let Lr : (ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d) →L[ℝ] (ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d) :=
    L.restrictScalars ℝ
  have hL : ∀ q, Lr q = (q.1, t • q.2) := fun q => rfl
  have hW : IsOpen (U ×ˢ (Set.univ : Set (ReciprocityTheory.L2DbarEstimates.V d))) := hU.prod isOpen_univ
  have hdiff : ∀ q ∈ U ×ˢ (Set.univ : Set (ReciprocityTheory.L2DbarEstimates.V d)), DifferentiableAt ℝ f q := fun q hq =>
    (hf.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hq)
  have hq0 : ((z, ξ) : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d) ∈ U ×ˢ Set.univ := ⟨hz, trivial⟩
  have hLq0 : Lr (z, ξ) ∈ U ×ˢ (Set.univ : Set (ReciprocityTheory.L2DbarEstimates.V d)) := ⟨hz, trivial⟩
  have heq : (f ∘ Lr) =ᶠ[𝓝 (z, ξ)] fun q => t ^ n • f q := by
    filter_upwards [hW.mem_nhds hq0] with q hq
    simpa [hL] using hom q.1 hq.1 q.2
  have hD : ∀ w, fderiv ℝ f (Lr (z, ξ)) (Lr w) = t ^ n • fderiv ℝ f (z, ξ) w := by
    intro w
    have h1 : fderiv ℝ (f ∘ Lr) (z, ξ) = (fderiv ℝ f (Lr (z, ξ))).comp Lr := by
      rw [fderiv_comp (z, ξ) (hdiff _ hLq0) Lr.differentiableAt, Lr.fderiv]
    have h2 := heq.fderiv_eq (𝕜 := ℝ)
    have hs : HasFDerivAt (fun q => t ^ n • f q) (t ^ n • fderiv ℝ f (z, ξ)) (z, ξ) :=
      (hdiff _ hq0).hasFDerivAt.const_smul (t ^ n)
    rw [hs.fderiv] at h2
    have h3 := congrArg (fun T => T w) (h1.symm.trans h2)
    simpa using h3
  have e0 : ((z, t • ξ) : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d) = Lr (z, ξ) := rfl
  have e1 : ((a, t • v) : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d) = Lr (a, v) := rfl
  have e2 : Complex.I • Lr (a, v) = Lr (Complex.I • (a, v)) := (L.map_smul _ _).symm
  rw [del_apply, del_apply, e0, e1, e2, hD, hD, smul_comm Complex.I (t ^ n), ← smul_sub,
    smul_comm _ (t ^ n)]

end GlobalTheory.ChernReg.JetSmooth

namespace GlobalTheory.ChernReg.JetSmooth

variable {d : ℕ}

theorem jet_smul {U : Set (ReciprocityTheory.L2DbarEstimates.V d)} {b : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin d) (Fin d) ℂ}
    (hU : IsOpen U) (hb : ∀ k l, ContDiffOn ℝ ∞ (fun v => b v k l) U) (hdet : ∀ v ∈ U, IsUnit (b v).det)
    (n : ℕ) : ∀ z ∈ U, ∀ (t : ℂ) ξ, jet b n (z, t • ξ) = t ^ n • jet b n (z, ξ) := by
  induction n with
  | zero => intro z _ t ξ; simp [jet_zero]
  | succ n ih =>
    intro z hz t ξ
    rw [jet_succ, jet_succ]
    dsimp only
    rw [chris_smul]
    have e1 : ((t • ξ, -(t ^ 2 • christoffel b z ξ)) : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d) =
        (t • ξ, t • -(t • christoffel b z ξ)) := by
      rw [pow_two, ← smul_smul, smul_neg]
    rw [e1, del_scale hU (contDiffOn_jet hU hb hdet n) t n (fun z hz ξ => ih z hz t ξ) hz]
    have e2 : ((t • ξ, -(t • christoffel b z ξ)) : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d) =
        t • (ξ, -christoffel b z ξ) := by
      rw [Prod.smul_mk, smul_neg]
    rw [e2, map_smul, smul_smul, pow_succ]

end GlobalTheory.ChernReg.JetSmooth

theorem GlobalTheory.ChernReg.jet_contDiffOn_and_homogeneous : ∀ (d : ℕ) (U : Set (ReciprocityTheory.L2DbarEstimates.V d)) (b : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin d) (Fin d) ℂ), IsOpen U → (∀ k l, ContDiffOn ℝ ∞ (fun v => b v k l) U) → (∀ v ∈ U, IsUnit (b v).det) → ∀ n, ContDiffOn ℝ ∞ (jet b n) (U ×ˢ Set.univ) ∧ ∀ z ∈ U, ∀ (t : ℂ) ξ, jet b n (z, t • ξ) = t ^ n • jet b n (z, ξ) := by
  intro d U b hU hb hdet n
  exact ⟨JetSmooth.contDiffOn_jet hU hb hdet n, JetSmooth.jet_smul hU hb hdet n⟩

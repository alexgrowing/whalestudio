import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFramesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricPullbackGramAndInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameDomainCoordinatesHolomorphicStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

namespace GlobalTheory.MetSmooth

section Entries

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : Type*} [Fintype n] [DecidableEq n] {B : Set V}
  {M : V → Matrix n n ℂ}

theorem contDiffOn_det (h : ∀ a b, ContDiffOn ℝ ∞ (fun v => M v a b) B) : ContDiffOn ℝ ∞ (fun v => (M v).det) B := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem contDiffOn_inv_apply (h : ∀ a b, ContDiffOn ℝ ∞ (fun v => M v a b) B) (hd : ∀ v ∈ B, IsUnit (M v).det) (a b : n) :
    ContDiffOn ℝ ∞ (fun v => (M v)⁻¹ a b) B := by
  have e : ∀ v, (M v)⁻¹ a b = ((M v).det)⁻¹ * (M v).adjugate a b := fun v => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rfl
  simp only [e, Matrix.adjugate_apply]
  refine ContDiffOn.mul ((contDiffOn_det h).inv fun v hv => (hd v hv).ne_zero) (contDiffOn_det fun c d => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact h _ _

end Entries

end GlobalTheory.MetSmooth

open GlobalTheory.MetSmooth in

theorem GlobalTheory.MetSmooth.metsmooth : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (x : ToroidalCompactificationData s) (t : D.what₂.Tau), (∀ a b, HodgeDomain.SmoothOn fun z : Pt D.what₂.Tau j (N - j) => x.metW L k z t a b) ∧ ∀ a b, HodgeDomain.SmoothOn fun z : Pt D.what₂.Tau j (N - j) => x.metOm L k z t a b := by
  intro D A N j S κ s L k x t
  obtain ⟨f, hf, hd⟩ := GlobalTheory.T.frame_domain_coordinates_holomorphic D A N j S κ s L k
  have laws := (GlobalTheory.T.metric_pullback_gram_and_invariance D A N j S κ s L k x).1
  have hW : ∀ z ∈ DomI D.what₂.Tau j (N - j), x.metW L k z t = x.gramW L k (f z) t := fun z hz => by
    have h := (laws (f z) t).1
    rw [(hf z hz).1, ((hf z hz).2 _).1] at h
    simpa using h
  have hO : ∀ z ∈ DomI D.what₂.Tau j (N - j), x.metOm L k z t = x.gramOm L k (f z) t := fun z hz => by
    have h := (laws (f z) t).2
    rw [(hf z hz).1, ((hf z hz).2 _).2] at h
    simpa using h

  let e := Fintype.equivFin (D.what₂.Tau × Fin j × Fin (N - j))
  let R : (Fin (Fintype.card (D.what₂.Tau × Fin j × Fin (N - j))) → ℂ) ≃L[ℂ] (D.what₂.Tau × Fin j × Fin (N - j) → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ => ℂ) e.symm
  have hB : IsOpen (R ⁻¹' DomFlat D.what₂.Tau j (N - j)) := ActionDeriv.isOpen_domFlat.preimage R.continuous
  have hg := GlobalTheory.T.gram_smooth_of_holomorphic_frames D A N j S κ s L k x _ (R ⁻¹' DomFlat D.what₂.Tau j (N - j)) (fun w => f (unflat (R w))) hB
    fun τ a b => (hd τ a b).comp R.differentiable.differentiableOn fun _ h => h
  have key : ∀ τ a b, ContDiffOn ℝ ∞
      (fun v => x.gram (s.framePt k (f (unflat v))) (s.lieFrame k (f (unflat v))) τ a b)
      (DomFlat D.what₂.Tau j (N - j)) := fun τ a b => by
    have h := (hg τ a b).comp (R.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffOn
      (s := DomFlat D.what₂.Tau j (N - j)) fun v hv => by
        show R (R.symm v) ∈ DomFlat D.what₂.Tau j (N - j)
        rwa [R.apply_symm_apply]
    refine h.congr fun v _ => ?_
    show _ = x.gram (s.framePt k (f (unflat (R (R.symm v))))) (s.lieFrame k (f (unflat (R (R.symm v))))) τ a b
    rw [R.apply_symm_apply]
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · refine (key (L.ψ t).1 (Fin.cast (S.mult_psi L t).symm a) (Fin.cast (S.mult_psi L t).symm b)).congr fun v hv => ?_
    show x.metW L k (unflat v) t a b = _
    rw [hW _ hv]
    rfl
  · have hinv := contDiffOn_inv_apply (key (conjEmb (L.ψ t).1)) fun v _ =>
      (Matrix.isUnit_iff_isUnit_det _).1 (x.gram_posDef _ _).isUnit
    refine ((contDiffOn_const (c := (hodgeC (s.fd k) (s.lab L k) t : ℂ) ^ 2)).mul
      (hinv (Fin.cast (S.mult_conj L t).symm b.rev) (Fin.cast (S.mult_conj L t).symm a.rev))).congr fun v hv => ?_
    show x.metOm L k (unflat v) t a b = _
    rw [hO _ hv]
    rfl

import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameDomainCoordinatesHolomorphic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryArcLiftNotConvergesSymmetricDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam

theorem isHol_toCpt : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (U : (gen s.T.Z).Opens) (f : Γ(gen s.T.Z, U)), IsOpen {v ∈ DomFlat D.what₂.Tau j (N - j) | s.toCpt L k (unflat v) ∈ ptsIn (genStr s.T.Z) κ.σ₀ U} ∧ DifferentiableOn ℂ (fun v => ev (genStr s.T.Z) κ.σ₀ U f (s.toCpt L k (unflat v))) {v ∈ DomFlat D.what₂.Tau j (N - j) | s.toCpt L k (unflat v) ∈ ptsIn (genStr s.T.Z) κ.σ₀ U} := by
  intro D A N j S κ s L k U f
  classical
  obtain ⟨F, hF1, hF2⟩ := exists_holo_frame D A N j S κ s L k
  let sf : ReciprocityTheory.ChartRestriction.G.FD.Frame (s.fd k).Ψ N → (s.fd k).dom := fun x =>
    if h : x ∈ (s.fd k).dom then ⟨x, h⟩ else F 0
  have hsf : ∀ x (h : x ∈ (s.fd k).dom), sf x = ⟨x, h⟩ := fun x h => dif_pos h
  have hU : Formalism.L2.Pj.IsUnf (s.U κ.σ₀).toPj := (Formalism.L2.PjFree.isUnf_ofPj (s.U κ.σ₀).toPj).1 s.isUnf
  have h1 := BdArc.Leave.isHolTo_ptC (U := (s.U κ.σ₀).toPj) hU k sf fun x h => by rw [hsf x h]
  have h2 := LocLift.isHolTo_comp_hom h1 s.T.Z.jQ
  have ho : IsOpen (DomFlat D.what₂.Tau j (N - j)) := ActionDeriv.isOpen_domFlat
  have hβ : DifferentiableOn ℂ (fun v => (F (unflat v)).1) (DomFlat D.what₂.Tau j (N - j)) :=
    differentiableOn_pi.2 fun τ => differentiableOn_pi.2 fun a => differentiableOn_pi.2 fun b => hF2 τ a b
  have h3 := LocLift.isHolTo_comp h2 ho hβ fun v _ => (F (unflat v)).2
  have h4 : IsHolTo (DomFlat D.what₂.Tau j (N - j)) fun v => (s.toCpt L k (unflat v)).1 := by
    refine LocLift.isHolTo_congr h3 fun v hv => ?_
    have e : s.toCpt L k (unflat v) = s.framePt k (F (unflat v)) := by
      conv_lhs => rw [← (hF1 _ hv).1]
      exact s.toCpt_zOf L k _
    rw [e, hsf _ (F (unflat v)).2]
    rfl
  exact h4 U f

end GlobalTheory.ShFam

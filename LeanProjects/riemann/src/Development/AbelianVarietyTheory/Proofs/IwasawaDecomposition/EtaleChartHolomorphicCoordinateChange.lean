import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh

theorem valAt'_eq_ev {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {U : Y.Opens}
    {x : CxPts p σ} (h : x ∈ CxPts.ptsIn p σ U) (f : Γ(Y, U)) : valAt' x.1 U f = CxPts.ev p σ U f x := by
  rw [CxPts.ev_eq h, CxPts.evHom_eq_evalPt h, TangentOrigin.valAt'_eq_evalPt _ _ h]

theorem chart_change : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ) (c : AlgChart p σ n) (ψ : OpenPartialHomeomorph (ReciprocityTheory.L2DbarEstimates.V n) (Fin n → ℂ)), DifferentiableOn ℂ ψ ψ.source → DifferentiableOn ℂ ψ.symm ψ.target → (∀ j, HolAlong (c.e.trans ψ).source fun x => (c.e.trans ψ) x j) ∧ IsHolTo (c.e.trans ψ).target (fun z => ((c.e.trans ψ).symm z).1) := by
  intro k _ Y p n σ c ψ hψ hψs
  refine ⟨fun j V _ _ _ B x hB hx hm => ?_, fun U' f => ⟨?_, ?_⟩⟩
  · have hs : ∀ b ∈ B, x b ∈ c.e.source ∧ c.e (x b) ∈ ψ.source := fun b hb => by
      simpa [OpenPartialHomeomorph.trans_source] using hm hb
    have hco : ∀ a, DifferentiableOn ℂ (fun b => c.e (x b) a) B := fun a => by
      refine ((hx c.U (c.x a)).2.mono fun b hb => ⟨hb, c.source_subset (hs b hb).1⟩).congr fun b hb => ?_
      rw [c.apply_eq _ (hs b hb).1, valAt'_eq_ev (c.source_subset (hs b hb).1)]
    have hce : DifferentiableOn ℂ (fun b => c.e (x b)) B := differentiableOn_euclidean.2 hco
    have h2 : DifferentiableOn ℂ (fun b => ψ (c.e (x b))) B := hψ.comp hce fun b hb => (hs b hb).2
    exact differentiableOn_pi.1 h2 j
  · exact (c.e.trans ψ).continuousOn_symm.isOpen_inter_preimage (c.e.trans ψ).open_target
      (CxPts.isOpen_ptsIn U')
  · have hm : ∀ z ∈ {z ∈ (c.e.trans ψ).target | ⊤ ≤ ((c.e.trans ψ).symm z).1 ⁻¹ᵁ U'},
        z ∈ ψ.target ∧ ψ.symm z ∈ c.e.target ∧ c.e.symm (ψ.symm z) ∈ CxPts.ptsIn p σ U' := fun z hz => by
      have h1 := hz.1
      simp only [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at h1
      exact ⟨h1.1, h1.2, hz.2⟩
    have h2 : DifferentiableOn ℂ (CxPts.ev p σ U' f ∘ c.e.symm ∘ ψ.symm)
        {z ∈ (c.e.trans ψ).target | ⊤ ≤ ((c.e.trans ψ).symm z).1 ⁻¹ᵁ U'} :=
      (c.holo U' f).comp (hψs.mono fun z hz => (hm z hz).1) fun z hz => ⟨(hm z hz).2.1, (hm z hz).2.2⟩
    refine h2.congr fun z hz => ?_
    exact valAt'_eq_ev (hm z hz).2.2 f

end GlobalTheory.ShFam.Hor.LogCh

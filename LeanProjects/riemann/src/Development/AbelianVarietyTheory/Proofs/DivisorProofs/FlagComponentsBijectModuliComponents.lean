import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageConnectedComponentMem
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CovHt.Link

theorem exists_equiv_over : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag), ∃ q : s.Comp ≃ Comp s.Xo κ.c, ∀ k, Over Φ k (q k) := by
  intro D A N j S κ s Φ
  obtain ⟨q, hq⟩ := GlobalTheory.ShFam.PtComp.exists_equiv s
  refine ⟨q, fun k => ?_⟩
  letI := (constF κ.e (Φ.C k).Y).toAlgebra
  intro t
  have hx : (GlobalTheory.AllWt.ptF (Φ.C k).y0 ≫ s.T.Z.jQ) t = (Φ.C k).π (genericPt (Φ.C k).Y t) := by
    rw [(Φ.C k).y0_x]; rfl
  have hon : OnComp s k ((Φ.C k).π (genericPt (Φ.C k).Y t)) := by
    obtain ⟨z, hz⟩ : ((s.U κ.σ₀).X k).dom.Nonempty := GlobalTheory.OrbitScalar.exists_mem_dom _
    refine ⟨⟨z, hz⟩, fun pt => ?_⟩
    exact (isPreconnected_range (Φ.C k).π.continuous).subset_connectedComponent ⟨_, rfl⟩
      (Φ.label k ⟨z, hz⟩ pt)
  have e := (hq k _).1 hon
  show GlobalTheory.AllWt.ptF (Φ.C k).y0 t ∈ ((q k : _) : Set _)
  rw [e]
  rw [Set.mem_preimage]
  have : s.T.Z.jQ (GlobalTheory.AllWt.ptF (Φ.C k).y0 t) = (GlobalTheory.AllWt.ptF (Φ.C k).y0 ≫ s.T.Z.jQ) t := rfl
  rw [this, hx]
  exact mem_connectedComponent

end GlobalTheory.CovHt.Link

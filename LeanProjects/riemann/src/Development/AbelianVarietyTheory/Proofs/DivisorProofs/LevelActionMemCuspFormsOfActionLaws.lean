import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LevelCusp.actLev_mem_cuspA_of_actLev : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → ∀ g, (∀ a, (lev g).2 a = a) → ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, actLev T.Q.c lev g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := by
  intro D G _ T κ i lev hJ hL g _ f hf
  have h := hJ.toLawsM
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, by have := i.2; omega⟩
  have hp := h.pins
  have hpq : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    rw [(hp.2.2.2 _ hj).1, (hp.2.2.2 _ hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  obtain ⟨hs, hc⟩ := (mem_cusp _ _ _ _ _ _).1 hf
  have hg : actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev g f ∈
      sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA (κ i)) (κ i).n :=
    actL_mem _ _ _ _ hL.total hL.nat hL.bor _ g hs
  refine (mem_cusp _ _ _ _ _ _).2 ⟨hg, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩
  have hU := h.unf _ hj σ hσ
  refine GlobalTheory.LevelCusp.rdU_mem_SS (U := Formalism.L2.PjFree.Unf.ofPj (T.U ((i : ℕ) + 1) σ)) hσ hU (hU.1 ▸ hpq)
    (fun k k' τ => (h.xiAbs _ hj σ hσ k τ).trans (h.xiAbs _ hj σ hσ k' τ).symm) (dom_wtA (κ i)) hs hg
    (fun k => GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ (hc σ hσ) k) (fun y => ?_) k
  obtain ⟨ρ, ν, -, -, hm⟩ := mvPt_spec hL.total g y
  exact ⟨ρ, ν, _, hm, evalAt_actL hL (h.evalWD _ hj) frMap_trans_id g hs.1 y⟩

import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspFormsStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Onto

set_option maxHeartbeats 1000000 in

theorem holSub0_eq_span_readings : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → KapIs κ → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c σ → Formalism.L2.Pj.holSub0 (T.U ((i : ℕ) + 1) σ).X (laU (T.U ((i : ℕ) + 1) σ) (wtA (κ i)) (κ i).n) = Submodule.span ℂ (Set.range fun f : Cu T κ i => rdU (T.U ((i : ℕ) + 1) σ) (f : T.R ((i : ℕ) + 1))) := by
  intro D T κ h hκ hl hn i σ hσ
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; positivity)
  have hni : (κ i).n = D.R.nV := (hκ i τ).2.2
  apply le_antisymm
  · refine (GlobalTheory.T.holomorphicCuspSections_le_span_algebraicCuspForms D T h _ (inR i) (κ i) (hl i) (hni ▸ hn) σ hσ).trans (Submodule.span_mono ?_)
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    exact Submodule.mem_inf.2 ⟨((Formalism.L2.Pj.mem_cusp _ _ _ _ _ _).1 f.2).2 σ hσ, Formalism.L2.Pj.rdU_mem_offZero _ _⟩

end GlobalTheory.Onto

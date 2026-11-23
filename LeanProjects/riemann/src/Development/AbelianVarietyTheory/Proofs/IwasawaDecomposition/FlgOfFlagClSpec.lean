import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllStepsHoldOfHasDRStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfAllStepsHoldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagClosureStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.LocM

theorem flgOf_flagCl_spec : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p) (P : ∀ B : ct.Mdl, Lat B → Prop) (Z : ct.Mdl) (s : (flgOf ct P).FlagData Z), IsFlagCl Z s.1 ((flgOf ct P).flagCl Z s) := by
  intro D A N j S κ p ct P Z s
  have hid : ∀ Z : ct.Mdl, ∃ f, IsMap Z Z f := fun Z =>
    ⟨𝟙 _, MapComp.corr_refl Z, fun k _ w hw => by simpa using GlobalTheory.ProjBlowup.natImg_refl Z w hw⟩
  refine ct.isFlagCl_flagCl Z s.1 (hid Z) (fun h => ?_) (GlobalTheory.T.exists_flag_closure _ _ _ _ _ _ ct.hp ct.hW _ _ Z _ fun t ht => ?_)
  · obtain ⟨f, hf⟩ := h.2.2.1
    have hty (σ) : Z.ty σ ∪ stepTy (allSteps (Lat.top Z)) σ = Finset.range (S.Dw.mult σ + 1) := by
      rw [stepTy_allSteps, Finset.union_eq_right, ← h.2.1.1 σ]
      exact hf.1.2.2 σ
    refine ⟨h.1, fun σ => (h.2.1.1 σ).trans (hty σ).symm, ⟨f, hf⟩,
      GlobalTheory.T.allSteps_hold_of_hasDR _ _ _ _ _ _ ct.hp ct.hW _ _ Z _ h.2.1 ⟨f, hf⟩, fun Z'' hg hs => ?_⟩
    obtain ⟨Z₀, h₀⟩ := GlobalTheory.T.exists_flag_closure _ _ _ _ _ _ ct.hp ct.hW _ _ Z (allSteps (Lat.top Z)) fun t ht => by
      obtain ⟨σ, r, hr, rfl⟩ := mem_allSteps.1 ht
      exact hid Z
    obtain ⟨a, ha⟩ := h₀.2.2.2.2 Z'' hg hs
    obtain ⟨b, hb⟩ := h.2.2.2 Z₀ (GlobalTheory.T.hasDR_of_allSteps_hold _ _ _ _ _ _ ct.hp ct.hW _ _ Z Z₀ (fun σ => (h₀.2.1 σ).trans (hty σ)) h₀.2.2.2.1) h₀.2.2.1
    exact ⟨a ≫ b, MapComp.isMap_comp ha hb⟩
  · rcases (s.2 t ht).1 with h | h
    · exact h ▸ hid t.B
    · exact h

end GlobalTheory.LocM

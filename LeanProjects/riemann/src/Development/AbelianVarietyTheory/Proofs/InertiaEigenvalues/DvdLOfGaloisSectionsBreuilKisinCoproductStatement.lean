import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdLOfGaloisSectionsBreuilKisinCoproduct
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_l_of_galoisSections_breuilKisinCoproduct : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (κ : Type) [Fintype κ] (x : κ → En.Q.A) (c : κ → κ → En.Q.A) (h : ℕ), (∀ j, BK.hf En.inl bk.E ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι → σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ∣ σ.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ∣ x j := by
  first | exact @GlobalTheory.BSP.dvd_l_of_sections_env_bk | exact GlobalTheory.BSP.dvd_l_of_sections_env_bk | (intros; apply GlobalTheory.BSP.dvd_l_of_sections_env_bk <;> assumption)

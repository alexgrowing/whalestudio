import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniqueIsContr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Rigid

theorem isSpherical_locProd {E : Type} [Field E] [NumberField E] {c n : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n)
    (w : HeightOneSpectrum (𝓞 E)) (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
    (hs : ∀ i, GlobalTheory.LGrp.IsSpherical (σ i).ρ (GlobalTheory.LFun.KGL w (N i))) :
    GlobalTheory.LGrp.IsSpherical (GlobalTheory.UnitaryBC.locProd h w σ) (GlobalTheory.LFun.KGL w n) := by
  have hKO : ∀ m, GlobalTheory.LFun.KGL w m = KO (w.adicCompletion E) (Fin m) := fun m =>
    (GlobalTheory.SmGL.SphCompletion.KO_completion w m).symm
  choose v hv hv0 using fun i => (Submodule.ne_bot_iff _).1 (hs i)
  obtain ⟨f, hf, hf1⟩ := GlobalTheory.SatInd.exists_fixed_apply_one (k := w.adicCompletion E) (stdBlocks N h)
    (ρ := piTensor fun i => (σ i).ρ) (x := PiTensorProduct.tprod ℂ v) (fun g hg => by
      rw [piTensor_tprod]
      congr 1
      funext i
      exact GlobalTheory.LGrp.mem_fixed.1 (hv i) (g i) (by rw [hKO]; exact hg i))
  refine (Submodule.ne_bot_iff _).2 ⟨f, by rw [hKO]; exact hf, fun h0 => GlobalTheory.ContrObj.tprod_ne_zero v hv0 ?_⟩
  rw [← hf1, h0]
  rfl

end GlobalTheory.Rigid

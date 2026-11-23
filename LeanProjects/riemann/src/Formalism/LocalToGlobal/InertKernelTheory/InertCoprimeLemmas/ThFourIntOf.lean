import Formalism.LocalToGlobal.InertKernelTheory.DefsMM

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem thFourInt_of (hA : OneCopyLoc) (hB : LocInv) (hC : FourProd) (hD : GlobONB) (hE : AlgZero) : ThFourInt := by
  intro D cc δ B hcc hδ p _ hp hin lam s hs
  obtain ⟨σ, r, v, hσ, hv, hint⟩ := hA D cc δ B hcc hδ p hp hin lam
  obtain ⟨r₄, v₄, hv₄, hint₄⟩ := hC D cc δ B hcc hδ p hp hin lam σ r v hσ hv
    (fun s1 hs1 => ⟨hE D cc δ B hcc hδ p hp hin 1 1 s1 hs1, hint s1 hs1⟩)
  obtain ⟨rb, b, hb, hon, hloc⟩ := hD D p hp hin lam
  refine ⟨rb, b, hb, hon, ?_⟩
  intro C wq hC hwq
  exact hB D cc δ hcc hδ p hp hin lam σ hσ 2 2 _ r₄ rb v₄ _ _ hv₄ (hloc σ hσ) (hint₄ s hs) C wq hC hwq

end Formalism.L2.KerInert

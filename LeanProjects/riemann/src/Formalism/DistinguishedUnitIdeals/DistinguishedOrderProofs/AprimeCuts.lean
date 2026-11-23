import Mathlib
import Formalism.DistinguishedUnitIdeals.AprimeCuts
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.CutPlace
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.AprimeArith

namespace Formalism.ExponentWindows

theorem exists_cuts_exponent_bounds : AprimeCuts := by
  obtain ⟨C, hC, hA⟩ := Formalism.TruncatedSeriesCounting.WachCoordinates.exists_constant_exponent_inequalities
  refine ⟨C, hC, ?_⟩
  intro ℓ hℓ n j _ size b w S η rr hj hjn _hsize hCb hsep hrr

  obtain ⟨cuts, ell, hne, hcuts⟩ :=
    exists_cuts_of_sparse_thick n j (fun a => b ≤ size a ∧ size a ≤ b + η) hj hjn hsep
  refine ⟨cuts, ell, hne, fun c hc => ?_⟩
  obtain ⟨h1, h2, h3, _h4, h5, h6, _h7, h8, _h9⟩ := hcuts c hc
  refine ⟨h1, h2, h3, h5, h6, h8, ?_, ?_⟩
  · intro k _ hk
    exact (hA ℓ hℓ b w S η j (3 * j + 1) _ _ rr hj hCb le_rfl hk.1 hk.2 hk.1 hk.2 hrr).1
  · intro k k' _ _ hk hk'
    obtain ⟨_, _, e1, e2, e3⟩ :=
      hA ℓ hℓ b w S η j (3 * j + 1) _ _ rr hj hCb le_rfl hk'.1 hk'.2 hk.1 hk.2 hrr
    exact ⟨e1, e2, e3⟩

end Formalism.ExponentWindows

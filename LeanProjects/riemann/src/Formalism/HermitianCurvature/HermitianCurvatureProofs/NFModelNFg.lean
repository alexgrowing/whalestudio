import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomCore

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

def NFModelNFg : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ (l0 : ℕ) (Y : Finset ℝ) (w : List C.Letter), TBB.AdmW P l0 Y w → ∀ e : Wd.Ix (Fin w.length),
      ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (i i' : Fin m → ℕ) (h : Fin m → List (MA.A P (MA.DQ P))),
        (∀ j, b j ∈ Submonoid.closure (MA.bddSet P L)) ∧ (∀ j, i j + i' j = w.length) ∧
        (∀ j, (h j).length = w.length ∧ ∀ a ∈ h j, a ∈ MA.hatSet P L) ∧
        ∑ e' : Wd.Ix (Fin w.length),
            (Fr.ofWord L (MA.startM P (MA.DQ P) l0) (D.positionted w)).F e e' *
              Wd.uw (MA.sites P (MA.DQ P)) (D.positionted w) e' =
          ∑ j, b j * L.Di ^ i j * L.Dbi ^ i' j * (h j).prod

end

end Formalism.FourierDecayAlt.P.CutBP

import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm

noncomputable section

namespace GlobalTheory.OnePlace

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem GlobalTheory.TwU

def xiE {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]) :
    Eidx n' r0 r1 ⊕ Eidx n' r0 r1 → MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]
  | Sum.inl (r, a, b) => MvPowerSeries.subst (fun s : ZMod n' =>
      (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) (x (Sum.inl r))
  | Sum.inr (r, a, b) => MvPowerSeries.subst (fun s : ZMod n' =>
      (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) (x (Sum.inr r))

def jetZ (p : ℕ) [Fact p.Prime] (n' r0 r1 : ℕ) (z : Zidx n' r0 r1) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p] :=
  jetLogG p n' (((z.1 : ℕ) : ZMod n'), z.2)

end GlobalTheory.OnePlace

end

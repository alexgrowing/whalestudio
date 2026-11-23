import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit

noncomputable section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrCoord

theorem frFac_mul_c {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (VS D) D.R.rS T}
    {F0' : LFlag (VS D) D.R.rS T'} {FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS}
    {G : GFrames (placesOf Z) D.R.rS D.R.k} (c : GCoord Z F0 F0' FP G) (p : PlF D) (b : Fin (D.R.rS + 1)) :
    (show ((placesOf Z).loc p).Ep from frFac Z.δ p b) * algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) = 1 := by
  have hu : IsUnit (algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ)))) :=
    ((G.c p).isUnit.pow _).map _
  have he : (show ((placesOf Z).loc p).Ep from frFac Z.δ p b) =
      Ring.inverse (algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ)))) := by
    rw [map_pow]
    exact congrArg (fun x => Ring.inverse (x ^ (D.R.rS - (b : ℕ)))) (c.c_eq p).symm
  rw [he]
  exact Ring.inverse_mul_cancel _ hu

theorem step {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (VS D) D.R.rS T}
    {F0' : LFlag (VS D) D.R.rS T'} {FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS}
    {G : GFrames (placesOf Z) D.R.rS D.R.k} (c : GCoord Z F0 F0' FP G) (p : PlF D) (N : G.GLV) (m : (G.S p).GLV)
    (hm : (placesOf Z).Ext p N m) (B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (v : Fin (D.R.rS + 1) → (VS D).V) (g : Fin (D.R.rS + 1) → G.V) (gl : Fin (D.R.rS + 1) → (G.S p).V)
    (hg : ∀ a, g a = c.e (v a))
    (hgl : ∀ a : Fin (D.R.rS + 1), algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (a : ℕ))) • gl a =
      (placesOf Z).bc p (g a))
    (hN : ∀ b, N (g b) = ∑ a, B a b • g a) (b : Fin (D.R.rS + 1)) :
    (c.c p).e (scaled Z p (fun b => ∑ a, B a b • v a) b) = m (gl b) := by
  have h1 : c.e (∑ a, B a b • v a) = N (g b) := by
    rw [hN b, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, hg a]
  have h2 : (c.c p).e (scaled Z p (fun b => ∑ a, B a b • v a) b) =
      frFac Z.δ p b • (c.c p).e (baseChange₂ D p (∑ a, B a b • v a)) := (c.c p).e.map_smul _ _
  have h3 : m ((placesOf Z).bc p (g b)) = (placesOf Z).bc p (N (g b)) := hm (g b)
  have h4 : m (algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) • gl b) =
      algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) • m (gl b) := m.map_smul _ _
  have h5 : (c.c p).e (baseChange₂ D p (∑ a, B a b • v a)) =
      algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) • m (gl b) :=
    (c.compat p _).trans ((congrArg ((placesOf Z).bc p) h1).trans
      (h3.symm.trans ((congrArg m (hgl b).symm).trans h4)))
  have h6 : (show ((placesOf Z).loc p).Ep from frFac Z.δ p b) •
      algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) • m (gl b) =
      m (gl b) := by
    rw [smul_smul, frFac_mul_c c p b, one_smul]
  rw [h2, h5]
  exact h6

theorem scaled_coord : ∀ (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T') (FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (p : PlF D) (N : G.GLV) (m : (G.S p).GLV), (placesOf Z).Ext p N m → ∀ B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, ((∀ b, N (G.f b) = ∑ a, B a b • G.f a) → ∀ b, (c.c p).e (scaled Z p (fun b => ∑ a, B a b • frame F0 a) b) = m ((G.S p).f b)) ∧ ((∀ b, N (G.f' b) = ∑ a, B a b • G.f' a) → ∀ b, (c.c p).e (scaled Z p (fun b => ∑ a, B a b • frame F0' a) b) = m ((G.S p).f' b)) := by
  intro D Z T T' F0 F0' FP G c p N m hm B
  exact ⟨fun hN b => step c p N m hm B (frame F0) G.f (G.S p).f c.f_eq (G.f_eq p) hN b,
    fun hN b => step c p N m hm B (frame F0') G.f' (G.S p).f' c.f'_eq (G.f'_eq p) hN b⟩

end GlobalTheory.FrCoord

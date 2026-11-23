import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlIntertwinerOfResidualSpanEqTop
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnramifiedNoJump
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLamTie0OfIsLamTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumThEmptyNeZero

noncomputable section

namespace GlobalTheory.SettingHypotheses

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

def FieldSelfDual (i : X.Tw) (s : X.Sig i) : Prop :=
  ∃ B : Matrix (Fin D.R.r) (Fin D.R.r) (FractionRing (X.O0 i)), B.det ≠ 0 ∧
    ∀ g g' : GE N, (∀ x, g' x = X.cc (g (X.cc.symm x))) →
      (Tdual i s g').map (algebraMap (X.O0 i) (FractionRing (X.O0 i))) * B =
        B * ((((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g).map
          (algebraMap (X.O0 i) (FractionRing (X.O0 i)))

theorem setHyp_of_isTriple_of_galHodge (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7)
    (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (C₀ : Formalism.L2.Host.CharFrame D) (S : GlobalTheory.HeightCounting.CharSide D C₀)
    (hG : GlobalTheory.TripleLocal.GalHodge D T) (h2 : Formalism.MainNotions.BlochKatoReduction.adm2 D) (h : GlobalTheory.Triple.IsTriple D)
    (Z : GlobalTheory.LamTie.LamDat D) (hZ : Z.Ok) (hL : GlobalTheory.LamTie.IsLamTie D.ntw Z)
    (hr : 100 ≤ D.R.r) (hg : ∀ k, 2 * D.R.r ≤ D.host.g k) :
    ∀ i, D.ntw.NonzeroIndexPlace i → SetHyp (bk0 D) i := fun i hi =>
  have hA := (GlobalTheory.TripleLocal.galois_hypotheses_of_isTriple S
    (GlobalTheory.SplitFrobDense.frobDense D (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 hC)) hG h2 h).2.2 i hi
  have hT := GlobalTheory.LamTie.sum_th_empty_ne_zero D D.nd D.ntw Z hZ
    (GlobalTheory.LamTieWeak.isLamTie0_of_isLamTie D D.nd D.ntw Z hL) i hi
  ⟨hA.1, fun s _ => (hA.2 s).1, fun s _ => (hA.2 s).2, fun lam => (hT lam).1, fun lam => (hT lam).2, hr, hg⟩

end GlobalTheory.SettingHypotheses

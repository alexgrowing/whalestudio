import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.MassLink

def gm (D : D7) (i : Fin D.R.m) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E :=
  Matrix.transpose ((HSpace.gram (Wc D i)).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm))

def lat {D : D7} {Tu : Type} (Cl : LevCh D Tu) (i : Fin D.R.m) : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E) :=
  (Cl.ΛW i).comap (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)))

open Classical in

def psi (D : D7) : Finset (D.host.E →+* ℂ) := Finset.univ.image (TH.tauE D)

open Classical in

def lift (D : D7) (i : Fin D.R.m)
    (s : Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) : Theta.GA D (Wc D i) :=
  if h : ∃ k : Theta.GA D (Wc D i), k ∈ Theta.GfC (Wc D i) ∧
      (((Theta.finHom (Wc D i) k).val :
        Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))) =
        s.submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i))
  then h.choose else 1

end GlobalTheory.MassLink

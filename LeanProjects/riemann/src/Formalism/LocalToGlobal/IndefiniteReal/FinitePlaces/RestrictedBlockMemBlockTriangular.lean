import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TameAtOne

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Matrix NumberField IsDedekindDomain
open Formalism.IndefR.Datum (LowZero topL omegaG omegaQ omegaK)

namespace Formalism.IndefR.Fin.LevelGroupLemmas

section Mat
variable {κ : Type} [CommRing κ]

end Mat

section GlobalTheory
variable {κ : Type} [CommRing κ]

end GlobalTheory

section Omega
variable {D : D7}

def valG {a : ℕ} (L : LevDat D.host.E ℂ a) (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (g : ∀ PP : ↥L.Pg, GL (Fin a) (kP PP.1)) : ℂ :=
  ((ext1 L.P.H L.P.chi (fun PP => upperLeftBlock L.hr (g PP)) : ℂˣ) : ℂ) *
    (∏ PP : ↥L.Pg, ∏ c ∈ Finset.range L.s,
      ((L.cg (c + 1) PP.1 (dBlk (blkOf L.r L.t) (c + 1) (g PP)) : ℂˣ) : ℂ)) *
    ∏ PP : ↥L.Pg, (((χj PP.1 (Matrix.GeneralLinearGroup.det (g PP))) : ℂˣ) : ℂ)⁻¹

end Omega

section Conj
variable {D : D7}

end Conj

section Q
variable {D : D7}

end Q

section Det
variable {κ : Type} [CommRing κ]

end Det

section Lev
open scoped TensorProduct
variable {D : D7}

def levUnit {n : ℕ} (L : LevDat D.host.E ℂ n) (x : ∀ PP : Pl D.host.E, GL (Fin n) (kP PP)) : ℂˣ :=
  ext1 L.P.H L.P.chi (fun PP : ↥L.Pg => upperLeftBlock L.hr (x PP.1)) *
    (∏ PP ∈ L.Pg, ∏ c ∈ Finset.range L.s, L.cg (c + 1) PP (dBlk (blkOf L.r L.t) (c + 1) (x PP))) *
    ∏ PP ∈ L.Q, L.xq PP (dBlk (blk2 L.r) 1 (x PP))

end Lev

section Laws
variable {D : D7}

end Laws

section Bridge
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}

end Bridge

end Formalism.IndefR.Fin.LevelGroupLemmas

end

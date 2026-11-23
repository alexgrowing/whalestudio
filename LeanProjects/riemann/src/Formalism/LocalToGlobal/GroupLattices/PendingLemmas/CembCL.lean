import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.PNeZeroOL
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.FormalGroupSystem
open scoped TensorProduct

namespace Formalism.L2.G.Pend

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)

def cembCL : CEmbC (gatL D u h L h5 h2 he r Lc I ψ e) where
  toCEmb := cembL D u h L h5 h2 he r Lc I ψ e
  rd := fun _ => rdW p (orderOf (zPsi D.R.toFrame h))
  compat := compat_L D u h L h5 h2 he r Lc I ψ e

variable (c : ℕ) (hc : CloudBound D u c)
  (Lv : Levels (fillsL D u h L h5 h2 he r Lc I ψ e c hc)) (Ch : Chain Lv)
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k) (hfin : ∀ j c', (Lv.lev j c').FinClasses) (hst : FinStab Lv)
  {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g)

abbrev pendTL
    (F : ∀ j, (sysL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin).Lt j →
      (sysL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin).Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin (((sysL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin).Pj (j + 1)).m + 1) ×
        Fin (((sysL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin).Pj j).m + 1)) ℂ_[p]) :
    Pend (sysL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin) :=
  @pendT p hp (sysL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin) (fracOL L)
    (cembCL D u h L h5 h2 he r Lc I ψ e) hfin hst g hLT D.what₂.Tau
    (posL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin) F

end Formalism.L2.G.Pend

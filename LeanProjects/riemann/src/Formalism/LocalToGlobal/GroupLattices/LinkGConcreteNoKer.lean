import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
import Formalism.LocalToGlobal.GroupLattices.AdmissibleFamilyNoKernel
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.GramTotallyDefinite

noncomputable section

namespace Formalism.L2.G

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stdSubF_of_tied {eps : ℝ} (Fm : FamP eps) (h : GroupCompatibilityFamily Fm) : Ev Fm fun x i => Joints.StdSubAt (Fm.D x i) := by
  obtain ⟨x0, h0⟩ := h.and (Ev.x1 Fm)
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨ht, hx1⟩ := h0 x hx i
  obtain ⟨G⟩ := ht hx1
  exact stdSubAt_of_ring _ G.ring

theorem gatEF_of_tied {eps : ℝ} (Fm : FamP eps) (h : GroupCompatibilityFamily Fm) : Ev Fm fun x i => TrivialStabiliserFiniteClasses (Fm.D x i) := by
  obtain ⟨x0, h0⟩ := h.and (Ev.x1 Fm)
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨ht, hx1⟩ := h0 x hx i
  obtain ⟨G⟩ := ht hx1
  exact gatE_of_gatIs _ G.herm.lev0
    (fun u => Triv.trivStabU (G.herm.lev0 u) (Fm.D x i).host.g_prime (Fm.D x i).host.g_ne) G.gat

theorem npDescF_of_tied {eps : ℝ} (Fm : FamP eps) (h : GroupCompatibilityFamily Fm) : NPDescF Fm := by
  refine Cmp.npDescF_of_valRatF Fm ?_
  obtain ⟨x0, h0⟩ := h
  exact ⟨x0, fun x hx i hx1 => by
    obtain ⟨G⟩ := h0 x hx i hx1
    exact Cmp.CmpTied.valRat G.cmp⟩

theorem linkG_concrete (𝒞 : FamClass) (h : Loc)
    (hT : Closed 𝒞 fun Fm _ => GroupCompatibilityFamily Fm)
    (hsys : Closed 𝒞 fun Fm _ => Ev Fm fun x i => LocalDataSystem (Fm.Gx x i) (Fm.Gy x i) (Formalism.MainNotions.AuxBlock8.lowU (Fm.D x i)))
    (hsysS : Closed 𝒞 fun Fm _ => Ev Fm fun x i => LocalDataSystem (Fm.Gx x i) (Fm.Gy x i) (Formalism.MainNotions.G.lowFE (Fm.L x i)))
    (h2 : Closed 𝒞 fun Fm _ => Adm2F Fm) :
    Closed 𝒞 fun Fm _ => LinkG Fm := by
  refine link_of_numbers_proved 𝒞 h ?_ h2 (hT.imp fun Fm _ _ ht => npDescF_of_tied Fm ht)
  exact ((hT.and hsys).and hsysS).imp fun Fm _ _ hh =>
    { gatE := gatEF_of_tied Fm hh.1.1
      stdSub := stdSubF_of_tied Fm hh.1.1
      localSystemLowTerm := hh.1.2
      localSystemSizeLowTerm := hh.2 }

theorem linkG_concrete_noKer (𝒞 : FamClass) (h : Loc)
    (hT : Closed 𝒞 fun Fm _ => GroupCompatibilityFamily Fm) (h2 : Closed 𝒞 fun Fm _ => Adm2F Fm) :
    Closed 𝒞 fun Fm _ => LinkG Fm :=
  link_of_local_closed 𝒞 h (hT.imp fun Fm _ _ ht => gatEF_of_tied Fm ht) (hT.imp fun Fm _ _ ht => stdSubF_of_tied Fm ht)
    h2 (hT.imp fun Fm _ _ ht => npDescF_of_tied Fm ht)

theorem linkG_concrete5 (𝒞 : FamClass) (hT : Closed 𝒞 fun Fm _ => GroupCompatibilityFamily Fm) (h2 : Closed 𝒞 fun Fm _ => Adm2F Fm) :
    Closed 𝒞 fun Fm _ => LinkG Fm :=
  linkG_concrete_noKer 𝒞 loc_proved hT h2

end Formalism.L2.G

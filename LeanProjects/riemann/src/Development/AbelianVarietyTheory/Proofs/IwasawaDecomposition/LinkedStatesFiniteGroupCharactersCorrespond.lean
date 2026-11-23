import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharactersOnLiftFormsExtendedData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

namespace GlobalTheory.HeightCounting.SerMove

open GlobalTheory.Mem.R3.Tr

theorem chi_link_side : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ u, HEq (γ u) u) → ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → ∀ u : (sideAt x g hg a).Γ, ((((sideAt x' g' hg' a').R.FW j').chi (γ u) : (Dof x').what₂.LLˣ) : (Dof x').what₂.LL) = ι ((((sideAt x g hg a).R.FW j).chi u : (Dof x).what₂.LLˣ) : (Dof x).what₂.LL) := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' γ hγ j j' hj u
  apply RingHom.injective (Dof x').what₂.embLL
  have hC : x.m.z.R.toLevCh.C.mu0 j = f.mu0 j := by
    rw [x.m.z.lev.C, w.C_eq]; rfl
  have hC' : x'.m.z.R.toLevCh.C.mu0 j' = f'.mu0 j' := by
    rw [x'.m.z.lev.C, w'.C_eq]; rfl
  refine (x'.m.z.pins.char.base.grp.chiW j' (γ u)).trans
    (Eq.trans ?_ ((l.cp.embLL _).trans (x.m.z.pins.char.base.grp.chiW j u)).symm)
  exact GlobalTheory.Mem.R3.ChiExt.prod_eq l.enl.1 l.fr l.px j j' hj l.extN.Pg x.m.z.R.eG x'.m.z.R.eG l.extN.eG
    (x.m.z.R.chi ((j : ℕ) + 1)) (x'.m.z.R.chi ((j' : ℕ) + 1))
    (fun PP hP => hC ▸ x.m.z.lev.is.chi j PP hP) (fun PP hP => hC' ▸ x'.m.z.lev.is.chi j' PP hP) u (γ u) (hγ u)

end GlobalTheory.HeightCounting.SerMove

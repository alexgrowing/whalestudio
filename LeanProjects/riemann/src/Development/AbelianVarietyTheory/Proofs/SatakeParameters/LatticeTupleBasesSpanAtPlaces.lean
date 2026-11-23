import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.TwV.Joint.basesAt_span : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → ∀ v, (sysS H X std).latAt v j La.2 = colSpan ((sysS H X std).G.P.W v) ((basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om j La.2) v : Matrix _ _ ((sysS H X std).G.P.Qq v)) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j La hLa v
  obtain ⟨g, hdet, hg'⟩ := Formalism.L2.G.Pend.latAt_isLattice (sysS H X std) j La.2 hLa v
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 hdet
  unfold basesAt
  exact Classical.epsilon_spec (p := fun g' : GL (Fin (((sysS H X std).Pj j).m + 1)) ((sysS H X std).G.P.Qq v) =>
      (sysS H X std).latAt v j La.2 = colSpan ((sysS H X std).G.P.W v) (g' : Matrix _ _ _)) ⟨hu.unit, by rw [hu.unit_spec]; exact hg'⟩

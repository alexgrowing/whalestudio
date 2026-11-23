import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GidxFacts
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.SitePrime

set_option maxHeartbeats 2000000 in

theorem resChar_not_mem_S : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), D.what₂.places.resChar w ∉ (t.O u μ).S := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ _ J hmem
  obtain ⟨-, -, -, hg'⟩ := GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg
  obtain ⟨-, -, -, -, -, hT'⟩ := id hg
  rw [t.O_S u μ] at hmem
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with h | (h | h) | h
  · exact hT' (h ▸ dvd_rfl)
  · exact hg' 0 h
  · exact hg' 1 h
  · exact J.away h

end GlobalTheory.TwV.SitePrime

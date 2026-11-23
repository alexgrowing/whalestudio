import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
import Formalism.LocalToGlobal.HermitianForms.ExtraSym
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ExtraTie

open Formalism.L2.Herm

theorem errX_eq {D : D7} (X : FullTiedS D) (H : ColsHermS D) (hX : X.cols = H) (e : ErrX D)
    (h1 : e.piG = (H.levelZeroCompatibility D.u₀).piG) (h2 : ∀ u, e.piT u = (H.atT u).piU)
    (h3 : ∀ u v, e.vPl u v = (H.base.vT u v).1) : e = toErrXS X := by
  subst hX
  obtain ⟨piG, piG_K, piG_norm, piT, piT_K, piT_norm, piT_cong, vPl, vPl_inj, norm_mem_place_ideal⟩ := e
  have e1 : piG = (X.levelZeroCompatibility D.u₀).piG := h1
  have e2 : piT = fun u => (X.atT u).piU := funext h2
  have e3 : vPl = fun u v => (X.base.vT u v).1 := funext fun u => funext (h3 u)
  subst e1 e2 e3
  rfl

end GlobalTheory.Mem.Col2.TC.ExtraTie

end

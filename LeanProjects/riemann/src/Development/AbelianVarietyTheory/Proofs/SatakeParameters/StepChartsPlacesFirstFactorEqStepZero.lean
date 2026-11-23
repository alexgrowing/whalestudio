import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdicRingEquivEqSelf
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000 in

theorem chart_places_firstFactor_eq_zero :
    Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
      ∀ j (hj : j + 1 ≤ D.R.m) (β : (I.at' j hj).st.Ch) v, ((I.at' j hj).st.loc β).pl v = (A0 J).pl v ∧
        ∀ x, phiA ((I.at' j hj).st.loc β) v x = phiA (A0 J) v x) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _hD _hS j hj β v
  refine ⟨J.pl j hj β v, ?_⟩
  have h := firstFactor_agree D.host.F D.host.E _ _ (((I.at' j hj).st.loc β).pl v).1 ((A0 J).pl v).1
    (((I.at' j hj).st.loc β).eQ v) ((A0 J).eQ v) (((I.at' j hj).st.loc β).ph v) ((A0 J).ph v)
    (fun c => by
      show ((((I.at' j hj).st.loc β).spl v) ((1 : D.host.E) ⊗ₜ[D.host.F] c)).1 = c
      rw [J.alg j hj β v c])
    (fun c => by
      show (((A0 J).spl v) ((1 : D.host.E) ⊗ₜ[D.host.F] c)).1 = c
      rw [J.alg0 v c])
    ((H.core j hj β).int v) (J.one.int v)
    (fun a => by
      have h1 := RingHom.congr_fun (J.iw j hj β v) a
      exact h1)
  exact h.2

end GlobalTheory.TwV.Xc

import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDatumChars

theorem xi_eq_of_heq {D : D7} {C C' : Formalism.L2.Host.CharFrame D} {n : NChoice D} (h : C = C')
    (T : Formalism.L2.Host.TupTied D C n) (T' : Formalism.L2.Host.TupTied D C' n) (hT : HEq T T') : T.xi = T'.xi := by
  subst h; rw [eq_of_heq hT]

theorem weil_chars : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (X.R.toLevCh.mu (X.tupT (D.nd.mu i))) X.R.eta (j.1 + 1)).1 (P.tp.tup (D.nd.mu i) j) ∧ Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (X.R.toLevCh.mu (X.tupT (D.nd.mu i))) X.R.eta (j.1 + 1)).2 (P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹) := by
  intro hL D P X A i j hj
  have hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) :=
    Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩
  have hlev := X.recR.base.lev
  have hx : X.R.toLevCh.xiH (X.tupT (D.nd.mu i)) = P.tp.xi (D.nd.mu i) := by
    rw [X.recR.tupXi _ hμ, xi_eq_of_heq X.cfEq X.Tp P.tp X.tpEq]
  have hxi := hlev.xi (X.tupT (D.nd.mu i))
  rw [hx] at hxi
  have hm := hlev.mu0 j
  have he := hlev.eta
  have hC : X.R.toLevCh.C = P.cf := X.cfEq
  rw [hC] at hm he
  exact ⟨GlobalTheory.Mem.TupChar.chrEq_mul hm hxi, GlobalTheory.ClassScalarValue.chrEq_mul_inv hm hxi he⟩

end GlobalTheory.WeilDatumChars

import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftDat

open GlobalTheory.LiftLevel

variable {D : D7}

def rowAdj (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (v : Fin T.rank → D.host.E) :
    Matrix (Fin 1) (Fin T.rank) (EAf D) :=
  toEAf D a • HMul.hMul ((Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] v k) * incA D (T.gram k l)).map (toEAf D)) βT.val

def rowRed (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E)
    (v : Fin T.rank → D.host.E) : Fin T.rank → Formalism.L2.DIV.kP PP :=
  fun j => redM PP (rowAdj T βT a e v) 0 j

theorem liftI_le {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {PP : Formalism.L2.DIV.Pl D.host.E} (h : PP ∈ Pg ∪ Q) :
    liftI Pg Q ≤ conjI PP.asIdeal :=
  Ideal.prod_le_inf.trans (Finset.inf_le h)

def toConj (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (h : PP ∈ Pg ∪ Q) :
    𝓞 D.host.E ⧸ liftI Pg Q →+* 𝓞 D.host.E ⧸ conjI PP.asIdeal :=
  Ideal.quotientMap (conjI PP.asIdeal) (RingHom.id _) (fun _ hx => liftI_le h hx)

def conjRes (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (h : PP ∈ Pg ∪ Q) :
    𝓞 D.host.E ⧸ liftI Pg Q →+* Formalism.L2.DIV.kP PP :=
  Ideal.quotientMap PP.asIdeal GlobalTheory.SW.Lev.bar (fun _ hx => GlobalTheory.SW.Lev.mem_conjI.1 (liftI_le h hx))

def Jgrp (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ) : Subgroup (GL (Fin r) (𝓞 D.host.E ⧸ liftI Pg Q)) :=
  ⨅ PP : Pg, (Matrix.GeneralLinearGroup.map (toConj Pg Q PP.1 (Finset.mem_union_left _ PP.2))).ker

def lamHom (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) : Jgrp Pg Q r →* ℂˣ :=
  (∏ PP ∈ Q.attach, (ξ PP.1).comp ((Units.map (conjRes Pg Q PP.1 (Finset.mem_union_right _ PP.2)).toMonoidHom).comp
    (Matrix.GeneralLinearGroup.det.comp (Jgrp Pg Q r).subtype)))⁻¹

theorem mem_Jgrp {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {r : ℕ} {κ : GL (Fin r) (𝓞 D.host.E ⧸ liftI Pg Q)} :
    κ ∈ Jgrp Pg Q r ↔ ∀ PP (h : PP ∈ Pg),
      Matrix.GeneralLinearGroup.map (toConj Pg Q PP (Finset.mem_union_left _ h)) κ = 1 := by
  simp [Jgrp, Subgroup.mem_iInf, MonoidHom.mem_ker]

theorem lamHom_apply {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {r : ℕ}
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (κ : Jgrp Pg Q r) :
    lamHom Pg Q r ξ κ = (∏ PP ∈ Q.attach, ξ PP.1 (Units.map (conjRes Pg Q PP.1
      (Finset.mem_union_right _ PP.2)).toMonoidHom (Matrix.GeneralLinearGroup.det (κ : GL (Fin r) _))))⁻¹ := by
  simp [lamHom, MonoidHom.finset_prod_apply]

def mkLevel {S T : HSp D} (C : Ctx S T) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (h1 : liftI Pg Q ≠ ⊤) (h2 : liftI Pg Q ≠ ⊥)
    (h3 : IsCoprime (liftI Pg Q) (conjI (liftI Pg Q))) (h4 : IsCoprime (liftI Pg Q) (Ideal.span {2}))
    (β : Fin T.rank → Fin T.rank → D.host.E) (hβ : ∀ i, β i ∈ C.X.Λ)
    (hsp : C.X.Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ liftI Pg Q • C.X.Λ)
    (Lv0 : GlobalTheory.SW.Level C.X) : GlobalTheory.SW.Level C.X where
  𝔪 := liftI Pg Q
  proper := h1
  ne_bot := h2
  cop := h3
  odd := h4
  β := β
  β_mem := hβ
  β_span := hsp
  J := Jgrp Pg Q T.rank
  lam := lamHom Pg Q T.rank ξ
  w := Lv0.w
  w_int := Lv0.w_int
  w_tr := Lv0.w_tr

end GlobalTheory.LiftDat

end

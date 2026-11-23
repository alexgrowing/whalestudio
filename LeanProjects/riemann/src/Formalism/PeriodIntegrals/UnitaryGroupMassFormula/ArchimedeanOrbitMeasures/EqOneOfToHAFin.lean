import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.WittNr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ContinuousSplitA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SplitG

noncomputable section

open MeasureTheory NumberField Set
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace PI.AprimeInfU

theorem tauF_eq_comm {D : D7} (X : HidaSetting D) (y : AF X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    tauF X.B.I y = Algebra.TensorProduct.comm X.B.I.F (Af X.B.I.F) X.B.I.E
      (tensMap (E := X.B.I.E) (sndA X.B.I.F) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tauF_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem toHA_fin_one {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (s : X.B.I.Ginf) :
    (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (s, 1))).2 = 1 := by
  have hbr := ((toHA_isBridge X.B.I hb) (s, 1)).2
  apply Subtype.ext
  apply Units.ext
  ext i j
  have e := congrFun (congrFun hbr i) j
  simp only [ofHAFin, Matrix.map_apply] at e
  rw [tauF_eq_comm] at e
  have e2 := congrArg (Algebra.TensorProduct.comm X.B.I.F (Af X.B.I.F) X.B.I.E).symm e
  rw [AlgEquiv.symm_apply_apply] at e2
  show tensMap (E := X.B.I.E) (sndA X.B.I.F) _ = _
  rw [← e2]
  show _ = (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j
  simp only [Formalism.MainNotions.S.AutInst.fmat, OneMemClass.coe_one, Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem eq_one_of_toHA_fin {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : X.B.I.GA)
    (h : (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb p)).2 = 1) : p.2 = 1 := by
  have hbr := ((toHA_isBridge X.B.I hb) p).2
  apply Subtype.ext
  apply Units.ext
  ext i j
  have e := congrFun (congrFun hbr i) j
  simp only [ofHAFin, Matrix.map_apply] at e
  rw [tauF_eq_comm] at e
  have h2 : tensMap (E := X.B.I.E) (sndA X.B.I.F) (hmat X.B.I (toHA X.B.I hb p) i j) =
      (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j := by
    have := congrArg (fun g : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J =>
      (HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J g).val i j) h
    exact this
  rw [h2] at e
  rw [Formalism.MainNotions.S.AutInst.fmat] at e
  show _ = (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) i j
  rw [e, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

section Bridge

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def evInf (v : InfinitePlace X.B.I.F) : Ainf X.B.I.F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding v).comp
    (Pi.evalRingHom (fun w : InfinitePlace X.B.I.F => w.Completion) v)

def thetaInf (v : InfinitePlace X.B.I.F) : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E →+* ℂ :=
  letI : Algebra X.B.I.F ℂ := v.embedding.toAlgebra
  (Algebra.TensorProduct.lift
    ({ evInf X v with commutes' := fun a => evV_algebraMap X.B.I v a } : Ainf X.B.I.F →ₐ[X.B.I.F] ℂ)
    ({ X.B.I.φ v with commutes' := X.B.I.φ_over v } : X.B.I.E →ₐ[X.B.I.F] ℂ)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem thetaV_eq (v : InfinitePlace X.B.I.F) (y : AF X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    thetaV X.B.I v y = thetaInf X v (tensMap (E := X.B.I.E) (fstA X.B.I.F) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [thetaV_tmul]
    simp only [thetaInf, tensMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.lift_tmul, AlgHom.id_apply]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem ofHAInf_congr (a b : HAd X.B.I)
    (h : (splitA X.B.I.cm.sig X.B.I.J a).1 = (splitA X.B.I.cm.sig X.B.I.J b).1) :
    ofHAInf X.B.I a = ofHAInf X.B.I b := by
  funext v
  unfold ofHAInf
  congr 2
  ext i j
  simp only [Matrix.map_apply, thetaV_eq]
  have := congrArg (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    (HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g).val i j) h
  exact congrArg (thetaInf X v) this

theorem ofHAFin_congr (a b : HAd X.B.I)
    (h : (splitA X.B.I.cm.sig X.B.I.J a).2 = (splitA X.B.I.cm.sig X.B.I.J b).2) :
    ofHAFin X.B.I a = ofHAFin X.B.I b := by
  unfold ofHAFin
  ext i j
  simp only [Matrix.map_apply, tauF_eq_comm]
  have := congrArg (fun g : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    (HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J g).val i j) h
  exact congrArg (Algebra.TensorProduct.comm X.B.I.F (Af X.B.I.F) X.B.I.E) this

theorem eq_of_ofHA (p q : X.B.I.GA) (h1 : ofHAInf X.B.I (toHA X.B.I hb p) = ofHAInf X.B.I (toHA X.B.I hb q))
    (h2 : ofHAFin X.B.I (toHA X.B.I hb p) = ofHAFin X.B.I (toHA X.B.I hb q)) : p = q := by
  obtain ⟨a₁, b₁⟩ := (toHA_isBridge X.B.I hb) p
  obtain ⟨a₂, b₂⟩ := (toHA_isBridge X.B.I hb) q
  refine Prod.ext (funext fun v => ?_) ?_
  · exact Subtype.ext (Units.ext ((a₁ v).trans ((congrFun h1 v).trans (a₂ v).symm)))
  · exact Subtype.ext (Units.ext (b₁.trans (h2.trans b₂.symm)))

theorem toInf_mul (s t : X.B.I.Ginf) : X.toInf hb (s * t) = X.toInf hb s * X.toInf hb t := by
  have e : ((s * t, 1) : X.B.I.GA) = (s, 1) * (t, 1) := by simp
  show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (s * t, 1))).1 = _
  rw [e, map_mul, map_mul]
  rfl

theorem toHA_inf_one (hS : MassDataMassesW.SplitIso) (x : X.B.I.Gf) :
    (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (1, x))).1 = 1 := by
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  set h := toHA X.B.I hb (1, x) with hh
  set h' := e.symm (1, (splitA X.B.I.cm.sig X.B.I.J h).2) with hh'
  have hs' : splitA X.B.I.cm.sig X.B.I.J h' = (1, (splitA X.B.I.cm.sig X.B.I.J h).2) := by
    have h0 := e.apply_symm_apply (1, (splitA X.B.I.cm.sig X.B.I.J h).2)
    rw [he] at h0
    exact h0
  set q := (toHA X.B.I hb).symm h' with hq
  have hqh : toHA X.B.I hb q = h' := (toHA X.B.I hb).apply_symm_apply h'
  have h1 : ofHAInf X.B.I (toHA X.B.I hb q) = ofHAInf X.B.I (toHA X.B.I hb (1, 1)) := by
    rw [hqh]
    apply ofHAInf_congr
    rw [hs', show ((1, 1) : X.B.I.GA) = 1 from rfl, map_one, map_one]
    rfl
  have h1' : ofHAInf X.B.I (toHA X.B.I hb (1, 1)) = ofHAInf X.B.I (toHA X.B.I hb (1, x)) := by
    obtain ⟨a₁, -⟩ := (toHA_isBridge X.B.I hb) (1, 1)
    obtain ⟨a₂, -⟩ := (toHA_isBridge X.B.I hb) (1, x)
    funext v
    exact (a₁ v).symm.trans (a₂ v)
  have h2 : ofHAFin X.B.I (toHA X.B.I hb q) = ofHAFin X.B.I (toHA X.B.I hb (1, x)) := by
    rw [hqh]
    apply ofHAFin_congr
    rw [hs']
  have hq1 : q = (1, x) := eq_of_ofHA X hb q (1, x) (h1.trans h1') h2
  have : h' = h := by rw [← hqh, hq1]
  rw [← this, hs']

theorem split_toHA (hS : MassDataMassesW.SplitIso) (p : X.B.I.GA) :
    splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb p) = (X.toInf hb p.1, finHA X hb p.2) := by
  have e : p = (p.1, 1) * (1, p.2) := by simp
  conv_lhs => rw [e, map_mul, map_mul]
  refine Prod.ext ?_ ?_
  · show X.toInf hb p.1 * (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (1, p.2))).1 = _
    rw [toHA_inf_one X hb hS, mul_one]
  · show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (p.1, 1))).2 * finHA X hb p.2 = _
    rw [toHA_fin_one X hb, one_mul]

theorem toInf_surjective (hS : MassDataMassesW.SplitIso) : Function.Surjective (X.toInf hb) := by
  intro y
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  set p := (toHA X.B.I hb).symm (e.symm (y, 1))
  have hp : splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb p) = (y, 1) := by
    rw [← he]
    simp [p]
  have h2 : p.2 = 1 := eq_one_of_toHA_fin X hb p (by rw [hp])
  refine ⟨p.1, ?_⟩
  have := congrArg Prod.fst hp
  rw [split_toHA X hb hS] at this
  exact this

end Bridge

end PI.AprimeInfU

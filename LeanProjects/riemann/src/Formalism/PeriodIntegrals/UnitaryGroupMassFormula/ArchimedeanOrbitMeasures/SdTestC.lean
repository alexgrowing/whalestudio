import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SdCoord

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

theorem totReal_of {D : D7} (X : HidaSetting D) : ∀ v : InfinitePlace X.B.I.F, v.IsReal :=
  fun v => X.B.I.cm.totReal.isReal v

def tupCoord {D : D7} (X : HidaSetting D) :
    TupI X ≃ₜ EuclideanSpace ℝ (Fin (D.R.rS + 1 + D.R.rS) × Fin X.B.I.n ×
      Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F) :=
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  (Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ =>
    (tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F)).trans
      (Homeomorph.piCongrRight fun _ => ainfReal (totReal_of X))).trans (flat4 _ _ _ _)

theorem tupCoord_add {D : D7} (X : HidaSetting D) (x y : TupI X) :
    tupCoord X (x + y) = tupCoord X x + tupCoord X y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  simp only [tupCoord, Homeomorph.trans_apply]
  rw [← flatten_four_add]
  congr 1
  funext a i k
  simp only [Homeomorph.piCongrRight_apply, Homeomorph.trans_apply, Pi.add_apply]
  rw [tensCoord_add]
  exact ainfReal_add (totReal_of X) _ _

theorem psiInf_addP {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (a b : Ainf F) :
    psiInf F ψ (a + b) = psiInf F ψ a * psiInf F ψ b := by
  have h : (pairA F (a + b) 0 : AF F) = pairA F a 0 + pairA F b 0 := by
    show ((a + b, 0) : Ainf F × Af F) = ((a, 0) : Ainf F × Af F) + ((b, 0) : Ainf F × Af F)
    rw [Prod.mk_add_mk, add_zero]
  simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf]
  rw [h, AddChar.map_add_eq_mul]

theorem psiInf_eq {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hS : Formalism.L2.SG.LocVol.IsStdChar ψ) :
    psiInf F ψ = fun x => Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ)) :=
  funext hS

theorem continuous_psiInfP {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hS : Formalism.L2.SG.LocVol.IsStdChar ψ) : Continuous (psiInf F ψ) := by
  rw [psiInf_eq ψ hS]
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding (v := w)).continuous.comp (continuous_apply w))

theorem norm_psiInfP {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hS : Formalism.L2.SG.LocVol.IsStdChar ψ) (x : Ainf F) : ‖psiInf F ψ x‖ = 1 := by
  rw [hS x]
  have : 2 * (Real.pi : ℂ) * Complex.I *
      ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ) =
      ((2 * Real.pi * ∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ) *
        Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem BR_add_leftP {D : D7} (X : HidaSetting D) (x x' y : TupI X) :
    BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (x + x') y = BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y + BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x' y := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem BR_add_rightP {D : D7} (X : HidaSetting D) (x y y' : TupI X) :
    BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x (y + y') = BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y + BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y' := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem continuous_traceP {D : D7} (X : HidaSetting D) :
    Continuous (Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  exact IsModuleTopology.continuous_of_linearMap _

theorem continuous_BR_leftP {D : D7} (X : HidaSetting D) (y : TupI X) : Continuous fun x : TupI X => BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  show Continuous fun x : TupI X => ∑ a, Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)
    (∑ i, ∑ j, sigR (Ainf X.B.I.F) X.B.I.cm.sig (x a i) * JR (Ainf X.B.I.F) X.B.I.J i j * y a j)
  exact continuous_finsetSum _ fun a _ => (continuous_traceP X).comp (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => (((continuous_sigRP (Ainf X.B.I.F) X.B.I.cm.sig).comp
      ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul continuous_const)

theorem continuous_BR_rightP {D : D7} (X : HidaSetting D) (x : TupI X) : Continuous fun y : TupI X => BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  show Continuous fun y : TupI X => ∑ a, Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)
    (∑ i, ∑ j, sigR (Ainf X.B.I.F) X.B.I.cm.sig (x a i) * JR (Ainf X.B.I.F) X.B.I.J i j * y a j)
  exact continuous_finsetSum _ fun a _ => (continuous_traceP X).comp (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply a)))

theorem sdTestI_holds : SdTestI := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI := hP.2.2.2.2.1.1
  have hS := hP.2.2.1
  have hpc := continuous_psiInfP ψ hS
  exact ST.testEx_of_homeo μinf _ (tupCoord X) (tupCoord_add X)
    (fun x x' y => by rw [BR_add_leftP, psiInf_addP])
    (fun x y y' => by rw [BR_add_rightP, psiInf_addP])
    (fun x y => norm_psiInfP ψ hS _)
    (fun y => hpc.comp (continuous_BR_leftP X y))
    (fun x => hpc.comp (continuous_BR_rightP X x))

theorem invFib_holds : InvFib := invFib_of (sdInvG_of sdTestI_holds)

end PI.AprimeInfW

import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensGen

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

section Coord

variable {D : D7} (X : HidaSetting D)

def matCoord : (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) ≃ₜ EuclideanSpace ℝ (Fin (D.R.rS + 1 + D.R.rS) × Fin (D.R.rS + 1 + D.R.rS) × Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F) :=
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  (Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ =>
    (tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F)).trans
      (Homeomorph.piCongrRight fun _ => ainfReal (totReal_of X))).trans (flat4 _ _ _ _)

theorem matCoord_add (x y : (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : matCoord X (x + y) = matCoord X x + matCoord X y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  simp only [matCoord, Homeomorph.trans_apply]
  rw [← flatten_four_add]
  congr 1
  funext a i k
  simp only [Homeomorph.piCongrRight_apply, Homeomorph.trans_apply, Pi.add_apply]
  rw [tensCoord_add]
  exact ainfReal_add (totReal_of X) _ _

def scalI (t : ℝ) : Ainf X.B.I.F := (ainfReal (totReal_of X)).symm fun _ => t

theorem matCoord_scal (t : ℝ) (S : (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
    matCoord X (fun a b => algebraMap (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) (scalI X t) * S a b) =
      t • matCoord X S := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  simp only [matCoord, Homeomorph.trans_apply]
  have hf : ∀ f : Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) → Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) → InfinitePlace X.B.I.F → ℝ,
      flat4 _ _ _ _ (t • f) = t • flat4 _ _ _ _ f := by
    intro f
    show (EuclideanSpace.equiv _ ℝ).symm _ = t • (EuclideanSpace.equiv _ ℝ).symm _
    rw [← map_smul]
    rfl
  rw [← hf]
  congr 1
  funext a i k v
  simp only [Homeomorph.piCongrRight_apply, Homeomorph.trans_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Algebra.smul_def]
  have h1 : tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (scalI X t • S a i) =
      scalI X t • tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (S a i) :=
    map_smul (Module.Free.chooseBasis (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)).equivFun _ _
  rw [h1]
  show complReal v ((totReal_of X) v) ((scalI X t) v * _) = t * _
  rw [show complReal v ((totReal_of X) v) ((scalI X t) v * tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (S a i) k v) =
      complReal v ((totReal_of X) v) ((scalI X t) v) *
        complReal v ((totReal_of X) v) (tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (S a i) k v) from
    map_mul (InfinitePlace.Completion.ringEquivRealOfIsReal ((totReal_of X) v)) _ _]
  congr 1
  show ainfReal (totReal_of X) (scalI X t) v = t
  simp [scalI]

theorem herm_scal (t : ℝ) (S : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :
    Matrix.of (fun a b => algebraMap (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) (scalI X t) * (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) a b) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) := by
  intro a b
  have hS := S.2 a b
  simp only [Matrix.of_apply, map_mul]
  rw [hS]
  congr 1
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem matCoord_symm_add (c c' : EuclideanSpace ℝ (Fin (D.R.rS + 1 + D.R.rS) × Fin (D.R.rS + 1 + D.R.rS) × Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F)) :
    (matCoord X).symm (c + c') = (matCoord X).symm c + (matCoord X).symm c' := by
  apply (matCoord X).injective; rw [matCoord_add]; simp

theorem matCoord_symm_zero : (matCoord X).symm 0 = 0 := by
  apply (matCoord X).injective
  have h := matCoord_add X 0 0
  simp only [add_zero] at h
  rw [Homeomorph.apply_symm_apply]
  exact (by simpa using h : matCoord X 0 = 0).symm

theorem matCoord_symm_smul (t : ℝ) (c : EuclideanSpace ℝ (Fin (D.R.rS + 1 + D.R.rS) × Fin (D.R.rS + 1 + D.R.rS) × Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F)) :
    (matCoord X).symm (t • c) = fun a b => algebraMap (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) (scalI X t) * (matCoord X).symm c a b := by
  apply (matCoord X).injective; rw [matCoord_scal]; simp

def Wh : Submodule ℝ (EuclideanSpace ℝ (Fin (D.R.rS + 1 + D.R.rS) × Fin (D.R.rS + 1 + D.R.rS) × Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F)) where
  carrier := {c | Matrix.of ((matCoord X).symm c) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)}
  add_mem' := by
    intro c c' hc hc'
    show Matrix.of ((matCoord X).symm (c + c')) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)
    rw [matCoord_symm_add, ← Matrix.of_add_of]
    exact add_mem hc hc'
  zero_mem' := by
    show Matrix.of ((matCoord X).symm 0) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)
    rw [matCoord_symm_zero, Matrix.of_zero]
    exact zero_mem _
  smul_mem' := by
    intro t c hc
    show Matrix.of ((matCoord X).symm (t • c)) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)
    rw [matCoord_symm_smul]
    exact herm_scal X t ⟨_, hc⟩

theorem hermCoord_mem (S : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) : matCoord X (Matrix.of.symm (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))) ∈ Wh X := by
  show Matrix.of ((matCoord X).symm (matCoord X (Matrix.of.symm (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))))) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)
  rw [Homeomorph.symm_apply_apply, Equiv.apply_symm_apply]; exact S.2

def hermCoord : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) ≃ₜ Wh X where
  toFun S := ⟨matCoord X (Matrix.of.symm (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))), hermCoord_mem X S⟩
  invFun w := ⟨Matrix.of ((matCoord X).symm w), w.2⟩
  left_inv S := by apply Subtype.ext; simp
  right_inv w := by apply Subtype.ext; simp
  continuous_toFun := ((matCoord X).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((matCoord X).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem hermCoord_add (S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) : hermCoord X (S + T) = hermCoord X S + hermCoord X T := by
  apply Subtype.ext
  exact matCoord_add X (Matrix.of.symm (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))) (Matrix.of.symm (T : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))

theorem hermCoord_symm_add (x y : Wh X) :
    (hermCoord X).symm (x + y) = (hermCoord X).symm x + (hermCoord X).symm y := by
  apply (hermCoord X).injective; rw [hermCoord_add]; simp

end Coord

section Pair

variable {D : D7} (X : HidaSetting D)

theorem pairHerm_addL (S S' T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :
    pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ (S + S') T =
      pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S T + pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S' T := by
  simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add, mul_add]

theorem pairHerm_addR (S T T' : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :
    pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S (T + T') =
      pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S T + pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S T' := by
  simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]

theorem pairHerm_symm (S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :
    pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S T = pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ T S := by
  simp only [pairHerm]
  congr 2
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem continuous_pairHerm_leftP (T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :
    Continuous fun S : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) => pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S T := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  show Continuous fun S : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) => algebraMap X.B.I.F (Ainf X.B.I.F) (1 / 2) *
    Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)
      (∑ a, ∑ b, (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) a b * (T : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) b a)
  refine continuous_const.mul ((continuous_traceP X).comp ?_)
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact (Continuous.matrix_elem continuous_subtype_val a b).mul continuous_const

def sumReI (a : Ainf X.B.I.F) : ℝ :=
  ∑ w : InfinitePlace X.B.I.F, (InfinitePlace.Completion.extensionEmbedding w (a w)).re

theorem sumReI_add (a b : Ainf X.B.I.F) : sumReI X (a + b) = sumReI X a + sumReI X b := by
  simp only [sumReI]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (a + b) w = a w + b w from rfl, map_add, Complex.add_re]

theorem continuous_sumReI : Continuous (sumReI X) :=
  continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding (v := w)).continuous.comp (continuous_apply w))

def betaH (x y : Wh X) : ℝ := sumReI X (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) ((hermCoord X).symm x) ((hermCoord X).symm y))

end Pair

def DensNu : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    νinf.map (hermCoord X) = ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j =>
      betaH X (stdOrthonormalBasis ℝ (Wh X) i) (stdOrthonormalBasis ℝ (Wh X) j)).det|) • volume

theorem densNu_holds : DensNu := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) := ⟨rfl⟩
  have hS := hP.2.2.1
  have hν : SelfDual νinf (fun S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) => psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)) := hP.2.2.2.2.2.1
  have h1 : ∀ x y : Wh X, (fun S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) => psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)) ((hermCoord X).symm x) ((hermCoord X).symm y) = ((𝐞 (betaH X x y) : Circle) : ℂ) := by
    intro x y
    simp only [betaH, sumReI]
    rw [psiInf_eq ψ hS, Real.fourierChar_apply]
    push_cast
    ring_nf
  have h2 : ∀ x x' y : Wh X, betaH X (x + x') y = betaH X x y + betaH X x' y := by
    intro x x' y
    simp only [betaH, hermCoord_symm_add, pairHerm_addL, sumReI_add]
  have h3 : ∀ x y y' : Wh X, betaH X x (y + y') = betaH X x y + betaH X x y' := by
    intro x y y'
    simp only [betaH, hermCoord_symm_add, pairHerm_addR, sumReI_add]
  have h4 : ∀ y : Wh X, Continuous fun x => betaH X x y := fun y =>
    (continuous_sumReI X).comp ((continuous_pairHerm_leftP X _).comp (hermCoord X).symm.continuous)
  have h6 : ∀ x y : Wh X, betaH X x y = betaH X y x := by
    intro x y
    simp only [betaH]
    rw [pairHerm_symm]
  have h5 : ∀ x : Wh X, Continuous fun y => betaH X x y := by
    intro x
    have e : (fun y => betaH X x y) = fun y => betaH X y x := funext fun y => h6 x y
    rw [e]
    exact h4 x
  exact PI.AprimeInfW.GenericDensity.dens_generic νinf (fun S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) => psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)) hν (hermCoord X) (hermCoord_add X) (betaH X) h1 h2 h3 h4 h5 h6
    (stdOrthonormalBasis ℝ (Wh X))

end PI.AprimeInfW

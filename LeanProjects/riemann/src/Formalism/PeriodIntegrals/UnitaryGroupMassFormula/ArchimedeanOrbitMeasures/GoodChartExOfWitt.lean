import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.StdConjExOfWitt

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S
open scoped TensorProduct Matrix

def WittLin : Prop := ∀ {n m k : ℕ}, n = m + k → ∀ (ε : Fin n → Bool) (w : Fin m → Fin n → ℂ),
    LinearIndependent ℂ w →
    (∀ z : Fin n → ℂ, z ≠ 0 → (∀ b, star (w b) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ z) = 0) →
      0 < (star z ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ z)).re) →
    ∃ (S : Finset (Fin n)) (c : Formalism.REAL.UJ ε), (S.card = k ∧ ∀ i ∈ S, ε i = true) ∧
      Submodule.span ℂ (Set.range fun b => uMat c⁻¹ *ᵥ w b) =
        Submodule.span ℂ ((fun i => (Pi.single i 1 : Fin n → ℂ)) '' (↑S)ᶜ)

def DimNK : Prop := ∀ {D : D7} (X : HidaSetting D), X.B.I.n = (D.R.rS + 1 + D.R.rS) + D.R.k

def LinIndW : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ v : InfinitePlace X.B.I.F, LinearIndependent ℂ (wV X u' v)

def PerpPosV : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ v : InfinitePlace X.B.I.F, ∀ z : Fin X.B.I.n → ℂ, z ≠ 0 →
      (∀ b, star (wV X u' v b) ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ z) = 0) →
      0 < (star z ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ z)).re

theorem dimNK_holds : DimNK := by
  intro D X
  rw [X.n_eq]
  have h1 := D.R.rS_two
  have h2 := D.R.r_eq
  omega

theorem gram_wV {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (b b' : Fin (D.R.rS + 1 + D.R.rS)) :
    star (wV X u' v b) ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ wV X u' v b') =
      X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) b b') := by
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hJ : ((X.B.I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (X.B.I.P v)⁻¹ = X.B.I.J.map (X.B.I.φ v) := by
    rw [← X.B.I.P_spec v]
    have e1 : ((X.B.I.P v)⁻¹)ᴴ * (X.B.I.P v)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hPu, Matrix.conjTranspose_one]
    calc ((X.B.I.P v)⁻¹)ᴴ * ((X.B.I.P v)ᴴ * X.B.I.J.map (X.B.I.φ v) * X.B.I.P v) * (X.B.I.P v)⁻¹
        = (((X.B.I.P v)⁻¹)ᴴ * (X.B.I.P v)ᴴ) * X.B.I.J.map (X.B.I.φ v) * (X.B.I.P v * (X.B.I.P v)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = X.B.I.J.map (X.B.I.φ v) := by
          rw [e1, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul, Matrix.mul_one]
  unfold wV
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hJ]
  have hσφ : ∀ a, X.B.I.φ v (X.B.I.cm.sig a) = star (X.B.I.φ v a) := fun a => X.B.I.cm.cmUnram.2.1 (X.B.I.φ v) a
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, gramE, hE, Formalism.UG.hform, map_sum, map_mul, Pi.star_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) (tupH (frameOf X u') b i) = X.B.I.cm.sig (tupH (frameOf X u') b i) from rfl,
    hσφ]
  ring

theorem linIndW_holds : LinIndW := by
  intro D X u' ψ hT μinf νinf fibInf hP v
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  set G : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) ℂ :=
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (X.B.I.φ v) with hG
  have hGd : G.det ≠ 0 := by
    have e : G.det = X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det :=
      (RingHom.map_det (X.B.I.φ v) _).symm
    rw [e]
    exact (map_ne_zero _).2 hd
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hGg : G *ᵥ g = 0 := by
    funext b'
    have h0 := congrArg (fun z => star (wV X u' v b') ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ z)) hg
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul,
      Matrix.mulVec_zero, dotProduct_zero] at h0
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← h0]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [gram_wV]
    simp only [hG, Matrix.map_apply]
    ring
  exact fun b => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hGd hGg) b

theorem wittBlock_of (h0 : DimNK) (h1 : LinIndW) (h2 : PerpPosV) (h3 : WittLin) : WittBlock := by
  intro D X u' ψ hT μinf νinf fibInf hP v
  exact h3 (h0 X) (X.B.I.ε v) (wV X u' v) (h1 X u' ψ hT μinf νinf fibInf hP v)
    (h2 X u' ψ hT μinf νinf fibInf hP v)

theorem goodChartEx_of_witt (h1 : LinIndW) (h2 : PerpPosV) (h3 : WittLin) (hG : GrpStd) (hT : TupStd) :
    GoodChartEx :=
  goodChartEx_of_std (stdDataEx_of (stdConjEx_of_witt (wittBlock_of dimNK_holds h1 h2 h3))) hG hT

end PI.AprimeInfW

import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.LatticeNormMatrixConj
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.IntAtEventually

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SwFinM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compV_apply (v : HeightOneSpectrum (𝓞 F)) (y : HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E) :
    compV v y = Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

section Tup

variable {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {n M : ℕ}

theorem mem_latV_iff (Y : Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :
    Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV (M := M) (n := n) bs v ↔ ∀ a i, Y a i ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v := Iff.rfl

theorem mul_mem_latV {σ : E →ₐ[F] E} (h : PositivityTheory.SiegelWeilFormula.Gunr.IntAt v (PositivityTheory.SiegelWeilFormula.Gunr.basisSet σ bs))
    (X : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (hX : ∀ i j, X i j ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v)
    (Y : Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) (hY : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV (M := M) (n := n) bs v) :
    (HMul.hMul (α := Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
      (β := Matrix (Fin n) (Fin M) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) X Y : Fin n → Fin M → _) ∈
      HeckeCharacterZeroLocus.SiegelWeilU.latV (M := M) (n := n) bs v := by
  have hY' := (mem_latV_iff Y).1 hY
  refine (mem_latV_iff _).2 fun j i => ?_
  have e : (HMul.hMul (α := Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
      (β := Matrix (Fin n) (Fin M) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) X Y) j i = ∑ c, X j c * Y c i := rfl
  rw [e]
  have hs : (∑ c, X j c * Y c i) ∈ GlobalTheory.CompanionTheory.RvRingPf.ringOf h :=
    Subring.sum_mem _ fun c _ => Subring.mul_mem _ ((mem_ringOf h _).2 (hX j c)) ((mem_ringOf h _).2 (hY' c i))
  exact (mem_ringOf h _).1 hs

def lmulHomeo (X Xi : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (h1 : X * Xi = 1) (h2 : Xi * X = 1) :
    (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) ≃ₜ (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) where
  toFun Y := (HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) X Y : Matrix (Fin n) (Fin M) _)
  invFun Y := (HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) Xi Y : Matrix (Fin n) (Fin M) _)
  left_inv Y := by
    show HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) Xi
      (HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) X Y) = Y
    exact (Matrix.mul_assoc Xi X (Matrix.of Y)).symm.trans
      (by rw [h2, Matrix.one_mul] : (Xi * X) * Matrix.of Y = Matrix.of Y)
  right_inv Y := by
    show HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) X
      (HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) Xi Y) = Y
    exact (Matrix.mul_assoc X Xi (Matrix.of Y)).symm.trans
      (by rw [h1, Matrix.one_mul] : (X * Xi) * Matrix.of Y = Matrix.of Y)
  continuous_toFun := continuous_const.matrix_mul continuous_id
  continuous_invFun := continuous_const.matrix_mul continuous_id

end Tup

section Parts

variable {n M : ℕ}

theorem projV_lmul (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E))
    (X : Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) :
    HeckeCharacterZeroLocus.SiegelWeilU.projV v (fun j i => ∑ c, Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (A c j) * X c i) =
      fun j i => ∑ c, PositivityTheory.SiegelWeilFormula.Gen.matV v A c j * HeckeCharacterZeroLocus.SiegelWeilU.projV v X c i := by
  funext j i
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.projV, map_sum, map_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  exact (compV_apply v (A c j)).symm

theorem finPart_mul (x : Matrix (Fin M) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E))
    (A : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    (fun i j => Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) ((x * A) i j)) =
      fun i j => ∑ c, Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (A c j) *
        Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (x i c) := by
  funext i j
  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, mul_comm]

end Parts

end GlobalTheory.CompanionTheory.SwFinM

end

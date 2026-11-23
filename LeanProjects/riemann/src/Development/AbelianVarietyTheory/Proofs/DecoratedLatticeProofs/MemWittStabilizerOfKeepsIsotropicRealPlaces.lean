import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG

noncomputable section

namespace GlobalTheory.Core.Rk.IwGlob

open GlobalTheory.MixModel
open scoped TensorProduct

theorem tens_prod_ext {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] {z z' : (A × B) ⊗[F] E}
    (a : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z')
    (b : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z') : z = z' := by
  have hz : ∀ z : (A × B) ⊗[F] E, z = LinearMap.rTensor E (LinearMap.inl F A B)
        (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F A B)
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul x y => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [hz z, hz z', a, b]

theorem adTens_ext {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {z z' : AF F ⊗[F] E}
    (h1 : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.compInf F E w z = GlobalTheory.AdelicU.compInf F E w z')
    (h2 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z') : z = z' := by
  refine tens_prod_ext (A := Ainf F) (B := Af F) (GlobalTheory.AutFunCompare.infTens_ext fun w => ?_) h2
  have e : ∀ y : AF F ⊗[F] E, Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) y) =
      GlobalTheory.AdelicU.compInf F E w y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => erw [map_zero]
    | tmul a x => rfl
    | add x y hx hy => erw [map_add, map_add, map_add, hx, hy]
  rw [e, e]
  exact h1 w

theorem map_mul_eq_of_keeps {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (X : Matrix (Fin n) (Fin r) A) (P : Matrix (Fin r) (Fin n) A)
    (hPX : P * X = 1) (β : Matrix (Fin r) (Fin r) R) (h : M.map φ * X.map φ = X.map φ * β) :
    (M * X).map φ = (X * (P * M * X)).map φ := by
  have hPX' : P.map φ * X.map φ = 1 := by
    rw [← Matrix.map_mul, hPX, Matrix.map_one _ (map_zero φ) (map_one φ)]
  simp only [Matrix.map_mul]
  rw [h, Matrix.mul_assoc (P.map φ), h, ← Matrix.mul_assoc (P.map φ), hPX', Matrix.one_mul]

theorem mat_projArch {D : D7} {T : HSp D} (q : GA D T) (w : InfinitePlace D.host.F) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram (GlobalTheory.AdelicU.projArch D.sp.cm.sig T.gram w q)).1 =
                 (Formalism.L2.Theta.mt T q).map (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) :=
  Matrix.ext fun _ _ => rfl

theorem mt_inv_mul_self {D : D7} {T : HSp D} (q : GA D T) :
    Formalism.L2.Theta.mt T q⁻¹ * Formalism.L2.Theta.mt T q = 1 := by
  show (Formalism.L2.Theta.matHom T q⁻¹).1 * (Formalism.L2.Theta.matHom T q).1 = 1
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem keeps_map {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (w : InfinitePlace D.host.F)
    (β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E))
    (h : (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) :
    (Formalism.L2.Theta.mt T q).map (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) * Matrix.map d.jX (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) =
      Matrix.map d.jX (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) * β := by
  rw [← mat_projArch q w]
  exact h

theorem arch_comp {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (w : InfinitePlace D.host.F)
    (β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E))
    (h : (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β)
    (i : Fin T.rank) (j : Fin r) :
    GlobalTheory.AdelicU.compInf D.host.F D.host.E w ((Formalism.L2.Theta.mt T q ⬝ d.jX) i j) =
      GlobalTheory.AdelicU.compInf D.host.F D.host.E w ((d.jX ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX)) i j) := by
  have h2 := keeps_map d q w β h
  have h3 := map_mul_eq_of_keeps (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (Formalism.L2.Theta.mt T q) d.jX d.pX
    d.pX_jX β h2
  rw [← Matrix.map_apply (f := GlobalTheory.AdelicU.compInf D.host.F D.host.E w), h3]
  rfl

theorem mul_jX_eq {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (hq : q ∈ GinfC T)
    (hw : ∀ w : InfinitePlace D.host.F, ∃ β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E), (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) :
    Formalism.L2.Theta.mt T q ⬝ d.jX = d.jX ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX) := by
  let φf : AE D →+* Af D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hf : (Formalism.L2.Theta.mt T q).map φf = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hq)
  have hfin := map_mul_eq_of_keeps φf (Formalism.L2.Theta.mt T q) d.jX d.pX d.pX_jX 1
    (by rw [hf, Matrix.one_mul, Matrix.mul_one])
  funext i j
  exact adTens_ext (F := D.host.F) (E := D.host.E) (fun w => Exists.elim (hw w) fun β hβ => arch_comp d q w β hβ i j)
    (congrFun (congrFun hfin i) j)

theorem mem_stab_of_keeps : ∀ {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T), q ∈ GinfC T → (∀ w : InfinitePlace D.host.F, ∃ β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E), (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) → q ∈ stab d := by
  intro D T T₀ r d q hq hw
  have hPX : d.pX ⬝ d.jX = 1 := d.pX_jX
  have key := mul_jX_eq d q hq hw
  have hinv : Formalism.L2.Theta.mt T q⁻¹ ⬝ Formalism.L2.Theta.mt T q = 1 := mt_inv_mul_self q
  have h1 : (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹ ⬝ d.jX) ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX) = 1 := by
    calc (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹ ⬝ d.jX) ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX)
        = (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹) ⬝ (d.jX ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX)) := by
          rw [Matrix.mul_assoc]
      _ = (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹) ⬝ (Formalism.L2.Theta.mt T q ⬝ d.jX) := by rw [← key]
      _ = d.pX ⬝ ((Formalism.L2.Theta.mt T q⁻¹ ⬝ Formalism.L2.Theta.mt T q) ⬝ d.jX) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hinv, Matrix.one_mul, hPX]
  exact ⟨⟨_, _, mul_eq_one_comm.mp h1, h1⟩, key⟩

end GlobalTheory.Core.Rk.IwGlob

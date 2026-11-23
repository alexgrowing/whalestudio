import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CharpolyEqOfIsNilpotentSub
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFrobSSWdRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitOfStableLine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section

open Polynomial Module

namespace GlobalTheory.Pst.TwistLetters

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {L : FinExt l}
  (V : Type) [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]

def smulEnd : (Fin 1 → ↥L.1) →ₗ[ℚ_[l]] End ℚ_[l] V where
  toFun v' := ((LinearMap.lsmul ↥L.1 V) (v' 0)).restrictScalars ℚ_[l]
  map_add' x y := by ext v; simp [add_smul]
  map_smul' c x := by ext v; simp [smul_assoc]

def mulB : ((Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) →ₗ[ℚ_[l]] End ℚ_[l] (V ⊗[ℚ_[l]] Bst P) :=
  TensorProduct.lift ((TensorProduct.mapBilinear (RingHom.id ℚ_[l]) V (Bst P) V (Bst P)).compl₁₂ (smulEnd V)
    (LinearMap.mul ℚ_[l] (Bst P)))

@[simp] theorem mulB_tmul (v' : Fin 1 → ↥L.1) (b' : Bst P) (v : V) (b : Bst P) :
    mulB P V (v' ⊗ₜ b') (v ⊗ₜ b) = (v' 0 • v) ⊗ₜ (b' * b) := by
  simp [mulB, smulEnd]

variable {P V}

theorem mulB_smul (a : ↥L.1) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB P V y (a • x) = a • mulB P V y x := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [TensorProduct.smul_tmul', mulB_tmul, mulB_tmul, TensorProduct.smul_tmul', smul_smul, smul_smul, mul_comm]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulB_smul_left (a : ↥L.1) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB P V (a • y) x = a • mulB P V y x := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [TensorProduct.smul_tmul', mulB_tmul, mulB_tmul, TensorProduct.smul_tmul', Pi.smul_apply, smul_eq_mul, mul_smul]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulB_mulV (c : ↥(MaximalUnramifiedExtension l)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB P V y (mulV P ↥L.1 V c x) = mulV P ↥L.1 V c (mulB P V y x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulV_tmul, mulB_tmul, mulB_tmul, mulV_tmul, mul_left_comm]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulV_mulB (c : ↥(MaximalUnramifiedExtension l)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB P V (mulV P ↥L.1 (Fin 1 → ↥L.1) c y) x = mulV P ↥L.1 V c (mulB P V y x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulV_tmul, mulB_tmul, mulB_tmul, mulV_tmul, mul_assoc]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem phiV_mulB (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    phiV P ↥L.1 V (mulB P V y x) = mulB P V (phiV P ↥L.1 (Fin 1 → ↥L.1) y) (phiV P ↥L.1 V x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulB_tmul, phiV_tmul, phiV_tmul, phiV_tmul, mulB_tmul, map_mul]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem monV_mulB (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    monV P ↥L.1 V (mulB P V y x) = mulB P V (monV P ↥L.1 (Fin 1 → ↥L.1) y) x +
      mulB P V y (monV P ↥L.1 V x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulB_tmul, monV_tmul, monV_tmul, monV_tmul, mulB_tmul, mulB_tmul, ← TensorProduct.tmul_add]
      congr 1
      simp only [monSt_apply, derivative_mul]
      ring
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, smul_add, hy, hy'] <;> abel

variable {K : FinExt l} (ρs ρt : Representation ↥L.1 ↥(GK K) V)
  (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1)

theorem stRep_mulB (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) (g : ↥(GK K))
    (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    stRep P ρt g (mulB P V y x) = mulB P V (stRep P ρm g y) (stRep P ρs g x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulB_tmul, stRep_tmul, stRep_tmul, stRep_tmul, mulB_tmul, map_mul, ht, hm, map_smul, Pi.smul_apply,
        smul_eq_mul, smul_smul, mul_smul]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulB_mem_Dpst (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v)
    {x : V ⊗[ℚ_[l]] Bst P} {y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P} (hx : x ∈ Dpst P ρs) (hy : y ∈ Dpst P ρm) :
    mulB P V y x ∈ Dpst P ρt := by
  obtain ⟨K₁, h₁⟩ := (mem_Dpst P ρs).mp hx
  obtain ⟨K₂, h₂⟩ := (mem_Dpst P ρm).mp hy
  refine (mem_Dpst P ρt).mpr ⟨supExt K₁ K₂, fun g hg => ?_⟩
  rw [stRep_mulB ρs ρt ρm χ hm ht, h₁ g (GK_le (K' := supExt K₁ K₂) le_sup_left hg),
    h₂ g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)]

variable (P)

def dmul (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) :
    ↥(Dpst P ρs) →ₗ[↥L.1] ↥(Dpst P ρm) →ₗ[↥L.1] ↥(Dpst P ρt) :=
  LinearMap.mk₂ ↥L.1 (fun x y => ⟨mulB P V y.1 x.1, mulB_mem_Dpst ρs ρt ρm χ hm ht x.2 y.2⟩)
    (fun x x' y => Subtype.ext (by simp))
    (fun a x y => Subtype.ext (by simp [mulB_smul]))
    (fun x y y' => Subtype.ext (by simp))
    (fun a x y => Subtype.ext (by simp [mulB_smul_left]))

variable (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v)

@[simp] theorem coe_dmul (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    (dmul P ρs ρt ρm χ hm ht x y : V ⊗[ℚ_[l]] Bst P) = mulB P V y.1 x.1 := rfl

theorem dmul_mulD_left (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    dmul P ρs ρt ρm χ hm ht (mulD P ρs c x) y = mulD P ρt c (dmul P ρs ρt ρm χ hm ht x y) :=
  Subtype.ext (by simp [mulB_mulV])

theorem dmul_mulD_right (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    dmul P ρs ρt ρm χ hm ht x (mulD P ρm c y) = mulD P ρt c (dmul P ρs ρt ρm χ hm ht x y) :=
  Subtype.ext (by simp [mulV_mulB])

theorem phiD_dmul (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    phiD P ρt (dmul P ρs ρt ρm χ hm ht x y) = dmul P ρs ρt ρm χ hm ht (phiD P ρs x) (phiD P ρm y) :=
  Subtype.ext (by simp [phiV_mulB])

theorem monD_dmul (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    monD P ρt (dmul P ρs ρt ρm χ hm ht x y) =
      dmul P ρs ρt ρm χ hm ht (monD P ρs x) y + dmul P ρs ρt ρm χ hm ht x (monD P ρm y) :=
  Subtype.ext (by simp [monV_mulB, add_comm])

theorem actD_dmul (g : ↥(GK K)) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    actD P ρt g (dmul P ρs ρt ρm χ hm ht x y) = dmul P ρs ρt ρm χ hm ht (actD P ρs g x) (actD P ρm g y) :=
  Subtype.ext (by simp [stRep_mulB ρs ρt ρm χ hm ht])

end GlobalTheory.Pst.TwistLetters

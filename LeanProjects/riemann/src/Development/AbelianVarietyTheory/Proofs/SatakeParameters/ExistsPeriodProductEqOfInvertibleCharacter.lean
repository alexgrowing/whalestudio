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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DmulMulDRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbedding
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters

noncomputable section

namespace GlobalTheory.Pst.TwistLetters.Invert

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {L : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]

theorem mulB_assoc (y y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (w : V ⊗[ℚ_[l]] Bst P) :
    mulB P V y (mulB P V y' w) = mulB P V (mulB P (Fin 1 → ↥L.1) y y') w := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul v c =>
        rw [mulB_tmul, mulB_tmul, mulB_tmul, mulB_tmul, Pi.smul_apply, smul_eq_mul, mul_smul, mul_assoc]
      | add w w' hw hw' => simp only [map_add, hw, hw']
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']

theorem mulB_comm (y y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    mulB P (Fin 1 → ↥L.1) y y' = mulB P (Fin 1 → ↥L.1) y' y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      rw [mulB_tmul, mulB_tmul, mul_comm b b']
      congr 1
      funext i
      rw [Subsingleton.elim i 0]
      simp [mul_comm]
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']

theorem one_mulB (w : V ⊗[ℚ_[l]] Bst P) :
    mulB P V ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P)) w = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => rw [mulB_tmul, one_smul, one_mul]
  | add w w' hw hw' => simp only [map_add, hw, hw']

variable {K : FinExt l}

theorem stRep_twist (ρs ρt : Representation ↥L.1 ↥(GK K) V) (χ : ↥(GK K) → ↥L.1)
    (ht : ∀ g v, ρt g v = χ g • ρs g v) (g : ↥(GK K)) (w : V ⊗[ℚ_[l]] Bst P) :
    stRep P ρt g w = χ g • stRep P ρs g w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => rw [stRep_tmul, stRep_tmul, ht, TensorProduct.smul_tmul']
  | add w w' hw hw' => simp only [map_add, smul_add, hw, hw']

theorem stRep_trivial_one (g : ↥(GK K)) :
    stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P)) =
      (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) := by
  rw [stRep_tmul, map_one]
  rfl

end GlobalTheory.Pst.TwistLetters.Invert

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
open GlobalTheory.Pst.TwistLetters.Invert in

theorem GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V) (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1) (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) (y : ↥(Dpst P ρm)) (y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P), GlobalTheory.Pst.TwistLetters.mulB P (Fin 1 → ↥L.1) y' (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) → ∀ z : ↥(Dpst P ρt), ∃ x : ↥(Dpst P ρs), GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht x y = z := by
  intro l _ P K L V _ _ _ _ ρs ρt ρm χ hm ht y y' hinv z
  have hmτ : ∀ g w, stRep P ρm g w =
      χ g • stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g w :=
    stRep_twist _ ρm χ (fun g v => by rw [hm]; rfl)
  have hτmul : ∀ g (a w : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P),
      stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g (mulB P (Fin 1 → ↥L.1) a w) =
        mulB P (Fin 1 → ↥L.1) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g a)
          (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g w) := fun g a w =>
    stRep_mulB _ _ _ (fun _ => (1 : ↥L.1)) (fun _ _ => by rw [one_smul]; rfl)
      (fun _ _ => by rw [one_smul]) g a w
  have hsmul : ∀ g (a : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (w : V ⊗[ℚ_[l]] Bst P),
      stRep P ρs g (mulB P V a w) =
        mulB P V (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g a) (stRep P ρs g w) :=
    fun g a w => stRep_mulB ρs ρs _ (fun _ => (1 : ↥L.1)) (fun _ _ => by rw [one_smul]; rfl)
      (fun _ _ => by rw [one_smul]) g a w
  have hτe := stRep_trivial_one (P := P) (L := L) (K := K)
  have hone : ∀ w : V ⊗[ℚ_[l]] Bst P, mulB P V ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P)) w = w := one_mulB
  have hone' : ∀ w : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P,
      mulB P (Fin 1 → ↥L.1) ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P)) w = w := one_mulB
  have hχ : ∀ g, χ g ≠ 0 := by
    intro g h0
    have h1 : ρm (g⁻¹ * g) (fun _ => (1 : ↥L.1)) = fun _ => 1 := by simp
    rw [map_mul, Module.End.mul_apply, hm, hm, h0] at h1
    have := congrFun h1 0
    simp at this
  have hcomm1 : ∀ a : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P, mulB P (Fin 1 → ↥L.1) a ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = a := fun a => by
    rw [mulB_comm, hone']
  obtain ⟨K₁, h₁⟩ := (mem_Dpst P ρm).mp y.2
  obtain ⟨K₂, h₂⟩ := (mem_Dpst P ρt).mp z.2
  have hx : mulB P V y' (z : V ⊗[ℚ_[l]] Bst P) ∈ Dpst P ρs := by
    refine (mem_Dpst P ρs).mpr ⟨supExt K₁ K₂, fun g hg => ?_⟩
    have hy := h₁ g (GK_le (K' := supExt K₁ K₂) le_sup_left hg)
    have hz := h₂ g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)
    have hc := hχ g
    have hτy : stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = (χ g)⁻¹ • (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) := by
      rw [hmτ] at hy
      conv_rhs => rw [← hy]
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hprod : mulB P (Fin 1 → ↥L.1) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y') (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = χ g • ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) := by
      have h3 := congrArg (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g) hinv
      rw [hτmul, hτy, hτe, mulB_smul] at h3
      rw [← h3, smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hτy' : stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y' = χ g • y' := by
      calc stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y' = mulB P (Fin 1 → ↥L.1) ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y') := by rw [hone']
        _ = mulB P (Fin 1 → ↥L.1) (mulB P (Fin 1 → ↥L.1) y' (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y') := by rw [hinv]
        _ = mulB P (Fin 1 → ↥L.1) y' (mulB P (Fin 1 → ↥L.1) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y') (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)) := by
          rw [← mulB_assoc, mulB_comm (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)]
        _ = χ g • y' := by rw [hprod, mulB_smul, hcomm1]
    have hsz : stRep P ρs g (z : V ⊗[ℚ_[l]] Bst P) = (χ g)⁻¹ • (z : V ⊗[ℚ_[l]] Bst P) := by
      rw [stRep_twist ρs ρt χ ht] at hz
      conv_rhs => rw [← hz]
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hsmul, hτy', hsz, mulB_smul, mulB_smul_left, smul_smul, inv_mul_cancel₀ hc, one_smul]
  refine ⟨⟨_, hx⟩, Subtype.ext ?_⟩
  rw [coe_dmul, mulB_assoc, mulB_comm, hinv, hone]

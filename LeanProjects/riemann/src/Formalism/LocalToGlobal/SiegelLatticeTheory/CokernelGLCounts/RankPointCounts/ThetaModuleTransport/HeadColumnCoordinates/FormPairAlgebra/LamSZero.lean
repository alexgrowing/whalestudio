import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.LamSMulVec
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.BRawHeadColsRight

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def kap (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) : E := (Z.map O.subtype)⁻¹ (Fin.last r) (Fin.last r)

def EtaNZD (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (T T' : E) : Prop :=
  ∀ u : E, (1 - T * T' * (kap O Z * cj (kap O Z))) * u = 0 → u = 0

theorem lamL_e' (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) :
    lamL O Z (Pi.single (Fin.last r) 1) = kap O Z := by
  simp only [lamL, LinearMap.coe_mk, AddHom.coe_mk, lamC, kap, Matrix.mulVec, dotProduct, Pi.single_apply]
  simp [apply_ite (fun x : O => (x : E)), mul_ite, Finset.sum_ite_eq']

theorem lamS_e' (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) :
    lamS O cj Z (Pi.single (Fin.last r) 1) = cj (kap O Z) := by
  simp only [lamS, lamStarC, kap, Matrix.mulVec, dotProduct, Pi.single_apply]
  simp [apply_ite (fun x : O => (x : E)), mul_ite, Finset.sum_ite_eq']

theorem lamS_smul (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (c : O) (v : Fin (r + 1) → O) :
    lamS O cj Z (c • v) = (c : E) * lamS O cj Z v := by
  simp [lamS, lamStarC, Matrix.mulVec, dotProduct, Finset.mul_sum, Subring.smul_def, mul_left_comm, map_mul]

theorem lamS_zero (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) : lamS O cj Z 0 = 0 := by
  simp [lamS, lamStarC]

def elimL : (Fin (r + 1) → O) →ₗ[O] (Ix r → O) where
  toFun y := Sum.elim y 0
  map_add' a b := by funext i; rcases i with i | i <;> simp
  map_smul' c a := by funext i; rcases i with i | i <;> simp

def elimR : (Fin (r + 1) → O) →ₗ[O] (Ix r → O) where
  toFun y := Sum.elim 0 y
  map_add' a b := by funext i; rcases i with i | i <;> simp
  map_smul' c a := by funext i; rcases i with i | i <;> simp

variable (hO : ∀ x ∈ O, cj x ∈ O)
include hO

theorem elimL_mem (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (t t' : O) (k : Fin (r + 1) → O)
    (hk : k ∈ headCols Z) : elimL O k ∈ relC O cj (Z.map O.subtype) t t' := by
  obtain ⟨w, hw, rfl⟩ := (mem_headCols_iff Z k).1 hk
  rw [mem_relC_iff O cj hO]
  refine ⟨0, w, ?_, ?_⟩
  · funext j; simp [elimL]
  · funext j; simp [elimL, hw]

theorem elimR_mem (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (t t' : O) (k : Fin (r + 1) → O)
    (hk : k ∈ headCols (cjT O cj hO Z)) : elimR O k ∈ relC O cj (Z.map O.subtype) t t' := by
  obtain ⟨w, hw, rfl⟩ := (mem_headCols_iff _ k).1 hk
  rw [mem_relC_iff O cj hO]
  refine ⟨w, 0, ?_, ?_⟩
  · funext j; simp [elimR, hw]
  · funext j; simp [elimR]

def iL (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (t t' : O) :
    MbMod Z →ₗ[O] (Ix r → O) ⧸ relC O cj (Z.map O.subtype) t t' :=
  (headCols Z).liftQ ((relC O cj (Z.map O.subtype) t t').mkQ ∘ₗ elimL O) (fun k hk => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact elimL_mem O cj hO Z t t' k hk)

def iR (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (t t' : O) :
    MbMod (cjT O cj hO Z) →ₗ[O] (Ix r → O) ⧸ relC O cj (Z.map O.subtype) t t' :=
  (headCols (cjT O cj hO Z)).liftQ ((relC O cj (Z.map O.subtype) t t').mkQ ∘ₗ elimR O) (fun k hk => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact elimR_mem O cj hO Z t t' k hk)

theorem iL_mk (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (t t' : O) (y : Fin (r + 1) → O) :
    iL O cj hO Z t t' (Submodule.Quotient.mk y) = Submodule.Quotient.mk (Sum.elim y 0) := rfl

theorem iR_mk (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (t t' : O) (y : Fin (r + 1) → O) :
    iR O cj hO Z t t' (Submodule.Quotient.mk y) = Submodule.Quotient.mk (Sum.elim (0 : Fin (r + 1) → O) y) := rfl

theorem mk_elim (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (t t' : O) (y y' : Fin (r + 1) → O) :
    (Submodule.Quotient.mk (Sum.elim y y') : (Ix r → O) ⧸ relC O cj (Z.map O.subtype) t t') =
      iL O cj hO Z t t' (Submodule.Quotient.mk y) + iR O cj hO Z t t' (Submodule.Quotient.mk y') := by
  rw [iL_mk, iR_mk, ← Submodule.Quotient.mk_add]
  congr 1
  funext i
  rcases i with i | i <;> simp

theorem ker_zero (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det) (t t' : O)
    (hη : EtaNZD O cj Z t t') (a a' : Fin (r + 1) → O)
    (h : (Submodule.Quotient.mk (Sum.elim a a') : (Ix r → O) ⧸ relC O cj (Z.map O.subtype) t t') = 0)
    (hl : lamL O Z a = 0) (hl' : lamS O cj Z a' = 0) :
    (Submodule.Quotient.mk a : MbMod Z) = 0 ∧ (Submodule.Quotient.mk a' : MbMod (cjT O cj hO Z)) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, mem_relC_iff O cj hO Z t t'] at h
  obtain ⟨c₁, c₂, h₁, h₂⟩ := h
  have ha : a = Z.mulVec c₂ - (t * c₁ (Fin.last r)) • Pi.single (Fin.last r) 1 := h₁
  have ha' : a' = (cjT O cj hO Z).mulVec c₁ - (t' * c₂ (Fin.last r)) • Pi.single (Fin.last r) 1 := h₂
  have e1 : lamL O Z a = (c₂ (Fin.last r) : E) - (t : E) * (c₁ (Fin.last r) : E) * kap O Z := by
    rw [ha, map_sub, map_smul, lamL_mulVec O Z hu, lamL_e', Subring.smul_def, smul_eq_mul]
    push_cast; ring
  have e2 : lamS O cj Z a' = (c₁ (Fin.last r) : E) - (t' : E) * (c₂ (Fin.last r) : E) * cj (kap O Z) := by
    rw [ha', lamS_sub, lamS_smul, lamS_mulVec O cj Z hO hu, lamS_e']
    push_cast; ring
  rw [e1] at hl
  rw [e2] at hl'
  have h0 : (c₁ (Fin.last r) : E) = 0 := by
    apply hη
    linear_combination hl' + (t' : E) * cj (kap O Z) * hl
  have h0' : (c₂ (Fin.last r) : E) = 0 := by
    linear_combination hl + (t : E) * kap O Z * h0
  have z1 : c₁ (Fin.last r) = 0 := Subtype.ext h0
  have z2 : c₂ (Fin.last r) = 0 := Subtype.ext h0'
  constructor
  · rw [ha, z1, mul_zero, zero_smul, sub_zero, mk_mulVec, z2, zero_smul]
  · rw [ha', z2, mul_zero, zero_smul, sub_zero, mk_mulVec, z1, zero_smul]

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

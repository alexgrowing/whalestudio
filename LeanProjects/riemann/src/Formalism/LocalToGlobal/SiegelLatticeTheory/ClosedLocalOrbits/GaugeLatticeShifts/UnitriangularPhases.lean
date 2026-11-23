import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.UnitriangularPhases

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Formalism.L2.SG.Pf

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def epsConj (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  fun c b => (-1) ^ (r - c.val) * M c b * (-1) ^ (r - b.val)

theorem zhatOM_mul (A Z M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    ZhatOM (A * Z * M) = A * ZhatOM Z * epsConj M := by
  ext a b
  simp only [ZhatOM, epsConj, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  have h : ((-1 : E) ^ (r - c.val)) * (-1) ^ (r - c.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination (-(A a d * Z d c * M c b * (-1 : E) ^ (r - b.val))) * h

theorem isUpUni_epsConj {M : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : IsUpUni M) : IsUpUni (epsConj M) := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · simp only [epsConj]; rw [(h i j).1 hij]; ring
  · subst hij
    simp only [epsConj]
    rw [(h i i).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]
    simp

theorem sgUp_epsConj (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : sgUp (epsConj M) = -sgUp M := by
  unfold sgUp
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · simp only [epsConj]
    have e : r - a.val = (r - (a.val + 1)) + 1 := by omega
    rw [e, pow_succ]
    have hsq : ((-1 : E) ^ (r - (a.val + 1))) * (-1) ^ (r - (a.val + 1)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    linear_combination (-(M a ⟨a.val + 1, h⟩)) * hsq
  · simp

theorem isLoUni_conjT {M : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : IsUpUni M) : IsLoUni M.conjTranspose := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.conjTranspose_apply, (h j i).1 hij, star_zero]
  · subst hij; rw [Matrix.conjTranspose_apply, (h i i).2 rfl, star_one]

theorem sgLo_conjT (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : sgLo M.conjTranspose = star (sgUp M) := by
  unfold sgLo sgUp
  rw [star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rfl
  · simp

theorem zhat_nm (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (Fs F2 : LFlag S r T')
    {n m : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ Fs) (hF2 : ∀ b, frame F2 b = n (m (frame Fs b))) :
    ∃ vn um : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni vn ∧ IsUpUni um ∧
      (∀ b, n⁻¹ (frame F b) = ∑ c, vn c b • frame F c) ∧ (∀ b, m (frame Fs b) = ∑ c, um c b • frame Fs c) ∧
      ZhatL F F2 = vn.conjTranspose * ZhatL F Fs * um := by
  have hni := Formalism.L2.SG.Pf.nlam_inv hn
  obtain ⟨vn, hvn, hvnF⟩ := nlam_frame Λ F hni
  obtain ⟨um, hum, humF⟩ := nlam_frame Λ Fs hm
  refine ⟨vn, um, hvn, hum, hvnF, humF, ?_⟩
  ext a b
  have hiso : ∀ x y, S.hT (n⁻¹ x) (n⁻¹ y) = S.hT x y := hni.1.1
  have hnn : ∀ y, n⁻¹ (n y) = y := fun y => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  have lhs : ZhatL F F2 a b = S.hT (frame F a) (frame F2 b) := rfl
  rw [lhs, hF2, ← hiso, hnn, hvnF, humF]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [show ∀ x y, ZhatL F Fs x y = S.hT (frame F x) (frame Fs y) from fun _ _ => rfl, starRingEnd_apply,
    RingHom.id_apply]
  ring

theorem phase_move (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (Fs F2 : LFlag S r T')
    {n m : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ Fs) (hF2 : ∀ b, frame F2 b = n (m (frame Fs b)))
    (w : Point E (r + 1)) {Ls Us L2 U2 : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hLs : IsLoUni Ls) (hUs : IsUpUni Us)
    (hL2 : IsLoUni L2) (hU2 : IsUpUni U2) (hs : ZhatOM (ZhatL F Fs) = Ls * ptMat w * Us)
    (h2 : ZhatOM (ZhatL F F2) = L2 * ptMat w * U2) :
    ∃ vn um : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni vn ∧ IsUpUni um ∧
      (∀ b, n⁻¹ (frame F b) = ∑ c, vn c b • frame F c) ∧ (∀ b, m (frame Fs b) = ∑ c, um c b • frame Fs c) ∧
      sgLo L2 + sgUp U2 = sgLo Ls + sgUp Us + star (sgUp vn) - sgUp um := by
  obtain ⟨vn, um, hvn, hum, hvF, humF, hZ⟩ := zhat_nm Λ F Fs F2 hn hm hF2
  refine ⟨vn, um, hvn, hum, hvF, humF, ?_⟩
  have e : (vn.conjTranspose * Ls) * ptMat w * (Us * epsConj um) = L2 * ptMat w * U2 := by
    rw [← h2, hZ, zhatOM_mul, hs]; simp only [Matrix.mul_assoc]
  have hds := simple_decomposition_holds E (r + 1) w _ _ _ _
    (Formalism.MainNotions.BridgeLemma.bru_lo_mul (isLoUni_conjT hvn) hLs) (Formalism.MainNotions.BridgeLemma.bru_up_mul hUs (isUpUni_epsConj hum))
    hL2 hU2 e
  rw [sgLo_mul (isLoUni_conjT hvn) hLs, sgUp_mul hUs (isUpUni_epsConj hum), sgLo_conjT, sgUp_epsConj] at hds
  linear_combination -hds

end Gen

end Formalism.L2.SG.Pf.UnitriangularPhases

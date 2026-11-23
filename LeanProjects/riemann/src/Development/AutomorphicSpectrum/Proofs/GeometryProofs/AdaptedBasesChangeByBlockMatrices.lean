import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem det_eq_det_mul_det_of_block {K : Type} [Field K] {p q : ℕ} (M : Matrix (Fin (p + q)) (Fin (p + q)) K)
    (P : Matrix (Fin p) (Fin p) K) (D : Matrix (Fin q) (Fin q) K)
    (h11 : ∀ i k, M (Fin.castAdd q i) (Fin.castAdd q k) = P i k)
    (h21 : ∀ j k, M (Fin.natAdd p j) (Fin.castAdd q k) = 0)
    (h22 : ∀ j l, M (Fin.natAdd p j) (Fin.natAdd p l) = D j l) : M.det = P.det * D.det := by
  have hM : M.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks P (Matrix.of fun i l => M (Fin.castAdd q i) (Fin.natAdd p l)) 0 D := by
    ext a b
    rcases a with i | j <;> rcases b with k | l
    · simp [h11]
    · simp
    · simp [h21]
    · simp [h22]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, hM, Matrix.det_fromBlocks_zero₂₁]

theorem exists_det_mul_eq_of_isAdapted
    (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [AddCommGroup W] [Module K W]
    (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (σ : E →+* K) (p q : ℕ) (v v' : Fin p → W) (w w' : Fin q → W)
    (u u' : Fin (p + q) → W × Module.Dual K W) (P : Matrix (Fin p) (Fin p) K) (Q : Matrix (Fin q) (Fin q) K) :
    IsAdapted ρH σ v w u → IsAdapted ρH σ v' w' u' → LinearIndependent K v →
    Submodule.span K (Set.range u) = HT.eigSp ρH σ →
    (∀ i, v' i = ∑ k, P i k • v k) → (∀ i, w' i = ∑ k, Q i k • w k) →
    ∃ B : Matrix (Fin (p + q)) (Fin (p + q)) K, (∀ i, u' i = ∑ k, B i k • u k) ∧ B.det * Q.det = P.det := by
  intro h h' hv hspan hP hQ
  obtain ⟨-, h1, h2⟩ := h
  obtain ⟨he', h1', h2'⟩ := h'
  have hex : ∀ i, ∃ c : Fin (p + q) → K, ∑ k, c k • u k = u' i := fun i => by
    rw [← Submodule.mem_span_range_iff_exists_fun, hspan]
    exact he' i
  choose B hB using hex
  let M : Matrix (Fin (p + q)) (Fin (p + q)) K := Matrix.of B
  have hMB : ∀ i k, M i k = B i k := fun _ _ => rfl
  refine ⟨M, fun i => (hB i).symm, ?_⟩
  have hfst : ∀ i, (u' i).1 = ∑ k : Fin p, M i (Fin.castAdd q k) • v k := fun i => by
    rw [← hB i, Prod.fst_sum, Fin.sum_univ_add]
    simp [h1, (h2 _).1, hMB]
  have h11 : ∀ i k, M (Fin.castAdd q i) (Fin.castAdd q k) = P i k := fun i k => by
    have e := (hfst (Fin.castAdd q i)).symm.trans ((h1' i).trans (hP i))
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at e
    simp only [← sub_smul] at e
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hv _ e k)
  have h21 : ∀ j k, M (Fin.natAdd p j) (Fin.castAdd q k) = 0 := fun j k => by
    have e := (hfst (Fin.natAdd p j)).symm.trans (h2' j).1
    exact Fintype.linearIndependent_iff.1 hv _ e k
  have hsnd : ∀ j, (u' (Fin.natAdd p j)).2 =
      ∑ l : Fin q, M (Fin.natAdd p j) (Fin.natAdd p l) • (u (Fin.natAdd p l)).2 := fun j => by
    rw [← hB (Fin.natAdd p j), Prod.snd_sum, Fin.sum_univ_add]
    simp only [← hMB, Prod.smul_snd, h21, zero_smul, Prod.snd_zero, Finset.sum_const_zero, _root_.zero_add]
  let D : Matrix (Fin q) (Fin q) K := fun j l => M (Fin.natAdd p j) (Fin.natAdd p l)
  have hDQ : D * Q.transpose = 1 := by
    ext j j'
    have e := (h2' j).2 j'
    rw [hsnd j, hQ j'] at e
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, (h2 _).2, smul_eq_mul] at e
    simp only [mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at e
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply]
    rw [← e]
    exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _
  have hdet : M.det = P.det * D.det := det_eq_det_mul_det_of_block M P D h11 h21 fun _ _ => rfl
  have hDQd : D.det * Q.det = 1 := by
    rw [← Matrix.det_transpose Q, ← Matrix.det_mul, hDQ, Matrix.det_one]
  rw [hdet, _root_.mul_assoc, hDQd, _root_.mul_one]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint

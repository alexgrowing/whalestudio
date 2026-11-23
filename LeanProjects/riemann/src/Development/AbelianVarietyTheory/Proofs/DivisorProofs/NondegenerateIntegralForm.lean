import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo

theorem det_gram_ne_zero {L : Type} [AddCommGroup L] {κ : Type} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis κ ℤ L) (B : LinearMap.BilinForm ℤ L) (hB : Function.Injective B) :
    (Matrix.of fun i j => B (b i) (b j)).det ≠ 0 := by
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  apply hc0
  have hx : B (∑ i, c i • b i) = 0 := by
    apply b.ext
    intro j
    have := congrFun hc j
    simpa [Matrix.vecMul, dotProduct, map_sum, map_smul, mul_comm] using this
  have h1 : ∑ i, c i • b i = 0 := hB (hx.trans (map_zero B).symm)
  funext i
  exact Fintype.linearIndependent_iff.mp b.linearIndependent c h1 i

theorem nondeg_afP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (z : AfP p ⊗[ℚ] VQ D),
    (∀ v, (D.EF.baseChange ℚ).baseChange (AfP p) v z = 0) → z = 0 := by
  intro p _ D z hz
  classical
  haveI := D.freeLa; haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let bQ := Algebra.TensorProduct.basis ℚ b
  let bA := Algebra.TensorProduct.basis (AfP p) bQ
  have hg : ∀ i j, (D.EF.baseChange ℚ).baseChange (AfP p) (bA i) (bA j) = ((D.EF (b i) (b j) : ℤ) : AfP p) := by
    intro i j
    simp [bA, bQ, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]
  set c := bA.repr z
  let M : Matrix _ _ (AfP p) := (Matrix.of fun i j => D.EF (b i) (b j)).map (Int.castRingHom (AfP p))
  have hzs : z = ∑ j, c j • bA j := (bA.sum_repr z).symm
  have hM : M.mulVec c = 0 := by
    funext i
    have := hz (bA i)
    rw [hzs, map_sum] at this
    simpa [Matrix.mulVec, dotProduct, M, hg, mul_comm] using this
  have hdet : IsUnit M.det := by
    rw [show M.det = Int.castRingHom (AfP p) (Matrix.of fun i j => D.EF (b i) (b j)).det from
      (RingHom.map_det _ _).symm]
    have h0 := det_gram_ne_zero b D.EF D.nondeg
    have hq : IsUnit (((Matrix.of fun i j => D.EF (b i) (b j)).det : ℤ) : ℚ) :=
      isUnit_iff_ne_zero.mpr (by exact_mod_cast h0)
    have := hq.map (algebraMap ℚ (AfP p))
    simpa using this
  have hc : (⇑c : _ → AfP p) = 0 := by
    have := congrArg (M⁻¹).mulVec hM
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  have hc' : ∀ j, c j = 0 := fun j => congrFun hc j
  rw [hzs]
  simp [hc']

end GlobalTheory.LKGeo

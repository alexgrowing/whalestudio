import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem evI_mulVec {L : Type} [AddCommGroup L] {g : ℕ} (P : L →+ (Fin g → ℂ)) (f : L →ₗ[ℤ] L)
    (H : Matrix (Fin g) (Fin g) ℂ) (h : ∀ x, P (f x) = H *ᵥ P x) (q : ℤ[X]) (x : L) :
    P (aeval f q x) = aeval H q *ᵥ P x := by
  induction q using Polynomial.induction_on generalizing x with
  | C a =>
    simp [Polynomial.aeval_C, Module.algebraMap_end_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
    ext j
    simp
  | add p r hp hr => simp only [map_add, LinearMap.add_apply, hp, hr, Matrix.add_mulVec]
  | monomial n a ih =>
    rw [pow_succ, ← _root_.mul_assoc, map_mul (aeval f) (C a * X ^ n) X, map_mul (aeval H) (C a * X ^ n) X,
      aeval_X, aeval_X, Module.End.mul_apply, ih, h, Matrix.mulVec_mulVec]

private theorem evI_diag {g : ℕ} (H Sb : Matrix (Fin g) (Fin g) ℂ) (ev : Fin g → ℂ)
    (h : H * Sb = Sb * Matrix.diagonal ev) (q : ℤ[X]) :
    aeval H q * Sb = Sb * Matrix.diagonal fun i => aeval (ev i) q := by
  induction q using Polynomial.induction_on with
  | C a =>
    rw [Polynomial.aeval_C]
    simp only [Polynomial.aeval_C, algebraMap_int_eq, eq_intCast, map_intCast]
    rw [Matrix.diagonal_intCast, Int.cast_comm]
  | add p r hp hr => simp only [map_add, add_mul, hp, hr, ← Matrix.diagonal_add, mul_add, Pi.add_def]
  | monomial n a ih =>
    rw [pow_succ, ← _root_.mul_assoc, map_mul (aeval H) (C a * X ^ n) X, aeval_X, _root_.mul_assoc, h,
      ← _root_.mul_assoc, ih, _root_.mul_assoc, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    rw [map_mul (aeval (ev i)) (C a * X ^ n) X, aeval_X]

theorem UpperTheory.Gal.W2.evIntegral_of :
    UpperTheory.Gal.W2.EvIntegral := by
  intro F _ _ O _ bar g ρ a D P₀ hP ga H hH Sb ty ev hD i x
  haveI := D.fin
  haveI := D.free
  let f : D.La →ₗ[ℤ] D.La := ga.toAddMonoidHom.toIntLinearMap
  have hf : ∀ y, P₀ (f y) = H *ᵥ P₀ y := hH
  have hv : ∀ y, aeval H f.charpoly *ᵥ P₀ y = 0 := fun y => by
    rw [← evI_mulVec P₀ f H hf f.charpoly y, LinearMap.aeval_self_charpoly]
    simp
  have hall : ∀ v, aeval H f.charpoly *ᵥ v = 0 := by
    intro v
    have hv' : v ∈ Submodule.span ℝ (Set.range P₀) := by
      rw [hP.2.2.2.1]
      trivial
    induction hv' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, rfl⟩ := hz
      exact hv y
    | zero => simp
    | add u w _ _ hu hw => rw [Matrix.mulVec_add, hu, hw, add_zero]
    | smul r u _ hu => rw [Matrix.mulVec_smul, hu, smul_zero]
  have hq0 : aeval H f.charpoly = 0 := by
    ext j k
    have hjk := congrFun (hall (Pi.single k 1)) j
    simpa [Matrix.mulVec_single] using hjk
  have hdiag := evI_diag H Sb ev hD.2.2 f.charpoly
  rw [hq0, zero_mul] at hdiag
  have hinv : IsUnit Sb := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hD.1)
  have hd : Matrix.diagonal (fun j => aeval (ev j) f.charpoly) = 0 :=
    hinv.mul_left_cancel (by rw [← hdiag, mul_zero])
  have hev0 : aeval (ev i) f.charpoly = 0 := by
    have hii := congrFun (congrFun hd i) i
    simpa using hii
  have hint_ev : IsIntegral ℤ (ev i) := ⟨f.charpoly, LinearMap.charpoly_monic f, by rw [← aeval_def]; exact hev0⟩
  have hint_t : IsIntegral ℤ (ty i (x : F)) :=
    (NumberField.RingOfIntegers.isIntegral_coe x).map (ty i).toIntAlgHom
  intro hzero
  have h2 : ty i ((2 * x : 𝓞 F) : F) = 2 * ty i (x : F) := by
    push_cast
    simp [map_mul, map_ofNat]
  rw [h2] at hzero
  have hprod : algebraMap ℚ ℂ (1 / 2) = ty i (x : F) * ev i := by
    simp only [map_div₀, map_one, map_ofNat]
    linear_combination (1 / 2 : ℂ) * hzero
  have hhalf : IsIntegral ℤ (algebraMap ℚ ℂ (1 / 2)) := by
    rw [hprod]
    exact hint_t.mul hint_ev
  rw [isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective] at hhalf
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hhalf
  have h2n : ((2 * n : ℤ) : ℚ) = 1 := by
    push_cast
    rw [show (n : ℚ) = algebraMap ℤ ℚ n from rfl, hn]
    norm_num
  have h2n' : 2 * n = 1 := by exact_mod_cast h2n
  omega

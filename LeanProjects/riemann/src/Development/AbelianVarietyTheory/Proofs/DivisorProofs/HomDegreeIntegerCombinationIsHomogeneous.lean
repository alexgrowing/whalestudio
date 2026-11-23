import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultilinearQuadraticIsHomogeneous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegOneLeftCompSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberMultilinearSymmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyTopSelfIntersectionAmplePosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionPullbackEqDegreeMulIntersectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPullbackSymmetricClassIntegralCombinationStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AV.AbVar.multilinear_quadratic_isHomogeneous' (P : Type*) [AddCommGroup P] (g n : ℕ)
    (M : MultilinearMap ℤ (fun _ : Fin g => P) ℤ) (a : Fin n → Fin n → P) :
    ∃ F : MvPolynomial (Fin n) ℤ, F.IsHomogeneous (2 * g) ∧
      ∀ m : Fin n → ℤ, MvPolynomial.eval m F = M (fun _ => ∑ i, ∑ j, (m i * m j) • a i j) := by
  let φ : (Fin n → Fin n → ℤ) →ₗ[ℤ] P :=
    { toFun := fun x => ∑ i, ∑ j, x i j • a i j
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  let e : Fin n → Fin n → (Fin n → Fin n → ℤ) := fun i j => Pi.single i (Pi.single j 1)
  have he : ∀ i j, φ (e i j) = a i j := by
    intro i j
    simp only [φ, e, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
    simp
  obtain ⟨F, hF, hFe⟩ := GlobalTheory.multilinear_quadratic_isHomogeneous (Fin n → Fin n → ℤ) g n
    (M.compLinearMap (fun _ => φ)) e
  refine ⟨F, hF, fun m => ?_⟩
  rw [hFe m, MultilinearMap.compLinearMap_apply]
  congr 1
  funext _
  simp only [map_sum, map_zsmul, he]

theorem GlobalTheory.AV.AbVar.deg_isHomogeneousPoly : ∀ (K : Type) [Field K] (A B : AbVar K), A.dim = B.dim → ∀ (n : ℕ) (f : Fin n → (A ⟶ B)), ∃ F : MvPolynomial (Fin n) ℚ, F.IsHomogeneous (2 * A.dim) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) F = (deg (∑ i, m i • f i) : ℚ) := by
  intro K _ A B hAB n f
  obtain ⟨c, hamp, hsym⟩ := GlobalTheory.AV.AbVar.exists_symm_ample K B
  obtain ⟨⟨M, hM⟩, -⟩ := GlobalTheory.T.intersection_number_multilinear_symm K A (Fin A.dim) (Fintype.card_fin _)
  set D : ℤ := inter B (fun _ : Fin A.dim => c) with hD
  have hDpos : 0 < D := GlobalTheory.T.abelianVariety_topSelfIntersection_ample_pos K B c hamp (Fin A.dim) (by rw [Fintype.card_fin, hAB])
  obtain ⟨F, hFh, hFe⟩ := GlobalTheory.AV.AbVar.multilinear_quadratic_isHomogeneous' (Pic A.X.left) A.dim n M
    (fun i j => AbVar.lam c (f i).hom (f j).hom)
  refine ⟨MvPolynomial.C ((1 : ℚ) / ((2 : ℚ) ^ A.dim * D)) * MvPolynomial.map (Int.castRingHom ℚ) F, ?_, ?_⟩
  · have := (MvPolynomial.isHomogeneous_C (Fin n) ((1 : ℚ) / ((2 : ℚ) ^ A.dim * D))).mul (hFh.map (Int.castRingHom ℚ))
    rwa [zero_add] at this
  · intro m
    have hq := GlobalTheory.T.two_smul_pullback_symmetric_class_integral_combination K A B c hsym n f m
    have hp := GlobalTheory.T.intersection_pullback_eq_degree_mul_intersection K A B (show A ⟶ B from ∑ i, m i • f i) hAB (Fin A.dim) (Fintype.card_fin _) (fun _ => c)
    have key : MvPolynomial.eval m F = 2 ^ A.dim * ((deg (show A ⟶ B from ∑ i, m i • f i) : ℤ) * D) := by
      rw [hFe m, ← hq, ← hp, ← hM]
      have := M.map_smul_univ (fun _ => (2 : ℤ)) (fun _ => CechPic.pull (Hom.hom (show A ⟶ B from ∑ i, m i • f i)).left c)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
      rw [← this]
      congr 1
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_map]
    have e2 : MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (m i : ℚ)) F = ((MvPolynomial.eval m F : ℤ) : ℚ) := by
      rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, ← eq_intCast (Int.castRingHom ℚ), MvPolynomial.eval₂_comp_left]
      rfl
    rw [e2, key]
    have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    push_cast
    field_simp

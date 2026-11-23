import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepEx
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed.LatticeTensorCoordinates

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private lemma exists_int_multiple (x : Matrix (Fin n) (Fin n) E) :
    ∃ (m : ℤ) (y : Matrix (Fin n) (Fin n) (𝓞 E)), m ≠ 0 ∧ y.map (algebraMap (𝓞 E) E) = (m : ℚ) • x := by
  classical
  obtain ⟨m, hm, hs⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image (fun ij : Fin n × Fin n => x ij.1 ij.2))
  have h : ∀ i j, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = (m : ℚ) • x i j := by
    intro i j
    have h1 := hs (x i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
    have h2 : m • x i j = (m : ℚ) • x i j := by
      simp [zsmul_eq_mul, Algebra.smul_def]
    rw [h2] at h1
    exact ⟨IsIntegralClosure.mk' (𝓞 E) _ h1, IsIntegralClosure.algebraMap_mk' _ _ _⟩
  choose y hy using h
  refine ⟨m, Matrix.of y, hm, ?_⟩
  ext i j
  simp [hy]

private lemma beta_rep (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E)))
    (hrep : ∀ (x : Matrix (Fin n) (Fin n) (𝓞 E)) (v : Fin n → 𝓞 E),
      rep (x.map (algebraMap (𝓞 E) E)) ((1 : ℚ) ⊗ₜ[ℤ] v) = (1 : ℚ) ⊗ₜ[ℤ] (x *ᵥ v))
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E))
    (hβ : ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E))
    (x : Matrix (Fin n) (Fin n) E) (z : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) : β (rep x z) = x *ᵥ β z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, mulVec_add, ha, hb]
  | tmul q v =>
    have hq : q ⊗ₜ[ℤ] v = q • ((1 : ℚ) ⊗ₜ[ℤ] v) := by
      rw [TensorProduct.smul_tmul']; simp
    obtain ⟨m, y, hm, hy⟩ := exists_int_multiple x
    have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    have key : (m : ℚ) • β (rep x (1 ⊗ₜ v)) = (m : ℚ) • (x *ᵥ β (1 ⊗ₜ v)) := by
      have e1 : (m : ℚ) • β (rep x (1 ⊗ₜ v)) = β (rep ((m : ℚ) • x) (1 ⊗ₜ v)) := by
        rw [map_smul, LinearMap.smul_apply, map_smul]
      have e2 : (m : ℚ) • (x *ᵥ β (1 ⊗ₜ v)) = ((m : ℚ) • x) *ᵥ β (1 ⊗ₜ v) := by
        rw [smul_mulVec]
      rw [e1, e2, ← hy, hrep]
      ext i
      rw [hβ]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
      rw [show ((∑ k, y i k * v k : 𝓞 E) : E) = ∑ k, ((y i k : 𝓞 E) : E) * (v k : E) by
        simp]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hβ]
    have h3 : β (rep x (1 ⊗ₜ v)) = x *ᵥ β (1 ⊗ₜ v) := smul_right_injective _ hmq key
    rw [hq, map_smul, map_smul, map_smul, mulVec_smul, h3]

private def nu (R : Type) [CommRing R] [Algebra ℚ R] (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E)) :
    R ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E)) ≃+ (Fin n → R ⊗[ℚ] E) :=
  ((TensorProduct.congr (LinearEquiv.refl ℚ R) β).trans
    (TensorProduct.piRight ℚ ℚ R (fun _ : Fin n => E))).toAddEquiv

private lemma nu_tmul (R : Type) [CommRing R] [Algebra ℚ R]
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E)) (r : R) (z : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) (i : Fin n) :
    nu R β (r ⊗ₜ z) i = r ⊗ₜ (β z i) := by
  simp [nu]

private lemma actOn_tmul {R : Type} [CommRing R] [Algebra ℚ R]
    (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E)))
    (r r' : R) (x : Matrix (Fin n) (Fin n) E) (z : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) :
    actOn rep R (r ⊗ₜ x) (r' ⊗ₜ z) = (r * r') ⊗ₜ rep x z := by
  unfold actOn
  erw [Algebra.TensorProduct.lift_tmul]
  show r • (LinearMap.baseChange R (rep x)) (r' ⊗ₜ z) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

private lemma nu_act {R : Type} [CommRing R] [Algebra ℚ R]
    (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) (hμ : IsMu μ)
    (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E)))
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E))
    (hr : ∀ x z, β (rep x z) = x *ᵥ β z)
    (y : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) (v : R ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E))) :
    nu R β (actOn rep R y v) = μ y *ᵥ nu R β v := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, add_mulVec, ha, hb]
  | tmul r x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, mulVec_add, ha, hb]
    | tmul r' z =>
      ext1 i
      rw [actOn_tmul, nu_tmul, hr]
      simp only [Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hμ r x i k, nu_tmul, Algebra.TensorProduct.tmul_mul_tmul]

private lemma nu_mem {p : ℕ} (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E))
    (hβ : ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E))
    (v : AfP p ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E))) :
    v ∈ AddSubgroup.closure {z : AfP p ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E)) |
        ∃ (a : AfP p) (x : Fin n → 𝓞 E), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)} ↔
      ∀ i, nu (AfP p) β v i ∈ OHat p E := by
  classical
  constructor
  · intro h i
    induction h using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, x, ha, rfl⟩ := hz
      exact AddSubgroup.subset_closure ⟨a, x i, ha, by rw [nu_tmul, hβ]⟩
    | zero => simpa using zero_mem _
    | add a b _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | neg a _ h => rw [map_neg]; exact neg_mem h
  · intro h
    have hs : ∀ i, ∀ w ∈ OHat p E, (nu (AfP p) β).symm (Pi.single i w) ∈
        AddSubgroup.closure {z : AfP p ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E)) |
          ∃ (a : AfP p) (x : Fin n → 𝓞 E), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)} := by
      intro i w hw
      induction hw using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, x, ha, rfl⟩ := hz
        refine AddSubgroup.subset_closure ⟨a, Pi.single i x, ha, ?_⟩
        rw [AddEquiv.symm_apply_eq]
        funext j
        rw [nu_tmul, hβ]
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      | zero => simpa using zero_mem _
      | add a b _ _ h1 h2 => rw [Pi.single_add, map_add]; exact add_mem h1 h2
      | neg a _ h => rw [Pi.single_neg, map_neg]; exact neg_mem h
    have hv : v = ∑ i, (nu (AfP p) β).symm (Pi.single i (nu (AfP p) β v i)) := by
      rw [← map_sum, Finset.univ_sum_single]; simp
    rw [hv]
    exact sum_mem fun i _ => hs i _ (h i)

end UpperTheory.Gal.W2.Seed.LatticeTensorCoordinates

open UpperTheory.Gal.W2.Seed.LatticeTensorCoordinates in
theorem UpperTheory.Gal.W2.Seed.pLatCoord :
    RepLaws → LatCoord := by
  intro _ E _ _ _ A n p _ S μ hμ
  obtain ⟨β, hβ⟩ := pRepEx E n
  have hr : ∀ x z, β (S.L.rep x z) = x *ᵥ β z := beta_rep S.L.rep S.L_rep β hβ
  refine ⟨nu (AfP p) β, ?_, ?_, ?_⟩
  · intro r v i
    exact (nu_tmul (AfP p) β r _ i).trans (congrArg (fun t => r ⊗ₜ[ℚ] t) (hβ v i))
  · intro h v
    exact nu_act μ hμ S.L.rep β hr (S.mx h) v
  · intro v
    exact nu_mem β hβ v

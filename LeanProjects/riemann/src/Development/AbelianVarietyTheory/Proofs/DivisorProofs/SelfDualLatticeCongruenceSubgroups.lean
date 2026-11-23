import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HatKMConjImp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryWithDeterminantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvertibleUnitaryAdelicMatrixOfRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceIffCompletionStatement

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.UCls.KGrp
open scoped ENNReal TensorProduct

theorem GlobalTheory.UCls.exists_special_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M m : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ L : Submodule (𝓞 E) (Fin r → E)) (g : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (S : Finset (Fin m)) (Γ : Fin m → Subgroup (GL (Fin r) E)) (Λi : Fin m → Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → (L : Set (Fin r → E)) = latOf (maximalRealSubfield E) g0 (Λ : Set (Fin r → E)) → (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) = g0.mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) → (∀ i, IsUA (IsCMField.complexConj E) G (g i)) → (∀ i ∈ S, TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M g0.det (g i).det) → (∀ i ∈ S, (Λi i : Set (Fin r → E)) = latOf (maximalRealSubfield E) (g i) (Λ : Set (Fin r → E)) ∧ ∀ γ, γ ∈ Γ i ↔ IsUStab G (Λi i) γ ∧ ∀ x ∈ Λi i, ∃ y ∈ Λi i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) → ∃ (γ : Fin m → GL (Fin r) E) (s : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), (∀ i ∈ S, (∀ u v, herm G ((γ i : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ i : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) ∧ IsSA G (s i) ∧ ∀ δ : GL (Fin r) E, (δ : Matrix (Fin r) (Fin r) E).det = 1 → (∀ u v, herm G ((δ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((δ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) → (δ ∈ (Γ i).map (MulAut.conj (γ i)⁻¹).toMonoidHom ↔ IsKM (IsCMField.complexConj E) G (L : Set (Fin r → E)) M ((s i)⁻¹ * ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) * s i))) ∧ ∀ i ∈ S, ∀ j ∈ S, SEquiv G (L : Set (Fin r → E)) M (s i) (s j) → UEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M (g i) (g j) := by
  intro E _ _ _ r M m G Λ L g g0 S Γ Λi hM hΛ hg0 hL hLhat hg hT hΓ
  have hU : ∀ {γ : GL (Fin r) E}, (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) → ∀ x y,
      herm G (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x)
        (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y := by
    intro γ hγ x y
    rw [← hγ, mulVec_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, one_mulVec]
  have hRA : ∀ γ : GL (Fin r) E, (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) →
      IsUA (IsCMField.complexConj E) G (ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E)) :=
    fun γ hγ => GlobalTheory.T.isInvertibleUnitaryAdelicMatrix_of_rational_unitary E r G _ (Matrix.isUnits_det_units γ).ne_zero hγ
  have hR1 : ∀ γ : GL (Fin r) E, ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E) *
      ratM (maximalRealSubfield E) ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = 1 := fun γ => by
    rw [← ratM_mul, Units.mul_inv, ratM_one]
  have hR2 : ∀ γ : GL (Fin r) E, ratM (maximalRealSubfield E) ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *
      ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E) = 1 := fun γ => by
    rw [← ratM_mul, Units.inv_mul, ratM_one]
  have hdet : ∀ γ : Matrix (Fin r) (Fin r) E, (ratM (maximalRealSubfield E) γ).det =
      (1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ γ.det := fun γ =>
    (RingHom.map_det (Algebra.TensorProduct.includeRight : E →ₐ[maximalRealSubfield E]
      RA (maximalRealSubfield E) E).toRingHom γ).symm
  have hex : ∀ i, ∃ (γ : GL (Fin r) E) (k : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), i ∈ S →
      (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) ∧
      IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M k ∧
      IsSA G (ratM (maximalRealSubfield E) ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i * k⁻¹ * g0⁻¹) := by
    intro i
    by_cases hi : i ∈ S
    swap
    · exact ⟨1, 1, fun h => absurd h hi⟩
    obtain ⟨u, hu, k, hk, hdg⟩ := hT i hi
    obtain ⟨γ, hγ, hγdet⟩ : ∃ γ : GL (Fin r) E, (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x)
        ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) ∧ (0 < r → (γ : Matrix (Fin r) (Fin r) E).det = u) := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · exact ⟨1, fun x y => by simp, fun h => absurd h (by omega)⟩
      · obtain ⟨γ, h1, h2⟩ := GlobalTheory.T.exists_unitary_with_determinant E r G u hr hΛ.1 hΛ.2.1 hu
        exact ⟨γ, h1, fun _ => h2⟩
    refine ⟨γ, k, fun _ => ⟨hγ, hk, ?_, ?_⟩⟩
    · exact isUA_mul _ G (isUA_mul _ G (isUA_mul _ G (hRA _ (hU hγ)) (hg i)) (isUA_inv _ G hk.1))
        (isUA_inv _ G hg0)
    · rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; simp
      · have hγ1 : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).det * u = 1 := by
          rw [← hγdet hr, ← det_mul, Units.inv_mul, det_one]
        have e1 : ((1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ
            ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).det : RA (maximalRealSubfield E) E) *
            ((1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ u) = 1 := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hγ1, Algebra.TensorProduct.one_def]
        have e2 := Ring.mul_inverse_cancel _ hg0.1
        have e3 := Ring.mul_inverse_cancel _ hk.1.1
        rw [det_mul, det_mul, det_mul, det_nonsing_inv, det_nonsing_inv, hdet, hdg]
        calc _ = (((1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ
            ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).det : RA (maximalRealSubfield E) E) *
            ((1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ u)) *
            (g0.det * Ring.inverse g0.det) * (k.det * Ring.inverse k.det) := by ring
          _ = 1 := by rw [e1, e2, e3, one_mul, one_mul]
  choose γ k hγk using hex

  refine ⟨γ, fun i => ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
    (k i)⁻¹ * g0⁻¹, ?_, ?_⟩
  · intro i hi
    obtain ⟨hγU, hk, hsSA⟩ := hγk i hi
    refine ⟨hγU, hsSA, fun δ hδdet hδU => ?_⟩
    have hmap : δ ∈ (Γ i).map (MulAut.conj (γ i)⁻¹).toMonoidHom ↔ γ i * δ * (γ i)⁻¹ ∈ Γ i := by
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
    obtain ⟨hΛi, hΓi⟩ := hΓ i hi
    have hgU : IsUnit (g i) := (Matrix.isUnit_iff_isUnit_det _).2 (hg i).1
    obtain ⟨Λ', hΛ'1, -, -, hΛ'hat⟩ := exists_lattice_latOf (maximalRealSubfield E) E r Λ hgU.unit
      hΛ.2.2.1 hΛ.2.2.2.1
    rw [IsUnit.unit_spec] at hΛ'1 hΛ'hat
    have hhat : (hat (maximalRealSubfield E) (Λi i : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) =
        (g i).mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set _) := by
      rw [hΛi, ← hΛ'1, hΛ'hat]
    have hrat : ∀ v, fv (maximalRealSubfield E) v ∈ hat (maximalRealSubfield E) (Λi i : Set (Fin r → E)) ↔
        v ∈ Λi i := fun v => by
      rw [← SetLike.mem_coe, hhat, ← SetLike.mem_coe (x := v), hΛi]; rfl
    have hβU : ∀ x y, herm G (((γ i * δ * (γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x)
        (((γ i * δ * (γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y := by
      intro x y
      simp only [Units.val_mul, ← mulVec_mulVec, hγU, hδU, hU hγU]
    have e0 : g0 * g0⁻¹ = 1 := mul_nonsing_inv g0 hg0.1
    have e0' : g0⁻¹ * g0 = 1 := nonsing_inv_mul g0 hg0.1
    have ek : k i * (k i)⁻¹ = 1 := mul_nonsing_inv _ hk.1.1
    have ek' : (k i)⁻¹ * k i = 1 := nonsing_inv_mul _ hk.1.1
    have eg : g i * (g i)⁻¹ = 1 := mul_nonsing_inv _ (hg i).1
    have eg' : (g i)⁻¹ * g i = 1 := nonsing_inv_mul _ (hg i).1
    have c0 : ∀ P, P * g0 * g0⁻¹ = P := fun P => by rw [Matrix.mul_assoc, e0, Matrix.mul_one]
    have c0' : ∀ P, P * g0⁻¹ * g0 = P := fun P => by rw [Matrix.mul_assoc, e0', Matrix.mul_one]
    have ck : ∀ P, P * k i * (k i)⁻¹ = P := fun P => by rw [Matrix.mul_assoc, ek, Matrix.mul_one]
    have ck' : ∀ P, P * (k i)⁻¹ * k i = P := fun P => by rw [Matrix.mul_assoc, ek', Matrix.mul_one]
    have cg : ∀ P, P * g i * (g i)⁻¹ = P := fun P => by rw [Matrix.mul_assoc, eg, Matrix.mul_one]
    have cg' : ∀ P, P * (g i)⁻¹ * g i = P := fun P => by rw [Matrix.mul_assoc, eg', Matrix.mul_one]
    have cR : ∀ P, P * ratM (maximalRealSubfield E) (γ i : Matrix (Fin r) (Fin r) E) *
        ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = P := fun P => by
      rw [Matrix.mul_assoc, hR1, Matrix.mul_one]
    have hXY : (hat (maximalRealSubfield E) (Λi i : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) =
        (g i * (k i)⁻¹ * g0⁻¹).mulVec '' (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) := by
      rw [hhat, ← isKM_image _ G _ M (isKM_inv _ G _ M hk), Set.image_image, hLhat, Set.image_image]
      simp only [mulVec_mulVec, c0']
    have hsinv : (ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
        (k i)⁻¹ * g0⁻¹)⁻¹ = g0 * k i * (g i)⁻¹ * ratM (maximalRealSubfield E) (γ i : Matrix (Fin r) (Fin r) E) := by
      refine Matrix.inv_eq_left_inv ?_
      simp only [← Matrix.mul_assoc, cR, cg', ck, e0]
    have hconj := hatKM_conj (X := (hat (maximalRealSubfield E) (Λi i : Set (Fin r → E)) : Set _))
      (Y := (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E))) M
      (A := g i * (k i)⁻¹ * g0⁻¹) (A' := g0 * k i * (g i)⁻¹)
      (P := ratM (maximalRealSubfield E) ((γ i * δ * (γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E))
      (by simp only [← Matrix.mul_assoc, c0', ck', eg]) (by simp only [← Matrix.mul_assoc, cg', ck, e0]) hXY
    have hPeq : g0 * k i * (g i)⁻¹ * ratM (maximalRealSubfield E)
        ((γ i * δ * (γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * (g i * (k i)⁻¹ * g0⁻¹) =
        (ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
        (k i)⁻¹ * g0⁻¹)⁻¹ * ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) *
        (ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
        (k i)⁻¹ * g0⁻¹) := by
      rw [hsinv, Units.val_mul, Units.val_mul, ratM_mul, ratM_mul]
      simp only [Matrix.mul_assoc]
    rw [hPeq] at hconj
    have hsUA := hsSA.1
    have hKUA : IsUA (IsCMField.complexConj E) G ((ratM (maximalRealSubfield E)
        (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i * (k i)⁻¹ * g0⁻¹)⁻¹ *
        ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) *
        (ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
        (k i)⁻¹ * g0⁻¹)) :=
      isUA_mul _ G (isUA_mul _ G (isUA_inv _ G hsUA) (hRA δ hδU)) hsUA
    have hL5 := GlobalTheory.T.lattice_congruence_iff_completion (maximalRealSubfield E) E r (Λi i) M (γ i * δ * (γ i)⁻¹) hM hrat
    rw [hmap, hΓi]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨hKUA, hconj.1 (hL5.1 ⟨h1, h2⟩)⟩
    · intro hK
      obtain ⟨h1, h2⟩ := hL5.2 (hconj.2 hK.2)
      exact ⟨⟨hβU, h1⟩, h2⟩

  · intro i hi j hj hSE
    obtain ⟨δ, hδ, κ, hκ, -, hsj⟩ := hSE
    simp only at hsj
    obtain ⟨hγiU, hki, -⟩ := hγk i hi
    obtain ⟨hγjU, hkj, -⟩ := hγk j hj
    have e0' : g0⁻¹ * g0 = 1 := nonsing_inv_mul g0 hg0.1
    have ekj : k j * (k j)⁻¹ = 1 := mul_nonsing_inv _ hkj.1.1
    have egj : g j * (g j)⁻¹ = 1 := mul_nonsing_inv _ (hg j).1
    refine ⟨(γ j : Matrix (Fin r) (Fin r) E) * δ * (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E), ?_,
      (k i)⁻¹ * (g0⁻¹ * κ * g0) * k j, ?_, ?_⟩
    · rw [ratM_mul, ratM_mul]
      exact isUA_mul _ G (isUA_mul _ G (hRA _ hγjU) hδ.1) (hRA _ (hU hγiU))
    · exact isKM_mul _ G _ M (isKM_mul _ G _ M (isKM_inv _ G _ M hki) (isKM_conj _ G _ _ M hg0 hLhat hκ)) hkj
    · have hdj : g j = ratM (maximalRealSubfield E) (γ j : Matrix (Fin r) (Fin r) E) *
          (ratM (maximalRealSubfield E) (((γ j)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g j *
            (k j)⁻¹ * g0⁻¹) * g0 * k j := by
        simp only [← Matrix.mul_assoc, hR1 (γ j), Matrix.one_mul]
        rw [Matrix.mul_assoc (g j * (k j)⁻¹), e0', Matrix.mul_one, Matrix.mul_assoc, nonsing_inv_mul _ hkj.1.1,
          Matrix.mul_one]
      rw [hdj, hsj, ratM_mul, ratM_mul]
      simp only [Matrix.mul_assoc]

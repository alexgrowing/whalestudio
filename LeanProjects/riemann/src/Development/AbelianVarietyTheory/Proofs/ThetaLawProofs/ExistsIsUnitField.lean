import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
open GlobalTheory.KeyKa

namespace GlobalTheory.TorsExists

variable {Ix : Type} [Fintype Ix] [DecidableEq Ix]

theorem exists_mul_mul_eq {K : Type} [Field K] (D : Matrix Ix Ix K) : ∃ G : Matrix Ix Ix K, D * G * D = D := by
  set f := Matrix.toLin' D with hf
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨g, hg⟩ := LinearMap.exists_extend s
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', ← hf]
  refine LinearMap.ext fun v => ?_
  have h1 : g (f v) = s (f.rangeRestrict v) := by rw [← hg]; rfl
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hs (f.rangeRestrict v))
  simp only [LinearMap.comp_apply, h1]
  exact h2

theorem exists_isUnit_field {K : Type} [Field K] (D : Matrix Ix Ix K) (hD : D * D = 0)
    (hex : ∀ v : Ix → K, D.mulVec v = 0 → ∃ w, D.mulVec w = v) :
    ∃ G : Matrix Ix Ix K, IsUnit (D * G + G * D).det := by
  obtain ⟨G, hG⟩ := exists_mul_mul_eq D
  refine ⟨G, ?_⟩
  set N := 1 - (D * G + G * D) with hN
  have h1 : D * N = 0 := by
    rw [hN, mul_sub, mul_add, ← mul_assoc, ← mul_assoc, hD, hG]; simp
  have h2 : N * D = 0 := by
    rw [hN, sub_mul, add_mul, mul_assoc G, hD, hG]; simp
  have h3 : N * N = 0 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    obtain ⟨w, hw⟩ := hex (N.mulVec v) (by rw [Matrix.mulVec_mulVec, h1, Matrix.zero_mulVec])
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← hw, Matrix.mulVec_mulVec, h2,
      Matrix.zero_mulVec, Matrix.zero_mulVec]
  have h4 : (D * G + G * D) * (1 + N) = 1 := by
    have : D * G + G * D = 1 - N := by rw [hN]; abel
    rw [this, sub_mul, mul_add, mul_add, h3]; simp
  exact Matrix.isUnit_det_of_right_inverse h4

theorem exists_contraction {R : Type} [CommRing R] [IsLocalRing R] (D : Matrix Ix Ix R) (hD : D * D = 0)
    (hex : ∀ v : Ix → IsLocalRing.ResidueField R, (D.map (IsLocalRing.residue R)).mulVec v = 0 →
      ∃ w, (D.map (IsLocalRing.residue R)).mulVec w = v) :
    ∃ h : Matrix Ix Ix R, D * h + h * D = 1 := by
  obtain ⟨G, hG⟩ := exists_isUnit_field (D.map (IsLocalRing.residue R))
    (by rw [← Matrix.map_mul, hD]; simp) hex
  choose H hH using fun p q => IsLocalRing.residue_surjective (R := R) (G p q)
  have hHG : (Matrix.of H).map (IsLocalRing.residue R) = G := by ext p q; exact hH p q
  set A := D * Matrix.of H + Matrix.of H * D with hA
  have hu : IsUnit A.det := by
    have : IsLocalRing.residue R A.det = (D.map (IsLocalRing.residue R) * G + G * D.map (IsLocalRing.residue R)).det := by
      rw [RingHom.map_det, ← hHG, hA]
      simp [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_add]
    rw [← this] at hG
    exact (isUnit_map_iff _ _).1 hG
  have hc : A * D = D * A := by
    rw [hA, add_mul, mul_add, mul_assoc (Matrix.of H), hD, ← mul_assoc D D, hD]; simp [mul_assoc]
  have hc' : A⁻¹ * D = D * A⁻¹ := by
    calc A⁻¹ * D = A⁻¹ * D * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv _ hu, mul_one]
      _ = A⁻¹ * (A * D) * A⁻¹ := by rw [hc]; simp only [mul_assoc]
      _ = D * A⁻¹ := by rw [← mul_assoc, Matrix.nonsing_inv_mul _ hu, one_mul]
  refine ⟨Matrix.of H * A⁻¹, ?_⟩
  rw [mul_assoc, hc', ← mul_assoc, ← mul_assoc, ← add_mul, ← hA, Matrix.mul_nonsing_inv _ hu]

theorem exists_homogeneous {R : Type} [CommRing R] (deg : Ix → ℕ) (D h : Matrix Ix Ix R)
    (hD : ∀ p q, deg q ≠ deg p + 1 → D p q = 0) (hh : D * h + h * D = 1) :
    ∃ h' : Matrix Ix Ix R, (∀ p q, deg p ≠ deg q + 1 → h' p q = 0) ∧ D * h' + h' * D = 1 := by
  refine ⟨Matrix.of fun p q => if deg p = deg q + 1 then h p q else 0, fun p q hpq => by simp [hpq], ?_⟩
  ext a b
  by_cases hab : deg a = deg b
  · rw [← hh]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
    congr 1 <;> refine Finset.sum_congr rfl fun p _ => ?_
    · split_ifs with hp
      · rfl
      · rw [hD a p (by omega)]; simp
    · split_ifs with hp
      · rfl
      · rw [hD p b (by omega)]; simp
  · rw [Matrix.one_apply_ne (fun e => hab (by rw [e]))]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro p _
      split_ifs with hp
      · rw [hD p b (by omega)]; simp
      · simp
    · intro p _
      split_ifs with hp
      · rw [hD a p (by omega)]; simp
      · simp

theorem block_mul_block {R : Type} [CommRing R] (P Q : Ix → Prop) [DecidablePred P] [DecidablePred Q]
    (M : Matrix Ix Ix R) (hM : M * M = 1) (h0 : ∀ p r, P p → ¬ Q r → M p r = 0) :
    M.submatrix (fun p : {p // P p} => p.1) (fun r : {r // Q r} => r.1) *
      M.submatrix (fun r : {r // Q r} => r.1) (fun p : {p // P p} => p.1) = 1 := by
  ext a b
  have h1 : (M * M) a.1 b.1 = (1 : Matrix {p // P p} {p // P p} R) a b := by
    rw [hM]; simp [Matrix.one_apply, Subtype.ext_iff]
  rw [← h1]
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype Q (fun r => M a.1 r * M r b.1)]
  rw [Finset.sum_eq_zero (s := (Finset.univ : Finset {r // ¬ Q r})), add_zero]
  intro r _
  rw [h0 _ _ a.2 r.2, zero_mul]

theorem nonempty_equiv {R : Type} [CommRing R] [Nontrivial R] (deg : Ix → ℕ) (D h : Matrix Ix Ix R)
    (hD : IsCx deg D) (hdeg : ∀ p q, deg p ≠ deg q + 1 → h p q = 0) (hh : D * h + h * D = 1) :
    Nonempty ({p // Even (deg p)} ≃ {p // ¬ Even (deg p)}) := by
  obtain ⟨hD1, hD2⟩ := hD
  have e1 : D * h = 1 - h * D := eq_sub_of_add_eq hh
  have e2 : D * h * D = D := by rw [e1, sub_mul, mul_assoc, hD2]; simp
  have e3 : D * h * (h * D) = 0 := by
    have : D * h = 1 - h * D := e1
    have e4 : h * D * (h * D) = h * D := by
      rw [mul_assoc, ← mul_assoc D, e2]
    rw [e1, sub_mul, e4]; simp
  set M := D + h * D * h with hM
  have hMM : M * M = 1 := by
    have : M * M = D * D + (D * h * D) * h + h * (D * h * D) + h * (D * h * (h * D)) * h := by
      rw [hM]; noncomm_ring
    rw [this, hD2, e2, e3, ← hh]; simp
  have hpar : ∀ p q, (Even (deg p) ↔ Even (deg q)) → M p q = 0 := by
    intro p q hpq
    have n1 : deg q ≠ deg p + 1 := fun e => by
      rw [e, Nat.even_add_one] at hpq; tauto
    have n2 : deg p ≠ deg q + 1 := fun e => by
      rw [e, Nat.even_add_one] at hpq; tauto
    rw [hM, Matrix.add_apply, hD1 p q n1, zero_add, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases c1 : deg p = deg s + 1
    · by_cases c2 : deg r = deg s + 1
      · rw [hdeg r q (by omega)]; simp
      · rw [hD1 s r c2]; simp
    · rw [hdeg p s c1]; simp
  exact ⟨Matrix.indexEquivOfInv
    (block_mul_block (fun p => Even (deg p)) (fun p => ¬ Even (deg p)) M hMM
      (fun p r hp hr => hpar p r (by tauto)))
    (block_mul_block (fun p => ¬ Even (deg p)) (fun p => Even (deg p)) M hMM
      (fun p r hp hr => hpar p r (by tauto)))⟩

theorem exists_torsSq : ∀ (R Ix : Type) [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : Matrix Ix Ix R) [IsLocalRing R], IsCx deg D → (∀ v : Ix → IsLocalRing.ResidueField R, (D.map (IsLocalRing.residue R)).mulVec v = 0 → ∃ w, (D.map (IsLocalRing.residue R)).mulVec w = v) → ∃ t, TorsSq deg D t := by
  intro R Ix _ _ _ deg D _ hD hex
  obtain ⟨h0, hh0⟩ := exists_contraction D hD.2 hex
  obtain ⟨h, hdeg, hh⟩ := exists_homogeneous deg D h0 hD.1 hh0
  obtain ⟨e⟩ := nonempty_equiv deg D h hD hdeg hh
  exact ⟨_, h, hdeg, hh, e, rfl⟩

end GlobalTheory.TorsExists

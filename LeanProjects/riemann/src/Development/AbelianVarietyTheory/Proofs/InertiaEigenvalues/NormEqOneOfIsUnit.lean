import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwConj
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorOfSeparableCharpolyField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorSemilocalOfCyclicVectorField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
open GlobalTheory.Tw Matrix

noncomputable section

namespace GlobalTheory.SplitLattice

variable {E : Type} [NormedField E] [IsUltrametricDist E]

def ball : ValuationSubring E where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha
  mem_or_inv_mem' x := by
    by_cases h : ‖x‖ ≤ 1
    · exact Or.inl h
    · right
      show ‖x⁻¹‖ ≤ 1
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 h))

theorem norm_le_one (x : (ball : ValuationSubring E)) : ‖(x : E)‖ ≤ 1 := x.2

theorem norm_eq_one_of_isUnit {x : (ball : ValuationSubring E)} (hx : IsUnit x) : ‖(x : E)‖ = 1 := by
  obtain ⟨u, rfl⟩ := hx
  have h0 : ((u : (ball : ValuationSubring E)) : E) * ((u⁻¹ : (ball : ValuationSubring E)ˣ) : E) = 1 :=
    congrArg Subtype.val u.mul_inv
  have h := congrArg norm h0
  rw [norm_mul, norm_one] at h
  have h1 := norm_le_one (u : (ball : ValuationSubring E))
  have h2 := norm_le_one ((u⁻¹ : (ball : ValuationSubring E)ˣ) : (ball : ValuationSubring E))
  nlinarith [norm_nonneg ((u : (ball : ValuationSubring E)) : E),
    norm_nonneg (((u⁻¹ : (ball : ValuationSubring E)ˣ) : (ball : ValuationSubring E)) : E)]

instance : Finite (MaximalSpectrum (ball : ValuationSubring E)) := by
  haveI : Subsingleton (MaximalSpectrum (ball : ValuationSubring E)) := ⟨fun a b => by
    have ha := IsLocalRing.eq_maximalIdeal a.isMaximal
    have hb := IsLocalRing.eq_maximalIdeal b.isMaximal
    exact MaximalSpectrum.ext (ha.trans hb.symm)⟩
  exact Finite.of_subsingleton

abbrev ι : (ball : ValuationSubring E) →+* E := (ball : ValuationSubring E).subtype

theorem exists_cyclic_basis {n : ℕ} (M : Matrix (Fin n) (Fin n) E) (hM : ∀ i j, ‖M i j‖ ≤ 1)
    (hs : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * M.charpoly + v * Polynomial.derivative M.charpoly = 1) :
    ∃ K : Matrix (Fin n) (Fin n) (ball : ValuationSubring E), IsUnit K.det ∧
      M * K.map ι = K.map ι * GlobalTheory.Orb.companionMat n M.charpoly := by
  obtain ⟨u, v, hu, hv, huv⟩ := hs
  let M' : Matrix (Fin n) (Fin n) (ball : ValuationSubring E) := Matrix.of fun i j => ⟨M i j, hM i j⟩
  have hM' : M'.map ι = M := by ext i j; rfl
  have lift : ∀ p : Polynomial E, (∀ i, ‖p.coeff i‖ ≤ 1) →
      ∃ q : Polynomial (ball : ValuationSubring E), q.map ι = p := by
    intro p hp
    exact (Polynomial.mem_lifts p).1 ((Polynomial.lifts_iff_coeff_lifts p).2 fun i => ⟨⟨p.coeff i, hp i⟩, rfl⟩)
  obtain ⟨u', hu'⟩ := lift u hu
  obtain ⟨v', hv'⟩ := lift v hv
  have hsep : M'.charpoly.Separable := by
    refine ⟨u', v', Polynomial.map_injective ι Subtype.val_injective ?_⟩
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      ← Matrix.charpoly_map, hM', hu', hv', Polynomial.map_one]
    exact huv
  obtain ⟨w, hw⟩ := GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField GlobalTheory.RegSS.cyclicField _
    (Fin n) M' hsep
  let σ : Equiv.Perm (Fin n) := (Fintype.equivFin (Fin n)).trans (finCongr (Fintype.card_fin n))
  have hk : GlobalTheory.RegSS.krylov M' w = (GlobalTheory.ClassParam.krylov M' w).submatrix id σ := by
    ext i j
    simp [GlobalTheory.RegSS.krylov, GlobalTheory.ClassParam.krylov, σ]
  refine ⟨GlobalTheory.ClassParam.krylov M' w, ?_, ?_⟩
  · rw [hk, Matrix.det_permute'] at hw
    exact isUnit_of_mul_isUnit_right hw
  · rw [GlobalTheory.ClassParam.krylov_map, hM']
    exact GlobalTheory.Orb.mul_krylov_eq M _

theorem split_place : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [LocallyCompactSpace E] (n : ℕ) (A x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖A i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * A.charpoly + v * Polynomial.derivative A.charpoly = 1) → IsUnit x → (∀ i j, ‖(x⁻¹ * A * x) i j‖ ≤ 1) → ∃ t k : Matrix (Fin n) (Fin n) E, IsUnit t ∧ t * A = A * t ∧ (∀ i j, ‖k i j‖ ≤ 1) ∧ ‖k.det‖ = 1 ∧ x = t * k := by
  intro E _ _ _ n A x hA hs hx hy
  obtain ⟨U, rfl⟩ := hx
  have hcp : ((U : Matrix (Fin n) (Fin n) E)⁻¹ * A *
      (U : Matrix (Fin n) (Fin n) E)).charpoly = A.charpoly :=
    Matrix.charpoly_units_conj' U A
  obtain ⟨KA, hKA, hA'⟩ := exists_cyclic_basis A hA hs
  obtain ⟨Ky, hKy, hy'⟩ := exists_cyclic_basis _ hy (hcp ▸ hs)
  rw [hcp] at hy'
  set C := GlobalTheory.Orb.companionMat n A.charpoly
  set a := KA.map ι with ha_def
  set b := Ky.map ι with hb_def
  have ha : IsUnit a.det := by
    rw [ha_def, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hKA.map ι
  have hb : IsUnit b.det := by
    rw [hb_def, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hKy.map ι
  have hbinv : (Ky⁻¹).map ι = b⁻¹ := by
    refine (Matrix.inv_eq_right_inv ?_).symm
    rw [hb_def, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
      Matrix.mul_nonsing_inv _ hKy, map_one]
  have hk : (KA * Ky⁻¹).map ι = a * b⁻¹ := by
    rw [← RingHom.mapMatrix_apply, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hbinv]
  have hUU : (U : Matrix (Fin n) (Fin n) E) * (U : Matrix (Fin n) (Fin n) E)⁻¹ = 1 := by
    rw [← Matrix.coe_units_inv]; exact Units.mul_inv U
  have haA : a⁻¹ * A = C * a⁻¹ := by
    calc a⁻¹ * A = a⁻¹ * (A * a) * a⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.mul_one]
      _ = C * a⁻¹ := by
          rw [hA', ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul]
  refine ⟨(U : Matrix (Fin n) (Fin n) E) * b * a⁻¹, (KA * Ky⁻¹).map ι, ?_, ?_, ?_, ?_, ?_⟩
  · exact (U.isUnit.mul ((Matrix.isUnit_iff_isUnit_det _).2 hb)).mul
      ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det a ha))
  · calc (U : Matrix (Fin n) (Fin n) E) * b * a⁻¹ * A = (U : Matrix (Fin n) (Fin n) E) * (b * C) * a⁻¹ := by
          rw [Matrix.mul_assoc, haA, ← Matrix.mul_assoc, Matrix.mul_assoc ((U : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E)]
      _ = (U : Matrix (Fin n) (Fin n) E) * ((U : Matrix (Fin n) (Fin n) E)⁻¹ * A * (U : Matrix (Fin n) (Fin n) E) * b) * a⁻¹ := by rw [hy']
      _ = A * ((U : Matrix (Fin n) (Fin n) E) * b * a⁻¹) := by
          simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  · intro i j
    exact norm_le_one _
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    refine norm_eq_one_of_isUnit ?_
    rw [Matrix.det_mul]
    exact hKA.mul (Matrix.isUnit_nonsing_inv_det Ky hKy)
  · rw [hk]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc a⁻¹ a, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hb, Matrix.mul_one]

end GlobalTheory.SplitLattice

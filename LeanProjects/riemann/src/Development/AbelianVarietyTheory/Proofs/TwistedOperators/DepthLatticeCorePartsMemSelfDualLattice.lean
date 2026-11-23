import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedHomLatticeModulusDepthMemShiftStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMatrixSandwichMemCompletedHomLatticeSelfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.BigProj

variable {D : D7}

theorem idLat_one {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : idLat 1 Λ = Λ := by
  apply le_antisymm
  · rw [idLat, Submodule.span_le]
    rintro z ⟨s, hs, y, hy, rfl⟩
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hs
    rw [algebraMap_smul]
    exact Λ.smul_mem r hy
  · intro y hy
    exact Submodule.subset_span ⟨1, FractionalIdeal.one_mem_one _, y, hy, (one_smul _ _).symm⟩

theorem idLat_mulVec {n : ℕ} (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (M : Matrix (Fin n) (Fin n) D.host.E) (hM : ∀ x ∈ Λ, M *ᵥ x ∈ Λ) : ∀ x ∈ idLat I Λ, M *ᵥ x ∈ idLat I Λ := by
  intro x hx
  have hle : idLat I Λ ≤ (idLat I Λ).comap ((Matrix.mulVecLin M).restrictScalars (𝓞 D.host.E)) := by
    rw [idLat, Submodule.span_le]
    rintro z ⟨s, hs, y, hy, rfl⟩
    change M *ᵥ (s • y) ∈ Submodule.span (𝓞 D.host.E) {z | ∃ s ∈ I, ∃ y ∈ Λ, z = s • y}
    rw [Matrix.mulVec_smul]
    exact Submodule.subset_span ⟨s, hs, M *ᵥ y, hM y hy, rfl⟩
  exact hle hx

theorem latO_negSp_le (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

section Witt

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem qX_e : d.qX * d.e = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.pX_jX)
theorem qX_e' : d.qX * d.e' = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pX_jY)
theorem qX_i₀ : d.qX * d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pX_j0)
theorem qY_e : d.qY * d.e = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pY_jX)
theorem qY_e' : d.qY * d.e' = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.pY_jY)
theorem qY_i₀ : d.qY * d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pY_j0)

end Witt

end GlobalTheory.AscFin.BigProj

namespace GlobalTheory.AscFin.BigProj

variable {D : D7}

theorem mul_col {m n r c : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (a : Matrix (Fin n) (Fin c) D.host.E)
    (Bm : Matrix (Fin n) (Fin r) D.host.E) (q : Fin c) (p : Fin r) (κ : D.host.E) (h : ∀ l, a l q = κ * Bm l p)
    (k : Fin m) : (M * a) k q = κ * (M * Bm) k p := by
  simp only [Matrix.mul_apply, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

section SlopeTestRemainingChoices

variable {A B : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B A ρ)

theorem auxiliary_vector_multiple_of_witt_basis_vector (hd : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ) (q : Fin c) :
    (q.1 < ρ → ∃ p : Fin ρ, ∃ κ : D.host.E, ∀ l, a.a l q = κ * d.e l p) ∧
    (¬ q.1 < ρ → ∃ p : Fin ρ, ∃ κ : D.host.E, ∀ l, a.a l q = κ * d.e' l p) := by
  obtain ⟨h2, he, s, he'⟩ := hd
  have hq2 := q.2
  refine ⟨fun hq => ⟨⟨q.1, hq⟩, ((-D.host.xi0) ^ (q.1 + 1))⁻¹, fun l => ?_⟩, fun hq => ?_⟩
  · rw [he]
    simp only [colsOf]
    rw [inv_mul_cancel_left₀ (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero))]
    rfl
  · have hp : c - 1 - q.1 < ρ := by omega
    have hs : s ⟨c - 1 - q.1, hp⟩ ≠ 0 := by
      intro h0
      have := congrFun (congrFun (qY_e' d) ⟨c - 1 - q.1, hp⟩) ⟨c - 1 - q.1, hp⟩
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
      simp [he', colsOf, h0] at this
    refine ⟨⟨c - 1 - q.1, hp⟩, (s ⟨c - 1 - q.1, hp⟩)⁻¹, fun l => ?_⟩
    rw [he']
    simp only [colsOf]
    rw [inv_mul_cancel_left₀ hs]
    congr 1
    ext
    simp only [Fin.val_rev, Fin.val_castLE]
    omega

theorem wittHyperbolic_projX_auxiliary_vectors (hd : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ) :
    d.e * d.qX * a.a = a.a * Matrix.diagonal (fun q : Fin c => if q.1 < ρ then (1 : D.host.E) else 0) := by
  ext k q
  rw [Matrix.mul_diagonal]
  by_cases hq : q.1 < ρ
  · obtain ⟨p, κ, h⟩ := (auxiliary_vector_multiple_of_witt_basis_vector a d hd hc q).1 hq
    rw [mul_col _ _ _ q p κ h, Matrix.mul_assoc, qX_e, Matrix.mul_one, if_pos hq, mul_one, h]
  · obtain ⟨p, κ, h⟩ := (auxiliary_vector_multiple_of_witt_basis_vector a d hd hc q).2 hq
    rw [mul_col _ _ _ q p κ h]
    simp [Matrix.mul_assoc, qX_e', hq]

theorem wittHyperbolic_projY_auxiliary_vectors (hd : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ) :
    d.e' * d.qY * a.a = a.a * Matrix.diagonal (fun q : Fin c => if q.1 < ρ then (0 : D.host.E) else 1) := by
  ext k q
  rw [Matrix.mul_diagonal]
  by_cases hq : q.1 < ρ
  · obtain ⟨p, κ, h⟩ := (auxiliary_vector_multiple_of_witt_basis_vector a d hd hc q).1 hq
    rw [mul_col _ _ _ q p κ h]
    simp [Matrix.mul_assoc, qY_e, hq]
  · obtain ⟨p, κ, h⟩ := (auxiliary_vector_multiple_of_witt_basis_vector a d hd hc q).2 hq
    rw [mul_col _ _ _ q p κ h, Matrix.mul_assoc, qY_e', Matrix.mul_one, if_neg hq, mul_one, h]

theorem proj_lat (hd : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ) (hi : d.i₀ = frameMat B A a.ι)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    ∀ x ∈ a.lat Λ 𝔟, (d.e * d.qX) *ᵥ x ∈ a.lat Λ 𝔟 ∧ (d.e' * d.qY) *ᵥ x ∈ a.lat Λ 𝔟 := by
  rintro x ⟨y, hy, u, hu, rfl⟩
  have k1 : d.e * d.qX * frameMat B A a.ι = 0 := by rw [← hi, Matrix.mul_assoc, qX_i₀, Matrix.mul_zero]
  have k2 : d.e' * d.qY * frameMat B A a.ι = 0 := by rw [← hi, Matrix.mul_assoc, qY_i₀, Matrix.mul_zero]
  refine ⟨⟨0, Λ.zero_mem, Matrix.diagonal (fun q : Fin c => if q.1 < ρ then (1 : D.host.E) else 0) *ᵥ u, fun p => ?_, ?_⟩,
    ⟨0, Λ.zero_mem, Matrix.diagonal (fun q : Fin c => if q.1 < ρ then (0 : D.host.E) else 1) *ᵥ u, fun p => ?_, ?_⟩⟩
  · rw [Matrix.mulVec_diagonal]
    split_ifs
    · rw [one_mul]; exact hu p
    · rw [zero_mul]; exact (𝔟 p).zero_mem
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, k1, wittHyperbolic_projX_auxiliary_vectors a d hd hc, ← Matrix.mulVec_mulVec,
      Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add]
  · rw [Matrix.mulVec_diagonal]
    split_ifs
    · rw [zero_mul]; exact (𝔟 p).zero_mem
    · rw [one_mul]; exact hu p
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, k2, wittHyperbolic_projY_auxiliary_vectors a d hd hc, ← Matrix.mulVec_mulVec,
      Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add]

end SlopeTestRemainingChoices

end GlobalTheory.AscFin.BigProj

namespace GlobalTheory.AscFin

open GlobalTheory.AscFin.BigProj in

theorem pcBF_big_core : OnStd fun {D} _ _ {sc} {G} W F =>
    ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ w : WO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)),
      (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latRow G (2 * ρ + 1) →
      (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ w)) ∈ latBig G (2 * ρ + 1) ∧
      (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incY (F.V₀ ρ) ((F.dJ ρ h).pY ⬝ w)) ∈ latBig G (2 * ρ + 1) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h w hw
  have sdS : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have sdT : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (G.isV (X := .grid (2 * ρ + 1) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have sdB := ((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF).1 (2 * ρ + 1) (by omega)).2.2.2
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have big : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latO (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 1 + 1) 0) : Set _) (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True) := by
    have key := GlobalTheory.T.completedHomLattice_modulus_depth_mem_shift hq μ0 hL G (S := G.V (.grid (2 * ρ + 2) 0)) (B := G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 2) 0)) 1 (G.Λ (.grid (2 * ρ + 1) 0)) sdS (by rw [idLat_one]; exact sdT)
      (by rw [one_mul]; exact sdB) _ (by rw [idLat_one]; exact latO_negSp_le _ _ _ _ _ hw.1)
      ⟨e, he, by rw [idLat_one]; exact hw.2 e he⟩
    rw [one_mul] at key
    exact key
  have h1 : 1 ≤ 2 * ρ + 1 := by omega
  have h2 : 2 * ρ + 1 ≤ D.R.m := by omega
  have hlat : ∀ x ∈ G.Λ (.grid (2 * ρ + 1) 0), ((F.dJ ρ h).e * (F.dJ ρ h).qX) *ᵥ x ∈ G.Λ (.grid (2 * ρ + 1) 0) ∧
      ((F.dJ ρ h).e' * (F.dJ ρ h).qY) *ᵥ x ∈ G.Λ (.grid (2 * ρ + 1) 0) := by
    have e1 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) h1 h2).lat (G.sp.P (2 * ρ + 1)).lat
        (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := G.sp.colLat (2 * ρ + 1) h1 h2
    rw [e1]
    exact proj_lat _ _ (hF.hJ ρ h) (by omega) (hF.aJ ρ h) _ _
  have sdS' : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) := sdS
  have hx := GlobalTheory.T.rationalMatrix_sandwich_mem_completed_homLattice_selfDual sdS' sdS' sdB 1 ((F.dJ ρ h).e * (F.dJ ρ h).qX)
    (fun y hy => by rw [Matrix.one_mulVec]; exact hy) (idLat_mulVec _ _ _ fun x hx => (hlat x hx).1) _ big
  have hy := GlobalTheory.T.rationalMatrix_sandwich_mem_completed_homLattice_selfDual sdS' sdS' sdB 1 ((F.dJ ρ h).e' * (F.dJ ρ h).qY)
    (fun y hy => by rw [Matrix.one_mulVec]; exact hy) (idLat_mulVec _ _ _ fun x hx => (hlat x hx).2) _ big
  have hr1 : ∀ x : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank (G.V (.grid (2 * ρ + 2) 0)).rank, x ⬝ rat 1 = x := fun x => by
    rw [rat_one]; exact Matrix.mul_one x
  have ex : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ w)) =
      (rat ((F.dJ ρ h).e * (F.dJ ρ h).qX) ⬝ (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ⬝ rat 1 := by
    rw [hr1, rat_mul]
    simp only [HypDec.matrixExtendByZero_apply, HypDec.incX_apply, Matrix.mul_assoc]
    rfl
  have ey : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incY (F.V₀ ρ) ((F.dJ ρ h).pY ⬝ w)) =
      (rat ((F.dJ ρ h).e' * (F.dJ ρ h).qY) ⬝ (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ⬝ rat 1 := by
    rw [hr1, rat_mul]
    simp only [HypDec.matrixExtendByZero_apply, HypDec.incY_apply, Matrix.mul_assoc]
    rfl
  exact ⟨ex ▸ hx, ey ▸ hy⟩

end GlobalTheory.AscFin

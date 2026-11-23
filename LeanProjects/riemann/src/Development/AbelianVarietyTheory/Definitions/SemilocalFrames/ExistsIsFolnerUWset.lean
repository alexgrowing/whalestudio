import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.FormalDegreeBessel.FinalG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

variable {k r : ℕ}

theorem isUnit_det_Hpk : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

theorem isUnit_det_of_mem_GG {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det :=
  ((uHGroup _ _ isUnit_det_Hpk).2.2 g hg).1

theorem norm_det_of_mem_GG {g : Mat k r} (hg : g ∈ GG k r) : ‖g.det‖ = 1 := by
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h2
  have h3 : star g.det * g.det = 1 := by
    have h4 : (star g.det * g.det) * (Hpk k r).det = 1 * (Hpk k r).det := by
      rw [one_mul]; linear_combination h2
    exact (isUnit_det_Hpk (k := k) (r := r)).mul_right_cancel h4
  have h5 : Complex.normSq g.det = 1 := by
    have h6 := Complex.normSq_eq_conj_mul_self (z := g.det)
    rw [starRingEnd_apply, h3] at h6
    exact_mod_cast h6
  have h7 : ‖g.det‖ ^ 2 = 1 := by rw [Complex.sq_norm, h5]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h7

theorem IsClosedSub.isClosedSubgroup {S : Set (Mat k r)} (hS : IsClosedSub k r S) :
    Formalism.FourierDecayAlt.B2.IsClosedSubgroup S := by
  obtain ⟨hG, hc, h1, hm, hi⟩ := hS
  exact ⟨h1, hm, hi, fun a ha => isUnit_det_of_mem_GG (hG ha), hc⟩

theorem isClosedSub_of {S : Set (Mat k r)} (hS : Formalism.FourierDecayAlt.B2.IsClosedSubgroup S) (h : S ⊆ GG k r) :
    IsClosedSub k r S := by
  unfold IsClosedSub
  exact ⟨h, hS.closed, hS.one_mem, hS.mul_mem, hS.inv_mem⟩

theorem isClosedSub_GG : IsClosedSub k r (GG k r) :=
  isClosedSub_of (Formalism.FourierDecayAlt.P.unitary_group_closed k r) subset_rfl

theorem isClosedSub_Nset : IsClosedSub k r (Nset k r) :=
  isClosedSub_of (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) fun _ hg => hg.1

theorem isClosedSub_UWset (z : Fin (2 * r + k + 1) → ℂ) : IsClosedSub k r (UWset k r z) :=
  isClosedSub_of (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) fun _ hg => hg.1

private theorem inv_eq_Hpk_conjTranspose_of_mem_GG {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', (hpkFacts k r).2.1]

theorem isClosedSub_Sset {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) :
    IsClosedSub k r (Sset k r z) := by
  obtain ⟨h1, hmul, hinv⟩ := sGroup k r z hz
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have hK : IsCompact (UWset k r z) := Formalism.FourierDecayAlt.P.B2x3.compactW k r z hz hT
  have hsub : Sset k r z ⊆ GG k r := by
    rintro s ⟨h, hh, m, hm, rfl⟩
    exact (uHGroup _ _ isUnit_det_Hpk).2.1 h hh.1 m hm.1
  have hclosed : IsClosed (Sset k r z) := by
    have : CompactSpace (UWset k r z) := isCompact_iff_compactSpace.mp hK
    have hC : IsClosed {p : UWset k r z × Mat k r | Hpk k r * (p.1 : Mat k r)ᴴ * Hpk k r * p.2 ∈ Nset k r} :=
      IsClosed.preimage (f := fun p : UWset k r z × Mat k r => Hpk k r * (p.1 : Mat k r)ᴴ * Hpk k r * p.2)
        (((continuous_const.mul (continuous_subtype_val.comp continuous_fst).matrix_conjTranspose).mul
          continuous_const).mul continuous_snd) hN.closed
    have himg : Sset k r z =
        Prod.snd '' {p : UWset k r z × Mat k r | Hpk k r * (p.1 : Mat k r)ᴴ * Hpk k r * p.2 ∈ Nset k r} := by
      ext s
      constructor
      · rintro ⟨h, hh, m, hm, rfl⟩
        refine ⟨(⟨h, hh⟩, h * m), ?_, rfl⟩
        show Hpk k r * hᴴ * Hpk k r * (h * m) ∈ Nset k r
        rw [← inv_eq_Hpk_conjTranspose_of_mem_GG hh.1, ← Matrix.mul_assoc,
          Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_GG hh.1), Matrix.one_mul]
        exact hm
      · rintro ⟨⟨⟨h, hh⟩, s'⟩, hp, rfl⟩
        refine ⟨h, hh, Hpk k r * hᴴ * Hpk k r * s', hp, ?_⟩
        show s' = h * (Hpk k r * hᴴ * Hpk k r * s')
        rw [← inv_eq_Hpk_conjTranspose_of_mem_GG hh.1, ← Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ (isUnit_det_of_mem_GG hh.1), Matrix.one_mul]
    rw [himg]
    exact isClosedMap_snd_of_compactSpace _ hC
  unfold IsClosedSub
  exact ⟨hsub, hclosed, h1, hmul, hinv⟩

theorem haar_unimod_of_biinv {S : Set (Mat k r)} (hS : IsClosedSub k r S) {μ : Measure (Mt k r)}
    (h : Formalism.FourierDecayAlt.B.IsHaarOn S μ) : IsHaarOn S μ ∧ IsUnimod S μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  have hsf : SigmaFinite μ := inferInstance
  constructor
  · unfold Formalism.MainNotions.S.IsHaarOn
    exact ⟨hsf, h.ne_zero, h.conc, h.left⟩
  · unfold IsUnimod
    exact ⟨h.right, Formalism.FourierDecayAlt.P.haar_measure_inversion k r S μ hS.isClosedSubgroup h⟩

theorem exists_unimod_GG : ∃ μ : Measure (Mt k r), IsHaarOn (GG k r) μ ∧ IsUnimod (GG k r) μ := by
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  exact ⟨μ, haar_unimod_of_biinv isClosedSub_GG hμ⟩

def zStd (k r : ℕ) : Fin (2 * r + k + 1) → ℂ := bvec (wI k r (Fin.last k))

theorem Tz_zStd : Tz k r (zStd k r) = 1 := by
  have hH : herm (Hpk k r) (zStd k r) (zStd k r) =
      Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) := by
    simp [herm, zStd, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [Tz, hH]
  simp [Hpk, wI]

def detRep (k r m : ℕ) (h : Mat k r) : ℂ →L[ℂ] ℂ := h.det ^ m • ContinuousLinearMap.id ℂ ℂ

example : ∃ h ∈ UWset 1 0 (zStd 1 0), detRep 1 0 1 h 1 = -1 := by
  refine ⟨!![-1, 0; 0, 1], ⟨?_, fun a => a.elim0, ?_⟩, ?_⟩
  · show (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * Hpk 1 0 * !![-1, 0; 0, 1] = Hpk 1 0
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Hpk]
  · show (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ (Pi.single 1 1) = Pi.single 1 1
    ext i
    fin_cases i <;> simp
  · show (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ).det ^ 1 • (1 : ℂ) = -1
    simp

example : (1 : Mat 1 0) ∉ Greg 1 0 (zStd 1 0) (zStd 1 0) := by
  rintro ⟨-, -, h⟩
  apply h
  have h0 : Dmin 1 0 (zStd 1 0) (zStd 1 0) 1 ⟨0, by omega⟩ = 1 := by simp [Dmin]
  have hz : zStd 1 0 = ![0, 1] := by
    ext i
    fin_cases i <;> simp [zStd, bvec, wI]
  have h1 : Dmin 1 0 (zStd 1 0) (zStd 1 0) 1 (Fin.last 1) = -1 := by
    show Matrix.det (n := Fin 1) _ = _
    rw [Matrix.det_fin_one, hz]
    simp [Zhat, fvec, herm, Hpk, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  unfold Gf
  rw [h0, h1, Tz_zStd]
  simp

end GlobalTheory.SgInf

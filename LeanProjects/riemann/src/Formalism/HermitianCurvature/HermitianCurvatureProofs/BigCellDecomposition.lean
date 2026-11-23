import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellInversePair
import Formalism.FormalDegreeBessel.FinalG
import Formalism.FormalDegreeBessel.FinalBF

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellDecomposition

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.JF

def CellDecomp : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), ∀ g ∈ GV k r, (∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' g l ≠ 0) →
    ∃ n ∈ Nset k r, ∃ n' ∈ Nset k r, ∃ c : Fin r → ℂ, (∀ a, c a ≠ 0) ∧
      ∃ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, μᴴ * Hb k * μ = Hb k ∧ g = n⁻¹ * bigCell k r c μ * n'

variable {k r : ℕ}

theorem bigCell_one_fixes_vector {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin r → ℂ) : bigCell k r c 1 *ᵥ z = z := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  have key : ∀ j, bigCell k r c 1 i j * z j = if j = i then z i else 0 := by
    intro j
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj, mul_zero]
      split_ifs with h
      · subst h
        exact (hz _ hj).symm
      · rfl
    · have hj1 : ¬ j.val < r := by omega
      have hj2 : j.val ≤ r + k := by omega
      simp only [bigCell, dif_neg hj1, dif_pos hj2]
      by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · simp only [dif_pos hi, Matrix.one_apply]
        by_cases hij : j = i
        · subst hij
          simp
        · have hne : (⟨i.val - r, by omega⟩ : Fin (k + 1)) ≠ ⟨j.val - r, by omega⟩ := by
            intro h
            apply hij
            ext
            simp only [Fin.mk.injEq] at h
            omega
          simp [hne, hij]
      · simp only [dif_neg hi, zero_mul]
        rw [if_neg]
        rintro rfl
        omega
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  simp

theorem n_inv_S {z : Fin (2 * r + k + 1) → ℂ} {n : Mat k r} (hn : n ∈ Nset k r) : n⁻¹ ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw z, n⁻¹, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hn, (one_mul _).symm⟩

theorem n_S {z : Fin (2 * r + k + 1) → ℂ} {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw z, n, hn, (one_mul n).symm⟩

end Formalism.FourierDecayAlt.P.BigCellDecomposition

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.JF

theorem jf_psiOnto_of_cellDecomp (hCD : BigCellDecomposition.CellDecomp) : Formalism.FourierDecayAlt.JF.PsiOnto := by
  intro k r Wp Wq _ _ _ _ D g hg
  obtain ⟨n, hn, n', hn', c, hc, μ, hμ, rfl⟩ := hCD k r D.z D.z' g hg.1 hg.2.1
  set ζ := herm (Hb k) (μ *ᵥ wbPart k r D.z') (wbPart k r D.z) with hζdef
  have hmin := bigCellMinors k r D.z D.z' c μ D.z_mem D.z'_mem

  have hG : 0 < Gf k r D.z D.z' (bigCell k r c μ) := by
    have := hg.2.2
    rwa [gInv k r D.z D.z' D.z_mem D.z'_mem _ (BigCellDecomposition.n_inv_S hn) _ (BigCellDecomposition.n_S hn')] at this
  have hζ : Tz k r D.z * Tz k r D.z' < Complex.normSq ζ := by
    have hz := hmin.2.2 hc
    rw [BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem] at hz
    have hr := hmin.1 (Fin.last r)
    set P := Dmin k r D.z D.z' (bigCell k r c μ) ⟨r, by omega⟩ with hP
    have hP0 : P ≠ 0 := by
      have : P = ∏ a : Fin r with a.val < (Fin.last r).val, c a := hr
      rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
    have hlast : Dmin k r D.z D.z' (bigCell k r c μ) (Fin.last (r + 1)) = ζ * P := by
      unfold zeta at hz
      rw [← hP] at hz
      have h2 := div_mul_cancel₀ (Dmin k r D.z D.z' (bigCell k r c μ) (Fin.last (r + 1))) hP0
      rw [hz] at h2
      exact h2.symm
    unfold Gf at hG
    rw [hlast, ← hP, Complex.normSq_mul] at hG
    have h1 : 0 < Complex.normSq P := Complex.normSq_pos.2 hP0
    nlinarith

  have hfac := bruhat_big_cell_factorization k r c μ
  have huw := unipotent_weyl_properties k r
  have hm : embWb k r μ ∈ UWb k r := TwoByOneBlock.emb_mem_UWb hμ
  have hmz : herm (Hpk k r) (embWb k r μ *ᵥ D.z') D.z = ζ := by
    have e1 : embWb k r μ *ᵥ D.z' = bigCell k r c μ *ᵥ D.z' := by
      rw [hfac.2, ← Matrix.mulVec_mulVec, BigCellDecomposition.bigCell_one_fixes_vector D.z'_mem]
    rw [e1, BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem]
  obtain ⟨h, hh, h', hh', hmeq⟩ := b2_rank_one_coord k r D.z D.z' D.μsec D.k_pos D.z_mem D.z'_mem D.T_pos
    D.T'_pos D.sec (embWb k r μ) hm (by rw [hmz]; exact hζ)
  rw [hmz] at hmeq
  have hu1 := WeylGroupFacts.isUnit_of_uh hh.1
  have hu2 := WeylGroupFacts.isUnit_of_uh hh'.1
  have hun := WeylGroupFacts.isUnit_of_uh hn.1
  have hcomm : bigCell k r c 1 * h⁻¹ = h⁻¹ * bigCell k r c 1 :=
    (huw.2.2 c h⁻¹ (huw.2.1 D.z (BigCellInversePair.uw_inv hh))).symm

  refine ⟨((h, h * n * h⁻¹), (h', h' * n' * h'⁻¹)), ⟨hh,
      (uWNormal k r D.z D.z_mem h hh n hn).1, hh', (uWNormal k r D.z' D.z'_mem h' hh' n' hn').1⟩,
    (c, ζ), ⟨hc, hζ⟩, ?_⟩
  show n⁻¹ * bigCell k r c μ * n' = h⁻¹ * (h * n * h⁻¹)⁻¹ * bigCell k r c (D.μsec ζ) * (h' * n' * h'⁻¹) * h'
  rw [hfac.1, hmeq, (bruhat_big_cell_factorization k r c (D.μsec ζ)).1]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu1]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hu2, Matrix.mul_one]
  rw [← Matrix.mul_assoc (bigCell k r c 1) h⁻¹, hcomm]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hu1]

theorem jf_equivDet_of_cellDecomp (hCD : BigCellDecomposition.CellDecomp) : Formalism.FourierDecayAlt.JF.EquivDet :=
  Formalism.FourierDecayAlt.P.equiv_det_of_onto (jf_psiOnto_of_cellDecomp hCD)

end Formalism.FourierDecayAlt.P

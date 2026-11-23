import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClrHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylCharEqGtChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualWeylModuleInvRationalPointEqConjCharAt

noncomputable section

open Matrix Polynomial

namespace UpperTheory.Gal.CertificateRingHomMap

open UpperTheory.Gal.Schur in
private theorem den_eq {n : ℕ} (t : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => t i ^ (n - 1 - (j : ℕ))).det = vdm t := by
  have hm : (Matrix.of fun i j : Fin n => t i ^ (n - 1 - (j : ℕ))) =
      Matrix.projVandermonde (fun _ => (1 : ℂ)) t := by
    ext i j
    simp only [Matrix.projVandermonde_apply, one_pow, one_mul, Matrix.of_apply, Fin.val_rev]
    congr 1
    omega
  rw [hm, Matrix.det_projVandermonde]
  simp only [one_mul, vdm]

open UpperTheory.Gal.Schur in
private theorem num_eq' {n : ℕ} (l : Fin n → ℤ) (t : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => t i ^ (l j + (n - 1 - (j : ℕ) : ℕ))).det =
      altnZ (fun i => l i + n - 1 - (i : ℕ)) t := by
  rw [← Matrix.det_transpose]
  unfold altnZ
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  congr 1
  have := i.isLt
  omega

theorem pTrSch_of : TrSch := by
  intro n lam m hpos g t ht hchar
  obtain ⟨d, hd0, hdchar, htr⟩ := GlobalTheory.ContraChar.exists_eig lam g
  have key : ∀ e : Fin n → ℂ, (∏ i, (X - C (e i))).roots = Multiset.map e Finset.univ.val := by
    intro e
    have he : (∏ i, (X - C (e i))) = ((Finset.univ.val.map e).map fun a => X - C a).prod := by
      rw [Multiset.map_map]
      rfl
    rw [he, Polynomial.roots_multiset_prod_X_sub_C]
  have hroots : Multiset.map d Finset.univ.val = Multiset.map t Finset.univ.val := by
    rw [← key d, ← key t, ← hdchar, ← hchar]
  obtain ⟨π, hπ⟩ := GlobalTheory.ContraChar.exists_perm_of_map_eq d t hroots
  have ht0 : ∀ i, t i ≠ 0 := fun i => by rw [← hπ i]; exact hd0 _
  have hgt : ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar n lam.w t = ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar n lam.w d := by
    rw [← GlobalTheory.ContraChar.gtChar_perm lam d hd0 π]
    congr 1
    funext i
    exact (hπ i).symm
  have hw := GlobalTheory.CompanionTheory.RmCharacter.weylChar_eq_gtChar lam.w lam.anti t ht0 ht
  rw [htr, ← hgt, ← hw]
  unfold PositivityTheory.RgBcC.weylChar
  rw [num_eq' lam.w t, den_eq t]
  rw [UpperTheory.Gal.Schur.WeylTie_holds ℂ n lam.w m (fun i => (lam.w i + m).toNat) t
    (fun i => (Int.toNat_of_nonneg (hpos i)).symm) ht ht0]
  have hp : (∏ k, t k) ^ m ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun i _ => ht0 i)
  exact div_mul_cancel₀ _ hp

end UpperTheory.Gal.CertificateRingHomMap

end

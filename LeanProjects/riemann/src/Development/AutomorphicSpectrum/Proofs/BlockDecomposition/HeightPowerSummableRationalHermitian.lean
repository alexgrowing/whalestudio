import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLeftInvariantRationalParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HermSum

open GlobalTheory.StdUnn.Model (submatrix_fromBlocks_mul block_matrix_one)

theorem mat_mul_block_decomposition {D : D7} {n : ℕ} (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem weyl_mul_inv {R : Type} [CommRing R] {k : ℕ} :
    blk4 (0 : Matrix (Fin k) (Fin k) R) 1 (-1) 0 * blk4 0 (-1) 1 0 = 1 := by
  rw [submatrix_fromBlocks_mul]
  simp [block_matrix_one]

theorem weyl_conj {R : Type} [CommRing R] {k : ℕ} (d : Matrix (Fin k) (Fin k) R) :
    blk4 (0 : Matrix (Fin k) (Fin k) R) 1 (-1) 0 * blk4 1 d 0 1 * blk4 0 (-1) 1 0 = blk4 1 0 (-d) 1 := by
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp

private theorem mat_one_eq_one {D : D7} {n : ℕ} : mat (1 : G D n) = 1 := by
  simp only [GlobalTheory.StdUnn.mat, map_one, Units.val_one]

private theorem mat_inv_eq_of_mat_mul_eq_one {D : D7} {n : ℕ} (g : G D n) (M : Mx D (n + n) (n + n))
    (h : mat g * M = 1) : mat g⁻¹ = M := by
  have h1 : mat g⁻¹ * mat g = 1 := by rw [← mat_mul_block_decomposition, inv_mul_cancel, mat_one_eq_one]
  calc mat g⁻¹ = mat g⁻¹ * (mat g * M) := by rw [h, mul_one]
    _ = M := by rw [← mul_assoc, h1, one_mul]

private theorem blk4_apply_inr_inl {R : Type} {k : ℕ} (a b c d : Matrix (Fin k) (Fin k) R) (i j : Fin k) :
    blk4 a b c d (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = c i j := by
  show (Matrix.fromBlocks a b c d).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
    (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = c i j
  rw [Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁]

private theorem mulVec_single_one_apply' {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R)
    (i j : Fin m) : (M *ᵥ Pi.single j 1) i = M i j := by
  simp [Matrix.mulVec]

private theorem eq_zero_of_mem_P_of_mat_eq_blk4 {D : D7} {n : ℕ} (x : G D n) (hx : x ∈ P D n)
    (d : Mx D n n) (hd : mat x = blk4 1 0 (-d) 1) : d = 0 := by
  have key : ∀ v : Fin (n + n) → AE D,
      v ∈ GlobalTheory.StdUnn.upperHalf D n ↔ (mat x).mulVec v ∈ GlobalTheory.StdUnn.upperHalf D n := hx
  refine Matrix.ext fun i j => ?_
  have hv : (Pi.single (finSumFinEquiv (Sum.inl j)) 1 : Fin (n + n) → AE D) ∈
      GlobalTheory.StdUnn.upperHalf D n := by
    rw [GlobalTheory.StdUnn.upperHalf, LinearMap.mem_ker]
    ext l
    rw [LinearMap.funLeft_apply, Pi.zero_apply, Pi.single_eq_of_ne]
    exact fun h => Sum.inr_ne_inl (finSumFinEquiv.injective h)
  have h2 := (key _).1 hv
  rw [hd, GlobalTheory.StdUnn.upperHalf, LinearMap.mem_ker] at h2
  have h3 := congrFun h2 i
  rw [LinearMap.funLeft_apply, Pi.zero_apply, mulVec_single_one_apply', blk4_apply_inr_inl, Matrix.neg_apply,
    neg_eq_zero] at h3
  rw [h3, Matrix.zero_apply]

theorem summable_height_rpow : ∀ (D : D7) (ρ : ℕ) (H : G D ρ → ℝ≥0), IsHt H → ∀ (w : G D ρ) (nb : hermA D ρ → G D ρ),
  mat w = blk4 0 1 (-1) 0 → (∀ z : hermA D ρ, mat (nb z) = blk4 1 z.1 0 1) → ∀ τ : ℝ, (ρ : ℝ) < τ →
    Summable (fun ζ : ratHerm D ρ => (H (w * nb ζ.1) : ℝ) ^ τ) := by
  intro D ρ H hH w nb hw hnb τ hτ
  have hτ0 : 0 ≤ τ := le_trans (Nat.cast_nonneg ρ) hτ.le
  set Φ : G D ρ → ℂ := fun g => (((H g : ℝ) ^ τ : ℝ) : ℂ) with hΦ
  set s₁ : ℂ := ((τ - (ρ : ℝ) / 2 : ℝ) : ℂ) with hs₁
  have hlaw : PositivityTheory.Rg.Rsw.IsLaw 1 s₁ Φ := by
    intro q hq a ha g
    have e1 := hH.2.2 q hq a ha g
    have e2 : s₁ + (ρ : ℂ) / 2 = (τ : ℂ) := by
      rw [hs₁]
      push_cast
      ring
    rw [e2]
    simp only [hΦ, e1, MonoidHom.one_apply, OneMemClass.coe_one, NNReal.coe_mul, GlobalTheory.Doubling.npow]
    rw [Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), Complex.ofReal_mul,
      ← Complex.ofReal_cpow (NNReal.coe_nonneg _)]
    simp
  have hcont : Continuous Φ := by
    have hH' : Continuous fun g => (H g : ℝ) := NNReal.continuous_coe.comp hH.1
    exact Complex.continuous_ofReal.comp (hH'.rpow_const fun _ => Or.inr hτ0)
  have hre : (ρ : ℝ) / 2 < s₁.re := by
    rw [hs₁, Complex.ofReal_re]
    linarith
  have hconv := GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law D ρ 1 s₁ Φ hcont hlaw hre 1
  have hHecke : Formalism.L2.Theta.IsHeckeChar D 1 :=
    ⟨by
      have h1 : (⇑(1 : (AE D)ˣ →* Circle)) = fun _ => 1 := funext fun _ => MonoidHom.one_apply _
      rw [h1]
      exact continuous_const, fun _ => MonoidHom.one_apply _⟩
  have hinv := GlobalTheory.CompanionTheory.FJE.leftInv_of_isLaw (1 : (AE D)ˣ →* Circle) s₁ Φ hHecke hlaw
  have hWr : mat w = GlobalTheory.MixModel.rat (blk4 (0 : Matrix (Fin ρ) (Fin ρ) D.host.E) 1 (-1) 0) := by
    rw [hw, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_zero', GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_neg',
      GlobalTheory.CompanionTheory.PcB.rat_one']
  have hwinv : mat w⁻¹ = blk4 0 (-1) 1 0 := by
    apply mat_inv_eq_of_mat_mul_eq_one
    rw [hw]
    exact weyl_mul_inv
  have hWr' : mat w⁻¹ = GlobalTheory.MixModel.rat (blk4 (0 : Matrix (Fin ρ) (Fin ρ) D.host.E) (-1) 1 0) := by
    rw [hwinv, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_zero', GlobalTheory.CompanionTheory.PcB.rat_neg', GlobalTheory.CompanionTheory.PcB.rat_one']
  have hwmem : w ∈ GF D ρ := GlobalTheory.CompanionTheory.PcB.mem_GF w _ _ hWr hWr'
  have hrat : ∀ ζ : ratHerm D ρ, ∃ Z : Matrix (Fin ρ) (Fin ρ) D.host.E,
      GlobalTheory.MixModel.rat Z = ((ζ.1 : hermA D ρ) : Mx D ρ ρ) := by
    intro ζ
    obtain ⟨Z, hZ⟩ := AddMonoidHom.mem_range.mp (AddSubgroup.mem_comap.mp ζ.2)
    exact ⟨Z, hZ⟩
  have hnbinv : ∀ ζ : ratHerm D ρ, mat (nb ζ.1)⁻¹ = blk4 1 (-((ζ.1 : hermA D ρ) : Mx D ρ ρ)) 0 1 := by
    intro ζ
    apply mat_inv_eq_of_mat_mul_eq_one
    rw [hnb, GlobalTheory.CompanionTheory.PcB.block_unipotent_mul, add_neg_cancel, block_matrix_one]
  have hnbmem : ∀ ζ : ratHerm D ρ, nb ζ.1 ∈ GF D ρ := by
    intro ζ
    obtain ⟨Z, hZ⟩ := hrat ζ
    refine GlobalTheory.CompanionTheory.PcB.mem_GF _ (blk4 1 Z 0 1) (blk4 1 (-Z) 0 1) ?_ ?_
    · rw [hnb, ← hZ, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_zero']
    · rw [hnbinv, ← hZ, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_zero',
        GlobalTheory.CompanionTheory.PcB.rat_neg']
  set x : ratHerm D ρ → GF D ρ := fun ζ => ⟨w * nb ζ.1, mul_mem hwmem (hnbmem ζ)⟩ with hx
  set ι : ratHerm D ρ → GlobalTheory.Eis.Cosets (P D ρ) (GF D ρ) :=
    fun ζ => Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (x ζ) with hι
  have hinj : Function.Injective ι := by
    intro ζ ζ' h
    have h0 : Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (x ζ) =
        Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (x ζ') := h
    have h1 : x ζ' * (x ζ)⁻¹ ∈ (P D ρ).subgroupOf (GF D ρ) :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact h0)
    have h2 : (w * nb ζ'.1) * (w * nb ζ.1)⁻¹ ∈ P D ρ := Subgroup.mem_subgroupOf.mp h1
    have hm : mat ((w * nb ζ'.1) * (w * nb ζ.1)⁻¹) =
        blk4 1 0 (-(((ζ'.1 : hermA D ρ) : Mx D ρ ρ) + -((ζ.1 : hermA D ρ) : Mx D ρ ρ))) 1 := by
      rw [mul_inv_rev, mat_mul_block_decomposition, mat_mul_block_decomposition, mat_mul_block_decomposition, hw, hnb, hwinv, hnbinv ζ, ← mul_assoc,
        mul_assoc (blk4 0 1 (-1) 0), GlobalTheory.CompanionTheory.PcB.block_unipotent_mul]
      exact weyl_conj _
    have h3 := eq_zero_of_mem_P_of_mat_eq_blk4 _ h2 _ hm
    exact Subtype.ext (Subtype.ext (add_neg_eq_zero.mp h3).symm)
  have hterm : ∀ ζ : ratHerm D ρ,
      ‖GlobalTheory.Eis.term (P D ρ) (GF D ρ) Φ 1 (ι ζ)‖ = (H (w * nb ζ.1) : ℝ) ^ τ := by
    intro ζ
    have ho : Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (Quotient.out (ι ζ)) =
        Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (x ζ) := Quotient.out_eq (ι ζ)
    have hrel : x ζ * (Quotient.out (ι ζ))⁻¹ ∈ (P D ρ).subgroupOf (GF D ρ) :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact ho)
    have hγ : Quotient.out (ι ζ) * (x ζ)⁻¹ ∈ (P D ρ).subgroupOf (GF D ρ) := by
      have h4 := inv_mem hrel
      rwa [mul_inv_rev, inv_inv] at h4
    have hγP : ((Quotient.out (ι ζ) * (x ζ)⁻¹ : GF D ρ) : G D ρ) ∈ P D ρ ⊓ GF D ρ :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hγ, (Quotient.out (ι ζ) * (x ζ)⁻¹).2⟩
    have hsplit : ((Quotient.out (ι ζ) : GF D ρ) : G D ρ) * 1 =
        ((Quotient.out (ι ζ) * (x ζ)⁻¹ : GF D ρ) : G D ρ) * ((x ζ : GF D ρ) : G D ρ) := by
      rw [mul_one, ← Subgroup.coe_mul, inv_mul_cancel_right]
    show ‖Φ (((Quotient.out (ι ζ) : GF D ρ) : G D ρ) * 1)‖ = _
    rw [hsplit, hinv _ hγP]
    show ‖(((H (w * nb ζ.1) : ℝ) ^ τ : ℝ) : ℂ)‖ = (H (w * nb ζ.1) : ℝ) ^ τ
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
  have hsum : Summable (fun q => ‖GlobalTheory.Eis.term (P D ρ) (GF D ρ) Φ 1 q‖) := hconv
  exact (hsum.comp_injective hinj).congr hterm

end GlobalTheory.CompanionTheory.HermSum

end

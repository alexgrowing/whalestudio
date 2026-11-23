import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupIsoGLStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralKeepsDoublingDiagonalAdicCompletio
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubledUnitaryChartSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormCmExtensionSplitPlaceEqZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAndIwasawaOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalPreservingInSiegelParabolicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicModulusCharacterStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)

noncomputable section

namespace GlobalTheory.SplitHgtDbl

theorem isSplitBasis_sumLat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)), IsSplitBasis t L b → IsSplitBasis t (sumLat finSumFinEquiv L L) (blkGL finSumFinEquiv (b, b)) := by
  intro F E _ _ _ _ _ n L v t b hb
  have key : ∀ x y : Fin n → Fv F v, pairVec finSumFinEquiv x y ∈ splitLat t (sumLat finSumFinEquiv L L) ↔
      x ∈ splitLat t L ∧ y ∈ splitLat t L := by
    intro x y
    simp only [mem_splitLat, latLoc_sumLat]
    constructor
    · rintro ⟨z, hz, hzu⟩
      rw [← pairVec_eta finSumFinEquiv z, pairVec_mem_sumLat] at hz
      refine ⟨⟨_, hz.1, funext fun i => ?_⟩, ⟨_, hz.2, funext fun i => ?_⟩⟩
      · have := congrFun hzu (finSumFinEquiv (.inl i))
        simp only [splitVec, pairVec_inl] at this
        exact this
      · have := congrFun hzu (finSumFinEquiv (.inr i))
        simp only [splitVec, pairVec_inr] at this
        exact this
    · rintro ⟨⟨z₁, h₁, rfl⟩, ⟨z₂, h₂, rfl⟩⟩
      refine ⟨pairVec finSumFinEquiv z₁ z₂, (pairVec_mem_sumLat _).2 ⟨h₁, h₂⟩, funext fun j => ?_⟩
      obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective j <;> simp only [splitVec, pairVec_inl, pairVec_inr]
  intro u
  rw [← pairVec_eta finSumFinEquiv u, val_blkGL, blkMat_mulVec, key, ← hb, ← hb, ← finSumFinEquiv.forall_congr_right,
    Sum.forall]
  simp only [pairVec_inl, pairVec_inr]

theorem locMat_io {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n : ℕ} {X : Spc F E n} {X₂ : Spc F E (n + n)} {i : UA σ X.J × UA σ X.J →* UA σ X₂.J}
    {K₂ : Subgroup (UA σ X₂.J)} (hD : IsDbl B X X₂ i K₂) {v : Pl F} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v))
    (g : UA σ X.J) :
    GlobalTheory.KSplit.locMat t (blkGL finSumFinEquiv (b, b)) (i (g, 1)) = blkGL finSumFinEquiv (GlobalTheory.KSplit.locMat t b g, 1) := by
  apply Units.ext
  rw [GlobalTheory.KSplit.locMat_val, hD.emb, ← map_inv, Prod.inv_mk, val_blkGL, val_blkGL, val_blkGL, GlobalTheory.KSplit.locMat_val,
    blkMat_map _ _ (map_zero _), blkMat_mul, blkMat_mul, GlobalTheory.StabHaar.mat_one, Matrix.map_one _ (map_zero _) (map_one _)]
  simp

theorem io_mem_UAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n : ℕ} {X : Spc F E n} {X₂ : Spc F E (n + n)} {i : UA σ X.J × UA σ X.J →* UA σ X₂.J}
    {K₂ : Subgroup (UA σ X₂.J)} (hD : IsDbl B X X₂ i K₂) {v : Pl F} {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) :
    i (g, 1) ∈ UAt σ X₂ (evFin F v) := by
  intro u hu
  have h1 : ∀ a c, u • (mat g a c - (1 : Matrix (Fin n) (Fin n) (AE F E)) a c) = 0 := fun a c => by
    simpa using congrFun (congrFun (hg u hu) a) c
  rw [hD.emb, GlobalTheory.StabHaar.mat_one, show (1 : Matrix (Fin (n + n)) (Fin (n + n)) (AE F E)) =
    blkMat finSumFinEquiv 1 1 from (blkMat_one _).symm]
  ext a c
  obtain ⟨a | a, rfl⟩ := finSumFinEquiv.surjective a <;> obtain ⟨c | c, rfl⟩ := finSumFinEquiv.surjective c <;>
    simp only [blkMat, Matrix.smul_apply, Matrix.sub_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, sub_self, smul_zero, h1]

theorem hgt_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)), IsSplitBasis t X.L b →
    ∀ (ϖ : (Fv F v)ˣ), IsUnifV F v ϖ.1 → ∀ (e : Fin n → ℤ) (T : GL (Fin n) (Fv F v)), T.1 = Matrix.diagonal (fun i => ϖ.1 ^ e i) → ∀ k₁ ∈ KGL v n, ∀ k₂ ∈ KGL v n,
    ∀ g ∈ UAt σ X (evFin F v), GlobalTheory.KSplit.locMat t b g = k₁ * T * k₂ →
      ((hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (g, 1)) : ℝ≥0) : ℝ) = (qV F v : ℝ) ^ (-∑ j, |e j|) := by
  intro F E _ _ _ _ _ σ B n X r s hB hX X₂ i K₂ hD v t b hb ϖ hϖ e T hT k₁ hk₁ k₂ hk₂ g hg hgT
  have hcm := hB.cm
  have hJ : X.J.det ≠ 0 := GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hX
  have hND₂ : IsHermND σ X₂.J := hD.gram ▸ GlobalTheory.LFun.DblSplit.isHermND_dbl σ ⟨hX.herm, hJ⟩
  haveI := hX.lat
  have hLat₂ : X₂.L.IsLattice E := by rw [hD.lat]; infer_instance
  have hQt : X₂.Jᵀ = dblGram finSumFinEquiv X.Jᵀ := by rw [hD.gram, GlobalTheory.DblIwasawa.transpose_dblGram]
  have hSD₂ : IsSelfDualAt σ X₂.Jᵀ X₂.L v := by
    rw [hD.lat]
    exact isSelfDualAt_dbl hQt (GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B n X r s hB hX v)
  have hb₂ : IsSplitBasis t X₂.L (blkGL finSumFinEquiv (b, b)) := by
    rw [hD.lat]; exact GlobalTheory.SplitHgtDbl.isSplitBasis_sumLat F E n X.L v t b hb
  obtain ⟨e₂, he₂, heK⟩ := GlobalTheory.T.local_unitary_group_iso_GL F E σ B (n + n) X₂ hcm hND₂ hLat₂ v hSD₂ K₂ hD.stab t _ hb₂
  obtain ⟨κ, hκ, hkeep, hl, hq⟩ := GlobalTheory.GraphShear.graph_shear F v n ϖ.1 hϖ e T k₁ k₂ hT hk₁ hk₂
  let y : UAtSub σ X₂ (evFin F v) := ⟨i (g, 1), io_mem_UAt hD hg⟩
  let p : UAtSub σ X₂ (evFin F v) := y * e₂.symm κ
  have hk : (e₂.symm κ).1 ∈ K₂ := (heK _).2 (by rw [e₂.apply_symm_apply]; exact hκ)
  have hep : e₂ p = blkGL finSumFinEquiv (k₁ * T * k₂, 1) * κ := by
    rw [map_mul, e₂.apply_symm_apply, he₂]
    change GlobalTheory.KSplit.locMat t _ (i (g, 1)) * κ = _
    rw [locMat_io hD t b g, hgT]
  have hM : (mat p.1).map (piW t) =
      ((blkGL finSumFinEquiv (b⁻¹, b⁻¹))⁻¹ * e₂ p * blkGL finSumFinEquiv (b⁻¹, b⁻¹)).1 := by
    have hc : blkGL finSumFinEquiv (b⁻¹, b⁻¹) = (blkGL finSumFinEquiv (b, b))⁻¹ := by
      rw [← map_inv, Prod.inv_mk]
    rw [hc, inv_inv, he₂, Units.val_mul, Units.val_mul, GlobalTheory.KSplit.locMat_val]
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Units.mul_inv_cancel_left]
  have hkeep' : KeepsDiag finSumFinEquiv ((mat p.1).map (piW t)) := by
    rw [hM]; exact (GlobalTheory.LFun.DblSplit.keepsDiag_conj_iff _ _ _).2 (by rw [hep]; exact hkeep)
  have hp := GlobalTheory.T.diagonal_preserving_in_siegel_parabolic F E σ hcm n X.J X₂ hJ hD.gram v t p.1 p.2 hkeep'
  have habs := GlobalTheory.T.siegel_parabolic_modulus_character F E σ hcm n X.J X₂ hJ hD.gram v t p.1 p.2 hp
  have hio : i (g, 1) = (⟨p.1, hp⟩ : siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype).1 * ((e₂.symm κ).1)⁻¹ := by
    change _ = (y.1 * (e₂.symm κ).1) * _
    rw [mul_inv_cancel_right]
  rw [hio, hD.iwa.hgtOf_mul _ (inv_mem hk), habs, hM, GlobalTheory.LFun.DblSplit.det_leviMat_conj _ _ (by rw [hep]; exact hkeep),
    GlobalTheory.LFun.DblSplit.det_quotMat_conj _ _ (by rw [hep]; exact hkeep), hep, hl, hq]
  congr 1
  rw [← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [abs_eq_max_neg]; omega

end GlobalTheory.SplitHgtDbl

end

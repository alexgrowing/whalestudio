import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecompDec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecompLie

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

variable {k r : ℕ}

lemma block_embedding_mul_embed (g X : Mb k) : embWb k r g * e0 k r X = e0 k r (g * X) := by
  rw [emb_eq]
  unfold e0
  rw [Matrix.add_mul]
  have h1 : Em k r * g * (Em k r)ᵀ * (Em k r * X * (Em k r)ᵀ) = Em k r * (g * X) * (Em k r)ᵀ := by
    calc Em k r * g * (Em k r)ᵀ * (Em k r * X * (Em k r)ᵀ) = Em k r * g * ((Em k r)ᵀ * Em k r) * X * (Em k r)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = Em k r * (g * X) * (Em k r)ᵀ := by rw [EmT_Em]; simp only [Matrix.mul_assoc, Matrix.one_mul]
  have h2 : (1 - Em k r * (Em k r)ᵀ) * (Em k r * X * (Em k r)ᵀ) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Q_Em, Matrix.zero_mul, Matrix.zero_mul]
  rw [h1, h2, add_zero]

lemma embed_mul_block_embedding (g X : Mb k) : e0 k r X * embWb k r g = e0 k r (X * g) := by
  rw [emb_eq]
  unfold e0
  rw [Matrix.mul_add]
  have h1 : Em k r * X * (Em k r)ᵀ * (Em k r * g * (Em k r)ᵀ) = Em k r * (X * g) * (Em k r)ᵀ := by
    calc Em k r * X * (Em k r)ᵀ * (Em k r * g * (Em k r)ᵀ) = Em k r * X * ((Em k r)ᵀ * Em k r) * g * (Em k r)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = Em k r * (X * g) * (Em k r)ᵀ := by rw [EmT_Em]; simp only [Matrix.mul_assoc, Matrix.one_mul]
  have h2 : Em k r * X * (Em k r)ᵀ * (1 - Em k r * (Em k r)ᵀ) = 0 := by
    rw [Matrix.mul_assoc, EmT_Q, Matrix.mul_zero]
  rw [h1, h2, add_zero]

lemma single_wI (a b : Fin (k + 1)) : Matrix.single (wI k r a) (wI k r b) (1 : ℂ) = e0 k r (Su k a b) := by
  have hE : ∀ c : Fin (k + 1), Em k r *ᵥ Pi.single c 1 = Pi.single (wI k r c) 1 := by
    intro c
    funext i
    rw [Matrix.mulVec_single_one]
    show Em k r i c = _
    rw [Em, Pi.single_apply]
  unfold e0 Su
  rw [Matrix.single_eq_single_vecMulVec_single, Matrix.single_eq_single_vecMulVec_single, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hE, hE]

def LS (k : ℕ) (p : Fin (k + 1) × Fin (k + 1)) : Mb k :=
  if p.1 = Fin.last k ∨ p.2 = Fin.last k then 0 else Su k p.1 p.2

lemma inL_LS (p : Fin (k + 1) × Fin (k + 1)) : InL k (LS k p) := by
  unfold LS
  split_ifs with h
  · exact inL_zero
  · exact inL_Su (not_or.1 h).1 (not_or.1 h).2

lemma sum_LS {n : ℕ} (e : Fin (k + 1) × Fin (k + 1) ≃ Fin n) (C : Mb k) (hC : InL k C) :
    ∑ t : Fin n, C (e.symm t).1 (e.symm t).2 • LS k (e.symm t) = C := by
  rw [e.symm.sum_comp (fun p => C p.1 p.2 • LS k p), Fintype.sum_prod_type]
  conv_rhs => rw [Matrix.matrix_eq_sum_single C]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold LS
  split_ifs with h
  · have : C i j = 0 := by
      rcases h with h | h
      · have h' : i = Fin.last k := h
        rw [h']; exact (hC j).2
      · have h' : j = Fin.last k := h
        rw [h']; exact (hC i).1
    rw [this, zero_smul, Matrix.single_zero]
  · unfold Su
    rw [Matrix.smul_single, smul_eq_mul, mul_one]

lemma embed_conj_finset_sum {n : ℕ} (g h : Mb k) (c : Fin n → ℂ) (X : Fin n → Mb k) :
    ∑ t, c t • e0 k r (g * X t * h) = e0 k r (g * (∑ t, c t • X t) * h) := by
  unfold e0
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

lemma ringSpec_normalisedCharacter_eq (z z' : Fin (2 * r + k + 1) → ℂ) (ζ : ℂ) :
    mu0 k r z z' ζ = embWb k r (gA k (wbPart k r z) (Tz k r z) * nu k (wZ (Tz k r z) (Tz k r z') ζ) (sZ (Tz k r z) (Tz k r z') ζ) *
      gB k (wbPart k r z') (Tz k r z')) := rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2 Dc

noncomputable section

theorem radial_decomposition_holds : Decomp := by
  intro k r z z' hk hz hz' hT hT' a b
  have h0 : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  obtain ⟨hA, -⟩ := gA_spec k hT (herm_self k r z hz)
  obtain ⟨hB, -⟩ := gB_spec k hT' (herm_self k r z' hz')
  set T := Tz k r z with hTd
  set T' := Tz k r z' with hTd'
  set ga := gA k (wbPart k r z) T with hga
  set gb := gB k (wbPart k r z') T' with hgb
  have iA : ga⁻¹ * ga = 1 := unit_inv_mul hA
  have iB : gb⁻¹ * gb = 1 := unit_inv_mul hB
  obtain ⟨C₁, C₂, β₁, β₂, c1, c2, c3, c4, c5⟩ := dec_all (T := T) (T' := T') h0 hT hT' (gb * Su k a b * gb⁻¹)
  let e := Fintype.equivFin (Fin (k + 1) × Fin (k + 1))
  refine ⟨_, _, fun t => e0 k r (gb⁻¹ * LS k (e.symm t) * gb), fun t ζ => C₁ ζ (e.symm t).1 (e.symm t).2,
    fun t => e0 k r (ga * LS k (e.symm t) * ga⁻¹), fun t ζ => C₂ ζ (e.symm t).1 (e.symm t).2, β₁, β₂,
    fun t => gwc_right k r z' hz' hT' _ (inL_LS _), fun t => gwc_left k r z hz hT _ (inL_LS _),
    fun t => c1.1 _ _, fun t => c2.1 _ _, c3, c4, fun ζ hζ => ?_⟩
  have hν := nuI_mul (k := k) h0 hT hT' hζ
  set ν := nu k (wZ T T' ζ) (sZ T T' ζ) with hνd
  set νi := nuI k T T' ζ with hνi
  have hmu : mu0 k r z z' ζ = embWb k r (ga * ν * gb) := ringSpec_normalisedCharacter_eq z z' ζ
  have hinv : (mu0 k r z z' ζ)⁻¹ = embWb k r (gb⁻¹ * νi * ga⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [hmu, ← emb_mul]
    have : gb⁻¹ * νi * ga⁻¹ * (ga * ν * gb) = gb⁻¹ * (νi * ((ga⁻¹ * ga) * ν)) * gb := by simp only [Matrix.mul_assoc]
    rw [this, iA, Matrix.one_mul, hν, Matrix.mul_one, iB, emb_one]
  have s1 : ∑ t, C₁ ζ (e.symm t).1 (e.symm t).2 • e0 k r (gb⁻¹ * LS k (e.symm t) * gb) = e0 k r (gb⁻¹ * C₁ ζ * gb) := by
    rw [embed_conj_finset_sum, sum_LS e _ (c1.2 ζ)]
  have s2 : ∑ t, C₂ ζ (e.symm t).1 (e.symm t).2 • e0 k r (ga * LS k (e.symm t) * ga⁻¹) = e0 k r (ga * C₂ ζ * ga⁻¹) := by
    rw [embed_conj_finset_sum, sum_LS e _ (c2.2 ζ)]
  have s3 : (mu0 k r z z' ζ)⁻¹ * e0 k r (ga * C₂ ζ * ga⁻¹) * mu0 k r z z' ζ = e0 k r (gb⁻¹ * (νi * C₂ ζ * ν) * gb) := by
    rw [hinv, hmu, block_embedding_mul_embed, embed_mul_block_embedding]
    congr 1
    have : gb⁻¹ * νi * ga⁻¹ * (ga * C₂ ζ * ga⁻¹) * (ga * ν * gb) =
        gb⁻¹ * (νi * ((ga⁻¹ * ga) * C₂ ζ * (ga⁻¹ * ga)) * ν) * gb := by simp only [Matrix.mul_assoc]
    rw [this, iA, Matrix.one_mul, Matrix.mul_one]
  have s4 : etaZ k r z z' ζ = e0 k r (gb⁻¹ * H1 k T T' ζ * gb) := by
    unfold etaZ
    rw [dmu_eq k r z z' hT hT' ζ hζ, hinv, block_embedding_mul_embed]
    congr 1
    unfold H1
    have : ∀ D : Mb k, gb⁻¹ * νi * ga⁻¹ * (ga * D * gb) = gb⁻¹ * (νi * ((ga⁻¹ * ga) * D)) * gb := by
      intro D; simp only [Matrix.mul_assoc]
    rw [this, iA, Matrix.one_mul]
  have s5 : etaZb k r z z' ζ = e0 k r (gb⁻¹ * H2 k T T' ζ * gb) := by
    unfold etaZb
    rw [dmub_eq k r z z' hT hT' ζ hζ, hinv, block_embedding_mul_embed]
    congr 1
    unfold H2
    have : ∀ D : Mb k, gb⁻¹ * νi * ga⁻¹ * (ga * D * gb) = gb⁻¹ * (νi * ((ga⁻¹ * ga) * D)) * gb := by
      intro D; simp only [Matrix.mul_assoc]
    rw [this, iA, Matrix.one_mul]
  have s6 : Su k a b = gb⁻¹ * (gb * Su k a b * gb⁻¹) * gb := by
    have : gb⁻¹ * (gb * Su k a b * gb⁻¹) * gb = (gb⁻¹ * gb) * Su k a b * (gb⁻¹ * gb) := by simp only [Matrix.mul_assoc]
    rw [this, iB, Matrix.one_mul, Matrix.mul_one]
  rw [s1, s2, s3, s4, s5, single_wI, s6, c5 ζ hζ, ← embed_smul, ← embed_smul, ← embed_add, ← embed_add, ← embed_add]
  congr 1
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

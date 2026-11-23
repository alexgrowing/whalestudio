import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagMemDoubledVacuumLatticeStabilizer
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacSplitConj

open GlobalTheory.DblVac Matrix

local notation:70 A:70 " ⬝ₘ " B:71 => @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

section Alg

variable {A : Type} [CommRing A] {d : ℕ}

def swapM (d : ℕ) (a b : A) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) A :=
  fromBlocks 1 ((-b) • 1) (a • 1) ((1 - 2 * (a + b)) • 1)

theorem swapM_mul_self {a b : A} (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0) :
    swapM d a b * swapM d a b = 1 := by
  rw [swapM, fromBlocks_multiply, ← fromBlocks_one]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  congr 1
  · linear_combination (norm := module) (-hab) • (1 : Matrix (Fin d) (Fin d) A)
  · linear_combination (norm := module) (2 * hab + 2 * hb) • (1 : Matrix (Fin d) (Fin d) A)
  · linear_combination (norm := module) (-2 * hab - 2 * ha) • (1 : Matrix (Fin d) (Fin d) A)
  · linear_combination (norm := module) (7 * hab + 4 * ha + 4 * hb) • (1 : Matrix (Fin d) (Fin d) A)

theorem swapM_unitary {a b : A} (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0) (J : Matrix (Fin d) (Fin d) A) :
    (swapM d a b)ᵀ * fromBlocks J 0 0 (-J) * fromBlocks 1 ((-a) • 1) (b • 1) ((1 - 2 * (a + b)) • 1) =
      fromBlocks J 0 0 (-J) := by
  rw [swapM, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
    Matrix.mul_zero, add_zero, zero_add, smul_zero]
  congr 1
  · linear_combination (norm := module) (-hab) • J
  · linear_combination (norm := module) (2 * hab + 2 * ha) • J
  · linear_combination (norm := module) (2 * hab + 2 * hb) • J
  · linear_combination (norm := module) (-7 * hab - 4 * ha - 4 * hb) • J

theorem swapM_conj_cols {a b : A} (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0) (K : Matrix (Fin d) (Fin d) A)
    (hK : (1 - (a + b)) • (K - 1) = 0) :
    (swapM d a b * fromBlocks K 0 0 1 * swapM d a b) ⬝ₘ fromRows (1 : Matrix (Fin d) (Fin d) A) 1 =
      fromRows (1 : Matrix (Fin d) (Fin d) A) 1 ⬝ₘ (1 + a • (K - 1)) := by
  rw [swapM, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_mul_fromRows, fromRows_mul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
    Matrix.mul_zero, add_zero, zero_add, smul_zero]
  congr 1
  · linear_combination (norm := module) hK + (hab + 2 * hb) • (1 : Matrix (Fin d) (Fin d) A)
  · linear_combination (norm := module) (-hab) • K + (6 * hab + 2 * ha + 4 * hb) • (1 : Matrix (Fin d) (Fin d) A)

theorem idem_unit' {a : A} (ha : a * a = a) (K L : Matrix (Fin d) (Fin d) A) (h : K * L = 1) :
    (1 + a • (K - 1)) * (1 + a • (L - 1)) = 1 := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    Matrix.sub_mul, Matrix.mul_sub, h]
  linear_combination (norm := module) ha • (2 • (1 : Matrix (Fin d) (Fin d) A) - K - L)

theorem swapM_mulVec (a b : A) (z : Fin d ⊕ Fin d → A) :
    (swapM d a b *ᵥ z) ∘ Sum.inl = z ∘ Sum.inl - b • (z ∘ Sum.inr) ∧
    (swapM d a b *ᵥ z) ∘ Sum.inr = a • (z ∘ Sum.inl) + (z ∘ Sum.inr - (a • (z ∘ Sum.inr) + b • (z ∘ Sum.inr)) -
      (a • (z ∘ Sum.inr) + b • (z ∘ Sum.inr))) := by
  rw [swapM, fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, smul_mulVec, one_mulVec]
  constructor <;> module

theorem smul_swapM_sub_one {a b u : A} (hua : u * a = 0) (hub : u * b = 0) : u • (swapM d a b - 1) = 0 := by
  rw [swapM, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, fromBlocks_smul, ← fromBlocks_zero]
  congr 1
  · module
  · linear_combination (norm := module) (-hub) • (1 : Matrix (Fin d) (Fin d) A)
  · linear_combination (norm := module) hua • (1 : Matrix (Fin d) (Fin d) A)
  · linear_combination (norm := module) (-2 * hua - 2 * hub) • (1 : Matrix (Fin d) (Fin d) A)

theorem swapM_map {a b : A} (c : A →+* A) (hca : c a = b) (hcb : c b = a) :
    (swapM d a b).map c = fromBlocks 1 ((-a) • 1) (b • 1) ((1 - 2 * (a + b)) • 1) := by
  ext (i | i) (j | j) <;> simp [swapM, Matrix.one_apply, hca, hcb] <;> split_ifs <;>
    simp [hca, hcb, map_ofNat, add_comm]

end Alg

theorem exists_conj_diag : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (V : Spc F E d) (v : Pl F) (e : AF F) (θ : AE F E),
    At (evFin F v) e → evFin F v e = 1 → e * e = e → θ * θ = θ → θ * cA σ θ = 0 →
    θ + cA σ θ = algebraMap (AF F) (AE F E) e →
    (∀ z ∈ GlobalTheory.InertSph.latAt V v, θ • z ∈ GlobalTheory.InertSph.latAt V v ∧ cA σ θ • z ∈ GlobalTheory.InertSph.latAt V v) →
    ∃ w₀ ∈ GlobalTheory.DblVac.KD σ V v, ∀ k ∈ GlobalTheory.InertSph.KAt σ V v, ∀ gd : GlobalTheory.DblVac.UD σ V,
      ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) = Matrix.fromBlocks (mat k) 0 0 1 →
      gd ∈ GlobalTheory.DblVac.KD σ V v →
      w₀ * gd * w₀⁻¹ ∈ GlobalTheory.DblVac.KD σ V v ∧ w₀ * gd * w₀⁻¹ ∈ GlobalTheory.DblVac.PDiag σ V := by
  intro F E _ _ _ _ _ σ d V v e θ hat hev _ ha hab hsum hlat
  have hb : cA σ θ * cA σ θ = cA σ θ := by rw [← map_mul, ha]
  have hcb : cA σ (cA σ θ) = θ := by
    have h := congrArg (cA σ) hsum
    rw [map_add, AlgHom.commutes, ← hsum] at h
    linear_combination h
  have hw2 := swapM_mul_self (d := d) ha hb hab
  have hU : (swapM d θ (cA σ θ))ᵀ * dbl (incM F V.J) * (swapM d θ (cA σ θ)).map (cA σ) = dbl (incM F V.J) := by
    have h := swapM_map (d := d) (cA σ).toRingHom (a := θ) (b := cA σ θ) rfl hcb
    have h' : (swapM d θ (cA σ θ)).map (cA σ) = _ := h
    rw [h']
    exact swapM_unitary ha hb hab _
  let w : UD σ V := ⟨⟨swapM d θ (cA σ θ), swapM d θ (cA σ θ), hw2, hw2⟩, hU⟩
  have hlatD : ∀ z ∈ latD V v, swapM d θ (cA σ θ) *ᵥ z ∈ latD V v := by
    intro z hz
    obtain ⟨h1, h2⟩ := swapM_mulVec θ (cA σ θ) z
    have hs := add_mem (hlat _ hz.2).1 (hlat _ hz.2).2
    refine ⟨?_, ?_⟩
    · rw [h1]; exact sub_mem hz.1 (hlat _ hz.2).2
    · rw [h2]; exact add_mem (hlat _ hz.1).1 (sub_mem (sub_mem hz.2 hs) hs)
  have hw : w ∈ KD σ V v := by
    refine ⟨fun u hu => ?_, fun z hz => ⟨hlatD z hz, hlatD z hz⟩⟩
    have hue : algebraMap (AF F) (AE F E) u * (θ + cA σ θ) = 0 := by
      have h0 : u * e = 0 := hat u hu
      rw [hsum, ← map_mul, h0, map_zero]
    have h := smul_swapM_sub_one (d := d) (u := algebraMap (AF F) (AE F E) u) (a := θ) (b := cA σ θ)
      (by linear_combination θ * hue - algebraMap (AF F) (AE F E) u * (ha + hab))
      (by linear_combination cA σ θ * hue - algebraMap (AF F) (AE F E) u * (hb + hab))
    rw [algebraMap_smul] at h
    exact h
  refine ⟨w, hw, fun k hk gd hgd hgK => ⟨GlobalTheory.DblVacFlip.mul_mem_KD (GlobalTheory.DblVacFlip.mul_mem_KD hw hgK)
    (GlobalTheory.DblVacFlip.inv_mem_KD hw), ?_⟩⟩
  have hK : (1 - (θ + cA σ θ)) • (mat k - 1) = 0 := by
    have h0 : (1 - e) • (mat k - 1) = 0 := hk.1 (1 - e) (by rw [map_sub, map_one, hev, sub_self])
    rw [hsum, ← map_one (algebraMap (AF F) (AE F E)), ← map_sub, algebraMap_smul, h0]
  refine ⟨⟨1 + θ • (mat k - 1), 1 + θ • (mat k⁻¹ - 1),
    idem_unit' ha _ _ (GlobalTheory.DblVacDiag.mat_mul_mat_inv k), idem_unit' ha _ _ (GlobalTheory.DblVacDiag.mat_inv_mul_mat k)⟩, ?_⟩
  have hgd' : matD gd = fromBlocks (mat k) 0 0 1 := hgd
  show (swapM d θ (cA σ θ) * matD gd * swapM d θ (cA σ θ)) ⬝ₘ diagCols (Fin d) = diagCols (Fin d) ⬝ₘ
    (1 + θ • (mat k - 1))
  rw [hgd']
  exact swapM_conj_cols ha hb hab _ hK

end GlobalTheory.DblVacSplitConj

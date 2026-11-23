import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.ClassSet
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic

open NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open scoped TensorProduct Matrix

namespace GlobalTheory.GenusCong

open GlobalTheory.NormSum.RepAt

theorem mem_iff_one_add {R : Type} [CommRing R] (O : Subring R) {n : ℕ} (L : Submodule O (Fin n → R))
    (m : R) (hmO : m ∈ O)
    (hm : ∀ Y ∈ matIn O n, ∀ u ∈ L, m • (Y *ᵥ u) ∈ L)
    (a : O) (ha : ∀ x : O, IsUnit (1 + a * x))
    (X : Matrix (Fin n) (Fin n) R) (hX : X ∈ matIn O n) (w : Fin n → R) :
    w ∈ L ↔ (1 + (a : R) • m • X) *ᵥ w ∈ L := by
  have haX : (a : R) • X ∈ matIn O n := fun i j => mul_mem a.2 (hX i j)
  constructor
  · intro hw
    rw [Matrix.add_mulVec, Matrix.one_mulVec, smul_comm, Matrix.smul_mulVec]
    exact add_mem hw (hm _ haX _ hw)
  · intro hz
    obtain ⟨W, hW, e⟩ := mat_inv O a ha (m • X) (fun i j => mul_mem hmO (hX i j))
    have e' := mul_eq_one_comm.1 e
    have eW : W = 1 - m • ((a : R) • X * W) := by
      rw [← e, add_mul, one_mul, smul_comm, Matrix.smul_mul, add_sub_cancel_right]
    have h1 : w = W *ᵥ ((1 + (a : R) • m • X) *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, e', Matrix.one_mulVec]
    generalize (1 + (a : R) • m • X) *ᵥ w = z at hz h1
    rw [h1, eW, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    exact sub_mem hz (hm _ (mul_mem haX hW) _ hz)

theorem eps_mulVec {R : Type} [CommRing R] {n : ℕ} (e p m : R) (he : e * e = e)
    (k X : Matrix (Fin n) (Fin n) R) (h : e • (k - 1) = (p * m) • X) (u : Fin n → R) :
    e • (k *ᵥ u) = (1 + (e * p) • m • X) *ᵥ (e • u) := by
  have h1 : e • k = e • (1 + (e * p) • m • X) := by
    rw [smul_add, smul_smul, smul_smul, ← mul_assoc, he, mul_assoc, mul_smul, ← h, smul_smul, he,
      smul_sub, add_sub_cancel]
  rw [← Matrix.smul_mulVec, h1, Matrix.smul_mulVec, Matrix.mulVec_smul]

section Ad

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

theorem exists_mult {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ m : ℕ, 0 < m ∧ ∀ Y ∈ matIn 𝒮 n, ∀ u ∈ latS (F := F) 𝔸 𝒮 Λ,
      (m : 𝒜) • (Y *ᵥ u) ∈ latS (F := F) 𝔸 𝒮 Λ := by
  obtain ⟨c₁, hc₁, h₁⟩ := adelstabL_lower (F := F) Λ hspan
  obtain ⟨c₂, hc₂, h₂⟩ := adelstabL_upper (F := F) Λ hfin
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c₁ * c₂}))
  refine ⟨Ideal.absNorm (Ideal.span {c₁ * c₂}), Nat.pos_of_ne_zero ?_, fun Y hY u hu => ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact mul_ne_zero hc₁ hc₂
  · rw [← levelafC_nat, ← hc, levelafC_mul, levelafC_mul]
    have e : (levelafC E c * (levelafC E c₁ * levelafC E c₂)) • (Y *ᵥ u) =
        fun i => levelafC E c₁ * ∑ j, levelafC E c * Y i j * (levelafC E c₂ * u j) := by
      ext i
      rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact h₁ _ fun i => sum_mem fun j _ => mul_mem (mul_mem (levelafC_mem c) (hY i j)) (h₂ u hu j)

end Ad

theorem eps_mem_latS_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Module.Finite (𝓞 E) Λ → Submodule.span E (Λ : Set (Fin n → E)) = ⊤ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∃ D : ℕ, 0 < D ∧ ∀ (k X : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), (∀ i j, X i j ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) → afsplitEps E v • (k - 1) = D • X → ∀ u : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, afsplitEps E v • u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔ afsplitEps E v • (k *ᵥ u) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ := by
  intro F E _ _ _ _ _ n Λ hfin hspan v
  obtain ⟨m, hm0, hm⟩ := exists_mult (F := F) Λ hfin hspan
  have hpv := Ideal.absNorm_mem v.asIdeal
  have hp : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  generalize Ideal.absNorm v.asIdeal = p at hpv hp
  refine ⟨p * m, Nat.mul_pos hp hm0, fun k X hX h u => ?_⟩
  rw [← Nat.cast_smul_eq_nsmul (E ⊗[F] FiniteAdeleRing (𝓞 F) F), Nat.cast_mul] at h
  rw [eps_mulVec _ _ _ (afsplit_eps_idem v) k X h u, eps_mul_nat]
  let a : intAd F := ⟨afsplitI v p, afsplitI_mem_intAd v _ (natCast_mem _ _)⟩
  exact mem_iff_one_add _ _ _ (natCast_mem _ _) hm (incInt a)
    (unit_of_integral _ incInt_integral a (unit_intAd v p hpv a rfl)) X hX _

end GlobalTheory.GenusCong

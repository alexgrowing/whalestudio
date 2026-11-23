import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import GroundTheory.AutomorphicForms.Cartan
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.KAK

variable {F : Type} [Field F]

def dg {n : ℕ} (a : Fin n → Fˣ) : GL (Fin n) F where
  val := Matrix.diagonal fun i => (a i : F)
  inv := Matrix.diagonal fun i => (((a i)⁻¹ : Fˣ) : F)
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

theorem dg_mem (O : Subring F) {n : ℕ} (a : Fin n → Fˣ) (h₁ : ∀ i, (a i : F) ∈ O)
    (h₂ : ∀ i, (((a i)⁻¹ : Fˣ) : F) ∈ O) : dg a ∈ GLint O n := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · change (Matrix.diagonal fun i => (a i : F)) i j ∈ O
    by_cases hij : i = j
    · subst hij; simpa using h₁ i
    · simp [Matrix.diagonal_apply_ne _ hij, O.zero_mem]
  · change (Matrix.diagonal fun i => (((a i)⁻¹ : Fˣ) : F)) i j ∈ O
    by_cases hij : i = j
    · subst hij; simpa using h₂ i
    · simp [Matrix.diagonal_apply_ne _ hij, O.zero_mem]

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem integralGL_le (n : ℕ) :
    GroundTheory.Automorphic.GLnLocal.integralGL F n ≤ GLint 𝒪[F] n := fun _ hg =>
  (GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff F n).1 hg

theorem irreducible_pi {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ} (h : LF 𝒪[F] ϖ nrm q)
    (hϖ : ϖ ∈ 𝒪[F]) : Irreducible (⟨ϖ, hϖ⟩ : 𝒪[F]) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  ext x
  have hu : IsUnit x ↔ ValuativeRel.valuation F (x : F) = 1 :=
    (Valuation.integer.integers (ValuativeRel.valuation F)).isUnit_iff_valuation_eq_one
  have hle : ValuativeRel.valuation F (x : F) ≤ 1 := x.2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hu, Ideal.mem_span_singleton']
  constructor
  · intro hx
    obtain ⟨o, ho, e⟩ := (h.lt_one (x : F)).1 (lt_of_le_of_ne hle hx)
    exact ⟨⟨o, ho⟩, Subtype.ext (by simp [e, mul_comm])⟩
  · rintro ⟨a, rfl⟩
    exact ((h.lt_one _).2 ⟨a, a.2, by simp [mul_comm]⟩).ne

theorem cartan {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ} (h : LF O ϖ nrm q)
    (n : ℕ) (g : GL (Fin n) F) :
    ∃ k₁ ∈ GLint O n, ∃ k₂ ∈ GLint O n, ∃ (e : Fin n → ℤ) (d : GL (Fin n) F),
      (d : Matrix (Fin n) (Fin n) F) = Matrix.diagonal (fun i => ϖ ^ e i) ∧ g = k₁ * d * k₂ := by
  obtain rfl := h.O_eq
  have hv : ValuativeRel.valuation F ϖ < 1 := (h.lt_one ϖ).2 ⟨1, Subring.one_mem _, by simp⟩
  have hϖ : ϖ ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).2 hv.le
  obtain ⟨c, hc⟩ := IsDiscreteValuationRing.associated_of_irreducible 𝒪[F]
    (GroundTheory.Automorphic.GLnLocal.irreducible_uniformizer F) (irreducible_pi h hϖ)

  have hcF : (GroundTheory.Automorphic.GLnLocal.uniformizer F : F) * ((c : 𝒪[F]) : F) = ϖ :=
    congrArg Subtype.val hc
  let cF : Fˣ := Units.map (𝒪[F]).subtype.toMonoidHom c
  have hcF' : (cF : F) = ((c : 𝒪[F]) : F) := rfl
  have hc₁ : ∀ z : ℤ, ((cF ^ z : Fˣ) : F) ∈ 𝒪[F] := fun z => by
    have : cF ^ z = Units.map (𝒪[F]).subtype.toMonoidHom (c ^ z) := by simp [cF]
    rw [this]; exact ((c ^ z : (𝒪[F])ˣ) : 𝒪[F]).2
  have hϖ0 : ϖ ≠ 0 := h.ne
  obtain ⟨μ, -, k₁, hk₁, k₂, hk₂, rfl⟩ := GroundTheory.Automorphic.Cartan.exists_eq_mul_diagPow_mul F n g
  let wu : Fˣ := Units.mk0 ϖ hϖ0
  refine ⟨k₁, integralGL_le n hk₁, dg (fun i => (cF ^ (-μ i) : Fˣ)) * k₂,
    (GLint 𝒪[F] n).mul_mem (dg_mem _ _ (fun i => hc₁ _) (fun i => ?_)) (integralGL_le n hk₂),
    μ, dg (fun i => wu ^ μ i), ?_, ?_⟩
  · rw [← _root_.zpow_neg]; exact hc₁ _
  · change (Matrix.diagonal fun i => ((wu ^ μ i : Fˣ) : F)) = _
    congr 1; funext i; simp [wu]
  · have hd : GroundTheory.Automorphic.Cartan.diagPow F n μ =
        dg (fun i => wu ^ μ i) * dg (fun i => (cF ^ (-μ i) : Fˣ)) := by
      apply Units.ext
      rw [Units.val_mul]
      change (Matrix.diagonal fun i => (GroundTheory.Automorphic.GLnLocal.uniformizer F : F) ^ μ i) =
        (Matrix.diagonal fun i => ((wu ^ μ i : Fˣ) : F)) *
          (Matrix.diagonal fun i => ((cF ^ (-μ i) : Fˣ) : F))
      rw [Matrix.diagonal_mul_diagonal]
      congr 1; funext i
      have hcu : ((c : 𝒪[F]) : F) ≠ 0 := by rw [← hcF']; exact cF.ne_zero
      have : ((c : 𝒪[F]) : F) ^ μ i ≠ 0 := zpow_ne_zero _ hcu
      simp only [_root_.zpow_neg, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, wu,
        Units.val_mk0, hcF', ← hcF, mul_zpow]
      field_simp
    rw [hd]; simp only [mul_assoc]

end GlobalTheory.CompanionTheory.QL.KAK

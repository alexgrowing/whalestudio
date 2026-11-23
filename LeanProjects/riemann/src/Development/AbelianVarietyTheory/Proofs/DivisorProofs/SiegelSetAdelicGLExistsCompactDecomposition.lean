import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactConeDiagonalConjUpperTriangularStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

open Pointwise Matrix

namespace GlobalTheory.SiegelSetGL

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

theorem continuous_pInfC : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_mapInf : Continuous (GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_pInfC E))

theorem continuous_mapFin : Continuous (GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))

theorem exists_compact_decomp : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (ω : Set (AdelicGLn.AdelicGL E a)), IsCompact ω →
    ω ⊆ (adelicBorel (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) → ∀ t : ℝ, 0 < t →
    ∃ (Ω : Set (GL (Fin a) (Cinf E))) (Kf : Set (GL (Fin a) (Af E))), IsCompact Ω ∧ IsCompact Kf ∧
      ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
        d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ b ∈ ω, ∀ k ∈ maxCompact (K := E) (n := a),
          ∃ c ∈ Ω, ∃ f ∈ Kf, b * infGL E a d * k = infGL E a (d * c) * finGL E a f := by
  intro E _ _ _ a ω hω hωB t ht
  set pI := GeneralLinearGroup.map (n := Fin a) (pInf E)
  set pF := GeneralLinearGroup.map (n := Fin a) (pFin E)
  have hωI : IsCompact (pI '' ω) := hω.image (continuous_mapInf E a)
  have hup : ∀ b ∈ pI '' ω, b.val.BlockTriangular id := by
    rintro _ ⟨b, hb, rfl⟩ i j hij
    have h0 : (b : Matrix (Fin a) (Fin a) (Ad E)) i j = 0 := hωB hb hij
    change pInf E ((b : Matrix (Fin a) (Fin a) (Ad E)) i j) = 0
    rw [h0, map_zero]
  obtain ⟨Ω0, hΩ0, hΩ⟩ := GlobalTheory.T.exists_compact_coneDiagonal_conj_upperTriangular E a (pI '' ω) hωI hup t ht
  have hK := isCompact_maxCompact (K := E) (n := a)
  refine ⟨Ω0 * pI '' (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)),
    pF '' ω * pF '' (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)),
    hΩ0.mul (hK.image (continuous_mapInf E a)),
    (hω.image (continuous_mapFin E a)).mul (hK.image (continuous_mapFin E a)), ?_⟩
  intro r d hr hrt hd b hb k hk
  refine ⟨(d⁻¹ * pI b * d) * pI k, Set.mul_mem_mul (hΩ r d hr hrt hd _ ⟨b, hb, rfl⟩) ⟨k, hk, rfl⟩,
    pF b * pF k, Set.mul_mem_mul ⟨b, hb, rfl⟩ ⟨k, hk, rfl⟩, ?_⟩
  apply ga_ext
  · change pI (b * infGL E a d * k) = pI (infGL E a (d * (d⁻¹ * pI b * d * pI k)) * finGL E a (pF b * pF k))
    simp only [map_mul, pI, pInf_infGL, pInf_finGL, mul_one]
    group
  · change pF (b * infGL E a d * k) = pF (infGL E a (d * (d⁻¹ * pI b * d * pI k)) * finGL E a (pF b * pF k))
    simp only [map_mul, pF, pFin_infGL, pFin_finGL, mul_one, one_mul]

end GlobalTheory.SiegelSetGL

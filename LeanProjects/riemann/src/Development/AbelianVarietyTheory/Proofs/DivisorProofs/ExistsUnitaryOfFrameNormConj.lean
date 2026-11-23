import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing
open scoped ComplexConjugate

namespace GlobalTheory

section Points

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {B : LB Y}

theorem CxPts.mem_ptsIn_conj {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    {U : Y.Opens} (hy : y ∈ ptsIn p σ U) : y' ∈ ptsIn p σ' U := by
  change ⊤ ≤ y'.1 ⁻¹ᵁ U
  rw [h]
  exact fun x _ => hy (Set.mem_univ _)

end Points

def CxPts.conjEquiv {E : Type} [Field E] {S : Scheme.{0}} (q : S ⟶ Sp E) (τ : E →+* ℂ) :
    CxPts q τ ≃ CxPts q (ComplexEmbedding.conjugate τ) :=
  (Points.conjHomeomorph S).toEquiv.subtypeEquiv fun y => by
    have e : spMap (ComplexEmbedding.conjugate τ) = spMap (starRingEnd ℂ) ≫ spMap τ := by
      rw [spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    have : IsIso (spMap (starRingEnd ℂ)) :=
      inferInstanceAs (IsIso (Spec.map (starRingAut (R := ℂ)).toCommRingCatIso.hom))
    change y ≫ q = _ ↔ (spMap (starRingEnd ℂ) ≫ y) ≫ q = _
    rw [e, Category.assoc, cancel_epi]

theorem mem_unitaryGroup_of_norm_mulVec {α : Type*} [Fintype α] [DecidableEq α] {V : Matrix α α ℂ}
    (h : ∀ w : α → ℂ, √(∑ i, ‖V.mulVec w i‖ ^ 2) = √(∑ i, ‖w i‖ ^ 2)) : V ∈ Matrix.unitaryGroup α ℂ := by
  have key := (LinearMap.norm_map_iff_inner_map_map (Matrix.toEuclideanLin V)).1 fun x => by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    exact h x.ofLp
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have := key (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  simpa [PiLp.inner_apply, Matrix.mul_apply, Matrix.one_apply, mul_comm, Pi.single_apply, eq_comm] using this

theorem exists_unitary_of_frameNorm_conj {N : ℕ} {M M' : Matrix (Fin N) (Fin N) ℂ} (hM : M.det ≠ 0)
    (hM' : M'.det ≠ 0) (h : ∀ x : Fin N → ℂ, frameNorm M' (fun j => conj (x j)) = frameNorm M x) :
    ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, M' = M.map (starRingEnd ℂ) * U := by
  have hV : M'⁻¹ * M.map (starRingEnd ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    mem_unitaryGroup_of_norm_mulVec fun w => by
      have := h (M.mulVec fun j => conj (w j))
      have e : (fun j => conj (M.mulVec (fun j => conj (w j)) j)) = (M.map (starRingEnd ℂ)).mulVec w :=
        funext fun j => by simp [Matrix.mulVec, dotProduct]
      rw [e, frameNorm, frameNorm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul M hM.isUnit, Matrix.one_mulVec] at this
      simpa only [RCLike.norm_conj] using this
  refine ⟨_, Unitary.star_mem hV, ?_⟩
  have e : M.map (starRingEnd ℂ) = M' * (M'⁻¹ * M.map (starRingEnd ℂ)) := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv M' hM'.isUnit, Matrix.one_mul]
  generalize M'⁻¹ * M.map (starRingEnd ℂ) = V at e hV
  rw [e, Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff.1 hV, Matrix.mul_one]

variable {F : Type} [Field F] [NumberField F]

theorem Adelic.HermSys.isConj_weight (T : Adelic.HermSys F) (hb : T.BasePointFree) (hh : T.Hermitian)
    (hc : T.ConjInvariant) (σ : F →+* ℂ) :
    (T.weight hb hh σ).IsConj (T.weight hb hh (ComplexEmbedding.conjugate σ)) := by
  obtain ⟨U, hU, e⟩ := exists_unitary_of_frameNorm_conj (hh σ) (hh (ComplexEmbedding.conjugate σ)) (hc σ)
  exact Weight.isConj_fsBasis_of_unitary _ _ _ _ _ hU e

namespace HilbertSamuel.Geo

variable (G : Geo F)

theorem isConj_φ (σ : F →+* ℂ) : (G.φ σ).IsConj (G.φ (ComplexEmbedding.conjugate σ)) :=
  G.isConj_weight _ _ G.conj σ

theorem isConj_φ₂ (σ : F →+* ℂ) : (G.φ₂ σ).IsConj (G.φ₂ (ComplexEmbedding.conjugate σ)) :=
  G.second.isConj_weight _ _ G.conj₂ σ

theorem isConj_φTw (m : ℤ) (σ : F →+* ℂ) : (G.φTw m σ).IsConj (G.φTw m (ComplexEmbedding.conjugate σ)) :=
  (G.isConj_φ₂ σ).tens ((G.isConj_φ σ).zpow m)

variable {G}

end HilbertSamuel.Geo

end GlobalTheory

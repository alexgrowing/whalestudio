import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedCuspFormL2Bounded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieActionSkewAdjointL2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantHermitianForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AuxiliaryCuspLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightHaarMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisRepresentationAdmitted
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.GKCoh MeasureTheory PositivityTheory.S2.Clozel

namespace PositivityTheory.Rg.Cz.J

theorem conj_sum_coord {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (z : Cinf E) :
    starRingEnd ℂ (∑ τ : E →+* ℂ, coord τ z) = ∑ τ : E →+* ℂ, coord τ z := by
  have h1 := GlobalTheory.CompanionTheory.HeckeAlg.dchi_eq_sum (Model.absC E 1) z
  have h2 := GlobalTheory.GKCoh.Tests.dchi_absC (E := E) 1 z
  simp only [Model.expo_absC, one_mul] at h1 h2
  rw [← h1, h2, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_mul, Complex.conj_ofReal, map_ofNat]

theorem unitTw_holds : PositivityTheory.Rg.Cz.UnitTw := by
  intro E _ _ _ a ha π
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.Clozel.exists_twist_isNormalised E a ha π
    (fun τ => ⟨_, ParLaws.hasInfChar_infChar (CG.mk π) τ⟩)
  obtain ⟨μ, h1, h2⟩ := GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant E a
  have := h1
  have := h2
  set χ := Model.absC E s with hχ
  set π' := π.twist χ with hπ'
  have hl := GlobalTheory.CompanionTheory.CuspForms.memL2_and_bounded_of_normalised GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E a μ π' hs
  have hm : ∀ φ ∈ π'.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 := fun φ hφ => (hl φ hφ).1
  have hb : ∀ φ ∈ π'.V, ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := fun φ hφ => (hl φ hφ).2
  have hi : Function.Injective (toL2ₗ μ π'.V hm) :=
    toL2ₗ_injective hm fun ψ hψ => ContAut.continuous_of_isOpen_stab E a ψ (π'.cusp ψ hψ).1.level
  let U := π.toTwist χ
  let F := toL2ₗ μ π'.V hm ∘ₗ U.toLinearMap
  have hF : Function.Injective F := hi.comp U.injective
  let H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun φ ψ => inner ℂ (F φ) (F ψ))
      (fun φ φ' ψ => by simp only [map_add, inner_add_left])
      (fun c φ ψ => by simp only [map_smul, inner_smul_left, smul_eq_mul])
      (fun φ ψ ψ' => by simp only [map_add, inner_add_right])
      (fun c φ ψ => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply])
  have hH : ∀ φ ψ, H φ ψ = inner ℂ (F φ) (F ψ) := fun φ ψ => rfl

  have hU : ∀ (X : Lie E a) (φ : π.V), F (lieOp π X φ) =
      toL2ₗ μ π'.V hm (π'.op (.lie X) (U φ)) - dchi χ (Matrix.of X).trace • F φ := fun X φ => by
    have e := π.op_toTwist χ (.lie X) φ
    have e3 : opMul χ (.lie X : Op E a) = 1 := rfl
    have e2 : opAdd χ (.lie X : Op E a) = dchi χ (Matrix.of X).trace := rfl
    rw [e3, e2, Units.val_one, one_smul] at e
    change toL2ₗ μ π'.V hm (U (π.op (.lie X) φ)) = _
    rw [e]
    simp only [map_add, map_smul, F, LinearMap.comp_apply, LinearEquiv.coe_coe, U]
    abel
  have htr : ∀ X : Lie E a, dchi χ (Matrix.of X).trace = s * ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i) := fun X => by
    rw [GlobalTheory.CompanionTheory.HeckeAlg.dchi_eq_sum, hχ]
    simp only [Model.expo_absC, ← Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Matrix.trace, map_sum]
    rfl
  refine ⟨H, -2 * s.re, fun φ ψ => ?_, fun φ hφ => ?_, fun X φ ψ => ?_⟩
  · rw [hH, hH, inner_conj_symm]
  · rw [hH]
    have : F φ ≠ 0 := fun h => hφ (hF (h.trans (map_zero F).symm))
    have hn : 0 < ‖F φ‖ := norm_pos_iff.2 this
    have e := inner_self_eq_norm_sq (𝕜 := ℂ) (F φ)
    change 0 < RCLike.re (inner ℂ (F φ) (F φ))
    rw [e]
    positivity
  · have sk : inner ℂ (F φ) (toL2ₗ μ π'.V hm (π'.op (.lie X) (U ψ))) =
        -inner ℂ (toL2ₗ μ π'.V hm (π'.op (.lie X) (U φ))) (F ψ) :=
      GlobalTheory.CompanionTheory.PeterssonSkew.lie_skew_adjoint E a μ π' hm hb X (U ψ) (U φ)
    rw [hH, hH, hH, hU, hU, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, sk, htr]
    have hr : starRingEnd ℂ (∑ τ : E →+* ℂ, ∑ i, coord τ (X i i)) = ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i) := by
      simpa only [map_sum] using conj_sum_coord (E := E) (∑ i, X i i)
    set t := ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i) with ht
    have hc : starRingEnd ℂ (s * t) = starRingEnd ℂ s * t := by rw [map_mul, hr]
    rw [hc]
    have hs2 : ((-2 * s.re : ℝ) : ℂ) = -(starRingEnd ℂ s + s) := by
      rw [add_comm, Complex.add_conj]; push_cast; ring
    rw [hs2]
    ring

end PositivityTheory.Rg.Cz.J

end

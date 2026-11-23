import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclicVectorOfSeparableCharpoly
open Matrix Polynomial

namespace GlobalTheory.SimSep

theorem mulVec_aeval_eq_zero_iff {R : Type} [Field R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (v : Fin m → R) (hv : ∀ u : Fin m → R, ∃ p : R[X], u = aeval A p *ᵥ v) (p : R[X]) :
    aeval A p *ᵥ v = 0 ↔ A.charpoly ∣ p := by
  constructor
  · intro h
    have hA : aeval A p = 0 := by
      refine Matrix.toLin'.injective (LinearMap.ext fun u => ?_)
      obtain ⟨q, rfl⟩ := hv u
      simp only [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, Matrix.mulVec_mulVec]
      rw [← map_mul, mul_comm, map_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
    have hmin : minpoly R A ∣ p := minpoly.dvd R A hA
    have hmon : (minpoly R A).Monic := minpoly.monic (Matrix.isIntegral A)

    set d := (minpoly R A).natDegree with hd
    let ψ : (Fin d → R) →ₗ[R] (Fin m → R) :=
      { toFun := fun c => aeval A (((degreeLTEquiv R d).symm c : degreeLT R d) : R[X]) *ᵥ v
        map_add' := fun a b => by simp [Matrix.add_mulVec]
        map_smul' := fun c a => by simp [Matrix.smul_mulVec] }
    have hψ : Function.Surjective ψ := by
      intro u
      obtain ⟨q, rfl⟩ := hv u
      have hq : q %ₘ minpoly R A ∈ degreeLT R d := by
        rw [mem_degreeLT]
        exact lt_of_lt_of_le (degree_modByMonic_lt q hmon) (degree_le_natDegree)
      refine ⟨degreeLTEquiv R d ⟨_, hq⟩, ?_⟩
      simp [ψ, Polynomial.aeval_modByMonic_eq_self_of_root (minpoly.aeval R A)]
    have hle : m ≤ d := by
      have := LinearMap.finrank_range_le ψ
      rw [LinearMap.range_eq_top.mpr hψ, finrank_top] at this
      simpa using this
    have heq : minpoly R A = A.charpoly := by
      refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon (Matrix.charpoly_monic A)
        (Matrix.minpoly_dvd_charpoly A) ?_).symm
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
      exact hle
    rwa [heq] at hmin
  · rintro ⟨q, rfl⟩
    rw [map_mul, Matrix.aeval_self_charpoly, zero_mul, Matrix.zero_mulVec]

end GlobalTheory.SimSep

namespace GlobalTheory.SimSep

theorem conj_of_charpoly_eq_of_separable : ∀ (R : Type) [Field R] (m : ℕ)
    (N U : Matrix (Fin m) (Fin m) R), N.charpoly = U.charpoly → N.charpoly.Separable →
    ∃ P : GL (Fin m) R, N * P.val = P.val * U := by
  intro R _ m N U hc hs
  obtain ⟨v, hv⟩ := GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly m N hs
  obtain ⟨w, hw⟩ := GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly m U (hc ▸ hs)
  let φ : R[X] →ₗ[R] (Fin m → R) :=
    { toFun := fun p => aeval N p *ᵥ v
      map_add' := fun a b => by simp [Matrix.add_mulVec]
      map_smul' := fun c a => by simp [Matrix.smul_mulVec] }
  let ψ : R[X] →ₗ[R] (Fin m → R) :=
    { toFun := fun p => aeval U p *ᵥ w
      map_add' := fun a b => by simp [Matrix.add_mulVec]
      map_smul' := fun c a => by simp [Matrix.smul_mulVec] }
  have hφ : Function.Surjective φ := fun u => let ⟨p, hp⟩ := hv u; ⟨p, hp.symm⟩
  have hψ : Function.Surjective ψ := fun u => let ⟨p, hp⟩ := hw u; ⟨p, hp.symm⟩
  have hker : LinearMap.ker ψ = LinearMap.ker φ := by
    ext p
    simp only [LinearMap.mem_ker]
    show aeval U p *ᵥ w = 0 ↔ aeval N p *ᵥ v = 0
    rw [mulVec_aeval_eq_zero_iff U w hw, mulVec_aeval_eq_zero_iff N v hv, hc]
  let T : (Fin m → R) ≃ₗ[R] (Fin m → R) :=
    ((ψ.quotKerEquivOfSurjective hψ).symm.trans (Submodule.quotEquivOfEq _ _ hker)).trans
      (φ.quotKerEquivOfSurjective hφ)
  have hT : ∀ p, T (ψ p) = φ p := by
    intro p
    have h1 : (ψ.quotKerEquivOfSurjective hψ).symm (ψ p) = Submodule.Quotient.mk p := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [T, LinearEquiv.trans_apply, h1, Submodule.quotEquivOfEq_mk]
    rfl
  have hcomm : ∀ x, T (U *ᵥ x) = N *ᵥ T x := by
    intro x
    obtain ⟨p, rfl⟩ := hψ x
    have e1 : U *ᵥ ψ p = ψ (X * p) := by
      show U *ᵥ (aeval U p *ᵥ w) = aeval U (X * p) *ᵥ w
      rw [map_mul, aeval_X, Matrix.mulVec_mulVec]
    have e2 : N *ᵥ φ p = φ (X * p) := by
      show N *ᵥ (aeval N p *ᵥ v) = aeval N (X * p) *ᵥ v
      rw [map_mul, aeval_X, Matrix.mulVec_mulVec]
    rw [e1, hT, hT, e2]
  have hl : T.toLinearMap.comp T.symm.toLinearMap = LinearMap.id :=
    LinearMap.ext fun x => by simp
  have hr : T.symm.toLinearMap.comp T.toLinearMap = LinearMap.id :=
    LinearMap.ext fun x => by simp
  let P : GL (Fin m) R :=
    ⟨LinearMap.toMatrix' T.toLinearMap, LinearMap.toMatrix' T.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp, hl, LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, hr, LinearMap.toMatrix'_id]⟩
  refine ⟨P, Matrix.toLin'.injective (LinearMap.ext fun x => ?_)⟩
  simp only [P, Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_toMatrix',
    Matrix.toLin'_apply, LinearEquiv.coe_coe]
  exact (hcomm x).symm

end GlobalTheory.SimSep

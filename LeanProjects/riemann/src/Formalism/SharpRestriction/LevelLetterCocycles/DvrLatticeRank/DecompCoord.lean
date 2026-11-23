import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.SatDVR

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Module

theorem decomp_coord {O LL : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field LL]
    [Algebra O LL] [IsFractionRing O LL] {L : Type*} [AddCommGroup L] [Module O L] {r m : ℕ}
    (bL : Basis (Fin r) O L) {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (C : ι₁ → Submodule LL (Fin r → LL)) (hC : ∀ τ, r ≤ finrank LL (C τ) + m)
    (Fs : ι₂ → Submodule LL (Fin r → LL)) (hF : ∀ τ, finrank LL (Fs τ) ≤ m) :
    ∃ (k : ℕ) (ell : Fin k → L) (Lr : Submodule O L) (P : Fin k → Fin r → O),
      finrank O Lr ≤ (Fintype.card ι₁ + Fintype.card ι₂) * m ∧
      (∀ j τ, (fun i => algebraMap O LL (bL.repr (ell j) i)) ∈ C τ) ∧
      (∀ i, bL i - ∑ j, P j i • ell j ∈ Lr) ∧
      (∀ τ, ∀ d ∈ Fs τ, ∀ j, ∑ i, algebraMap O LL (P j i) * d i = 0) := by
  obtain ⟨L₁, L₂, hc, hrk, hCL, hFL⟩ := DualFramesAlt.SatDVR.decomp (O := O) (K := LL) C hC Fs hF
  obtain ⟨k, bu⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin r)) L₁
  set pr := L₁.projectionOnto L₂ hc with hpr
  set P : Fin k → Fin r → O := fun j i => bu.coord j (pr (fun i' => if i = i' then 1 else 0)) with hP
  have hrepr : ∀ (u : Fin r → O) (i : Fin r), bL.repr (bL.equivFun.symm u) i = u i := by
    intro u i
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hsum : ∀ (i : Fin r), ∑ j, P j i • ((bu j : L₁) : Fin r → O) =
      ((pr (fun i' => if i = i' then 1 else 0) : L₁) : Fin r → O) := by
    intro i
    have h := congrArg Subtype.val (bu.sum_repr (pr (fun i' => if i = i' then 1 else 0)))
    rw [Submodule.coe_sum] at h
    simpa [hP, Basis.coord_apply] using h
  have hrow : ∀ (j : Fin k) (y : Fin r → O), ∑ i, P j i * y i = bu.coord j (pr y) := by
    intro j y
    rw [← LinearMap.comp_apply, LinearMap.pi_apply_eq_sum_univ ((bu.coord j).comp pr) y]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hP, smul_eq_mul, mul_comm]
  refine ⟨k, fun j => bL.equivFun.symm (bu j), L₂.map (bL.equivFun.symm : (Fin r → O) →ₗ[O] L), P, ?_, ?_, ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq]
    exact hrk
  · intro j τ
    convert hCL τ (bu j) (bu j).2 using 1
    funext i
    rw [DualFramesAlt.SatDVR.toK_apply, hrepr]
  · intro i
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, map_sub, map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    rw [hsum i, ← Submodule.ker_projectionOnto hc, LinearMap.mem_ker, map_sub, ← hpr,
      Submodule.projectionOnto_apply_left, sub_eq_zero]
    congr 1
    funext i'
    simp
  · intro τ d hd j
    let ψ : (Fin r → LL) →ₗ[LL] LL := ∑ i, algebraMap O LL (P j i) • LinearMap.proj i
    have hψ : ∀ x : Fin r → LL, ψ x = ∑ i, algebraMap O LL (P j i) * x i := by
      intro x
      simp [ψ, LinearMap.sum_apply, Algebra.smul_def]
    have hker : Submodule.span LL (DualFramesAlt.SatDVR.toK O LL r '' (L₂ : Set (Fin r → O))) ≤
        LinearMap.ker ψ := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hψ]
      simp only [DualFramesAlt.SatDVR.toK_apply, ← map_mul, ← map_sum]
      rw [hrow j y]
      have h0 : pr y = 0 := Submodule.projectionOnto_apply_right hc ⟨y, hy⟩
      rw [h0, map_zero, map_zero]
    have := hker (hFL τ hd)
    rwa [LinearMap.mem_ker, hψ] at this

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames

import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxNearMap :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {R' : Type} [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {τ : ℤ × ℤ →+ ℤ} {D : RD Φ R} (f : R →ₐ[Λ] R'), Φ.Near a τ D → Φ.Near a τ (D.map (f : R →+* R')) := by
  intro O Γ _ _ _ Φ Λ _ _ a R _ _ _ R' _ _ _ τ D f hD
  have hr : ∀ g i j, (D.map (f : R →+* R')).r g i j = f (D.r g i j) := by
    intro g i j
    simp [RD.map, mapRep]
  have hψ : ∀ v i s, (D.map (f : R →+* R')).ψ v i s = f (D.ψ v i s) := by
    intro v i s
    simp [RD.map]
  have hm : maximalIdeal R ≤ Ideal.comap (f : R →+* R') (maximalIdeal R') := by
    intro x hx
    rw [Ideal.mem_comap]
    show f x ∈ maximalIdeal R'
    rw [← res_eq_zero_iff Λ R', res_map, res_eq_zero_iff]
    exact hx
  have hadj : ∀ X : M4 R, adj ((f : R →+* R').mapMatrix X) = (f : R →+* R').mapMatrix (adj X) := by
    intro X
    ext i j
    simp [adj_apply, map_zsmul]
  have hrm : ∀ g, (D.map (f : R →+* R')).r g = (f : R →+* R').mapMatrix (D.r g) := by
    intro g
    ext i j
    rw [hr]
    simp
  refine ⟨⟨fun g => ?_, fun g hg => ?_, ?_⟩, fun i j => ?_, fun v i => ?_, fun g i => ?_,
    fun g i j hij hτ => ?_, fun v i s => ?_⟩
  · have hX : adj (D.r g) * D.r g = (algebraMap Λ R) (a ↑(Φ.ν g)) • 1 := hD.rep.mult g
    have h := congrArg (f : R →+* R').mapMatrix hX
    rw [map_mul, ← hadj, ← hrm] at h
    show adj ((D.map (f : R →+* R')).r g) * (D.map (f : R →+* R')).r g =
      ((algebraMap Λ R').comp a) ↑(Φ.ν g) • 1
    rw [h]
    ext i j
    simp [Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]
  · rw [hrm, hD.rep.kill g hg, map_one]
  · intro i j hij
    rw [hrm]
    simp [hD.rep.nrm hij]
  · simpa [hr] using adicCont_map (f : R →+* R') hm (hD.cont i j)
  · simpa [hψ] using adicCont_map (f : R →+* R') hm (hD.contψ v i)
  · rw [hr, res_map]
    exact hD.diag g i
  · rw [hr]
    exact hm (hD.off g i j hij hτ)
  · rw [hψ, res_map]
    exact hD.redψ v i s

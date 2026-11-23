import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OverAffineJLineComapSlGal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem admissible_sl2_action [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (g : GQ) : admitted X (slR X g) 1 := by
  have hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero) := by
    obtain ⟨φ, a, b⟩ := X.j_hol
    exact ⟨φ, b, a⟩
  have H := Tower.overY_comap_sl_gal ε X ε.injective hj
  refine ⟨fun c => (X.sl g).commutes c, fun W => ⟨fun hW => (H W hW).1 g, fun hW => ?_⟩⟩
  have h2 := (H _ hW).1 g⁻¹
  have e : (W.comap (slR X g : X.K →+* X.K)).comap (X.sl g⁻¹).toRingEquiv.toRingHom = W := by
    ext f
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap]
    change X.sl g (X.sl g⁻¹ f) ∈ W ↔ _
    rw [← X.sl_mul, inv_mul_cancel, X.sl_one]
  rwa [e] at h2

private theorem admissible_galois_action (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : admitted X (X.gal s) s := by
  refine ⟨fun c => X.gal_algebraMap s c, fun W => ?_⟩
  simp only [Tower.OverY, ValuationSubring.mem_comap, RingEquiv.coe_toRingHom, X.gal_algebraMap, X.gal_jK]
  refine and_congr ⟨fun h c => h _, fun h c => ?_⟩ Iff.rfl
  have h3 := h (s.symm c)
  rwa [AlgEquiv.apply_symm_apply] at h3

private theorem admissible_trans (X : Tower Ω ε) (τ : X.K ≃+* X.K) (s : Ω ≃ₐ[ℚ] Ω) (τ' : X.K ≃+* X.K) (s' : Ω ≃ₐ[ℚ] Ω)
    (h : admitted X τ s) (h' : admitted X τ' s') : admitted X (τ.trans τ') (s' * s) := by
  refine ⟨fun c => ?_, fun W => ?_⟩
  · show τ' (τ _) = _
    rw [h.1, h'.1, AlgEquiv.mul_apply]
  · have heq : W.comap ((τ.trans τ') : X.K →+* X.K)
        = (W.comap (τ' : X.K →+* X.K)).comap (τ : X.K →+* X.K) := by
      ext x
      rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, ValuationSubring.mem_comap]
      rfl
    rw [heq]
    exact (h'.2 W).trans (h.2 _)

private theorem admissible_symm (X : Tower Ω ε) (τ : X.K ≃+* X.K) (s : Ω ≃ₐ[ℚ] Ω) (h : admitted X τ s) :
    admitted X τ.symm s⁻¹ := by
  refine ⟨fun c => ?_, fun W => ?_⟩
  · rw [RingEquiv.symm_apply_eq, h.1, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  · have e : (W.comap (τ.symm : X.K →+* X.K)).comap (τ : X.K →+* X.K) = W := by
      ext f
      rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap]
      simp
    rw [h.2 (W.comap (τ.symm : X.K →+* X.K)), e]

private theorem admissible_preserves_units (X : Tower Ω ε) (τ : X.K ≃+* X.K) (s : Ω ≃ₐ[ℚ] Ω) (h : admitted X τ s) (u : X.K)
    (hu : IsU X u) : IsU X (τ u) := by
  have h0 : τ u ≠ 0 := (map_ne_zero τ).2 hu.1
  refine ⟨h0, fun W hW => ?_⟩
  have h1 := hu.2 _ ((h.2 W).1 hW)
  rw [KmapA.val_eq_one_iff _ hu.1] at h1
  rw [KmapA.val_eq_one_iff _ h0, ← map_inv₀]
  exact ⟨ValuationSubring.mem_comap.1 h1.1, ValuationSubring.mem_comap.1 h1.2⟩

private theorem exists_algebraic_closure_lift (X : Tower Ω ε) (τ : X.K ≃+* X.K) : ∃ σ, Lifts X σ τ :=
  ⟨IsAlgClosure.equivOfEquiv (Kb X) (Kb X) τ, fun f => IsAlgClosure.equivOfEquiv_algebraMap (Kb X) (Kb X) τ f⟩

private theorem units_subgroup_closure (X : Tower Ω ε) (m : ℕ) :
    (1 : X.Kˣ) ∈ X.Un m ∧ ∀ f g, f ∈ X.Un m → g ∈ X.Un m → f * g ∈ X.Un m ∧ f⁻¹ ∈ X.Un m := by
  refine ⟨fun W _ => ⟨1, by simp⟩, fun f g hf hg => ⟨fun W hW => ?_, fun W hW => ?_⟩⟩
  · obtain ⟨a, ha⟩ := hf W hW
    obtain ⟨b, hb⟩ := hg W hW
    refine ⟨a * b, ?_⟩
    rw [Units.val_mul, Units.val_mul, mul_pow, mul_div_mul_comm, map_mul, ha, hb, one_mul]
  · obtain ⟨a, ha⟩ := hf W hW
    refine ⟨a⁻¹, ?_⟩
    have e : ((f⁻¹ : X.Kˣ) : X.K) / ((a⁻¹ : X.Kˣ) : X.K) ^ m = ((f : X.K) / (a : X.K) ^ m)⁻¹ := by
      rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_pow, inv_div_inv, inv_div]
    rw [e, map_inv₀, ha, inv_one]

end

theorem UpperTheory.V.Z.Kato.Sym.admB :
    UpperTheory.V.Z.Kato.Sym.AdmB := by
  intro Ω _ _ _ ε X
  exact ⟨admissible_sl2_action X, admissible_galois_action X, ⟨fun _ => rfl, fun _ => Iff.rfl⟩, admissible_trans X, admissible_symm X,
    fun τ s h => ⟨admissible_preserves_units X τ s h, fun m f hf => KmapA.un_map X τ (fun W hW => (h.2 W).1 hW) m f hf⟩,
    exists_algebraic_closure_lift X, units_subgroup_closure X⟩

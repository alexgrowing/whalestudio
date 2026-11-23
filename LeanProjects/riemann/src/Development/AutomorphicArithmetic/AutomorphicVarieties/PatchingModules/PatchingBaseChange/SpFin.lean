import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem spf_nilp {k Q : Type} [Field k] [CommRing Q] (φ : k →+* Q) (x : Q)
    (hx : ∀ y, IsUnit (x * y + 1)) (f : Polynomial k) (hf : f ≠ 0) (h : f.eval₂ φ x = 0) :
    IsNilpotent x := by
  obtain ⟨g, hg, hd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf 0
  rw [map_zero, sub_zero] at hg hd
  rw [Polynomial.X_dvd_iff] at hd
  have hu : IsUnit (g.eval₂ φ x) := by
    have e : g.eval₂ φ x = φ (g.coeff 0) * (x * (φ (g.coeff 0)⁻¹ * g.divX.eval₂ φ x) + 1) := by
      have e1 : φ (g.coeff 0) * φ (g.coeff 0)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hd, map_one]
      conv_lhs => rw [← Polynomial.X_mul_divX_add g]
      rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
      linear_combination (-(x * g.divX.eval₂ φ x)) * e1
    rw [e]
    exact ((Ne.isUnit hd).map φ).mul (hx _)
  rw [hg, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at h
  exact ⟨_, hu.mul_left_eq_zero.1 h⟩

private theorem spf_nilp2 {k Q : Type} [Field k] [CommRing Q] (φ : k →+* Q) {n : ℕ} (x : Fin n → Q)
    (c : Fin n → k) (f : Polynomial k)
    (h : ∏ i, (Polynomial.X - Polynomial.C (φ (c i) + x i)) = f.map φ) (i : Fin n)
    (hx : ∀ y, IsUnit (x i * y + 1)) : IsNilpotent (x i) := by
  classical
  rcases subsingleton_or_nontrivial Q with hQ | hQ
  · exact ⟨1, Subsingleton.elim _ _⟩
  have hmon : (∏ j, (Polynomial.X - Polynomial.C (φ (c j) + x j))).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _
  have hf : f ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at h
    exact hmon.ne_zero h
  have hroot : f.eval₂ φ (φ (c i) + x i) = 0 := by
    rw [← Polynomial.eval_map, ← h, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  refine spf_nilp φ (x i) hx (f.comp (Polynomial.X + Polynomial.C (c i))) ?_ ?_
  · intro h0
    apply hf
    rwa [← Polynomial.taylor_apply, Polynomial.taylor_eq_zero] at h0
  · rw [Polynomial.eval₂_comp, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, add_comm]
    exact hroot

theorem UpperTheory.V.Pa.BC.sp_fin :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] (q n : ℕ) (P : Fin q → Polynomial B) (ut : Fin q → Fin n → B), Module.Finite B (Sp P ut) ∧ IsNoetherianRing (Sp P ut) := by
  intro B _ _ _ _ q n P ut
  classical
  let k := ResidueField B
  let J := spIdeal P ut
  let Jb : Ideal (MvPowerSeries (Fin q × Fin n) k) := Ideal.map (MvPowerSeries.map (residue B)) J
  let π := Ideal.Quotient.mk Jb
  let φ : k →+* (MvPowerSeries (Fin q × Fin n) k ⧸ Jb) := π.comp MvPowerSeries.C
  let ψ : MvPowerSeries (Fin q × Fin n) B →+* (MvPowerSeries (Fin q × Fin n) k ⧸ Jb) :=
    π.comp (MvPowerSeries.map (residue B))
  have hunit : ∀ (p : Fin q × Fin n) (y : MvPowerSeries (Fin q × Fin n) k ⧸ Jb),
      IsUnit (π (MvPowerSeries.X p) * y + 1) := by
    intro p y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one π, ← map_add]
    apply IsUnit.map
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have hnil : ∀ p : Fin q × Fin n, IsNilpotent (π (MvPowerSeries.X p)) := by
    rintro ⟨j, i⟩
    refine spf_nilp2 φ (fun i => π (MvPowerSeries.X (j, i))) (fun i => residue B (ut j i))
      ((P j).map (residue B)) ?_ i (hunit _)
    have hD : (∏ i, (Polynomial.X - Polynomial.C (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i))) -
        (P j).map MvPowerSeries.C).map ψ = 0 := by
      ext k'
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      show π _ = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, k', rfl⟩)
    rw [Polynomial.map_sub, sub_eq_zero, Polynomial.map_prod, Polynomial.map_map] at hD
    have hC : ψ.comp MvPowerSeries.C = φ.comp (residue B) := by
      ext b
      simp [ψ, φ, MvPowerSeries.map_C]
    rw [hC, ← Polynomial.map_map] at hD
    rw [← hD]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [ψ, φ, MvPowerSeries.map_C, MvPowerSeries.map_X]
  have hle : Ideal.map π (Ideal.span (Set.range
      (MvPowerSeries.X : Fin q × Fin n → MvPowerSeries (Fin q × Fin n) k))) ≤ nilradical _ := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    exact mem_nilradical.2 (hnil p)
  have hfg : (Ideal.map π (Ideal.span (Set.range
      (MvPowerSeries.X : Fin q × Fin n → MvPowerSeries (Fin q × Fin n) k)))).FG := by
    rw [Ideal.map_span]
    exact Submodule.fg_span ((Set.finite_range _).image _)
  obtain ⟨N, hN⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 hle
  have hpow : Ideal.span (Set.range
      (MvPowerSeries.X : Fin q × Fin n → MvPowerSeries (Fin q × Fin n) k)) ^ N ≤ Jb := by
    have h0 : Ideal.map π (Ideal.span (Set.range
        (MvPowerSeries.X : Fin q × Fin n → MvPowerSeries (Fin q × Fin n) k)) ^ N) = ⊥ := by
      rw [Ideal.map_pow, hN, Ideal.zero_eq_bot]
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at h0
    exact h0
  have hfin : Module.Finite B (MvPowerSeries (Fin q × Fin n) B ⧸ J) :=
    GlobalTheory.FormalIsogeny.finite_quotient_of_residue J (GlobalTheory.FormalIsogeny.finite_quotient_of_pow_le hpow)
  have hfin' : Module.Finite B (Sp P ut) := hfin
  refine ⟨hfin', ?_⟩
  have hB : IsNoetherian B (Sp P ut) := inferInstance
  exact isNoetherian_of_tower B hB

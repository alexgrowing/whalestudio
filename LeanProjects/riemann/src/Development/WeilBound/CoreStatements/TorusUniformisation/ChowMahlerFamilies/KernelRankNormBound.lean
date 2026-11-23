import Mathlib
open NumberField

namespace PositivityTheory.Xgn.AmalgamKernelBound

open Module

theorem det_eq_of_intertwine {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] [Module.Finite ℤ N]
    (ι : N →ₗ[ℤ] M) (hι : Function.Injective ι) (h : finrank ℤ N = finrank ℤ M)
    (f : M →ₗ[ℤ] M) (g : N →ₗ[ℤ] N) (hfg : ∀ x, ι (g x) = f (ι x)) :
    LinearMap.det f = LinearMap.det g := by
  obtain ⟨e⟩ : Nonempty (M ≃ₗ[ℤ] N) := ⟨LinearEquiv.ofFinrankEq M N h.symm⟩
  have hj : Function.Injective ((e : M →ₗ[ℤ] N) ∘ₗ ι) := e.injective.comp hι
  have hdet : LinearMap.det ((e : M →ₗ[ℤ] N) ∘ₗ ι) ≠ 0 := by
    intro h0
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0) (LinearMap.ker_eq_bot.mpr hj)
  have hcomm : ((e : M →ₗ[ℤ] N) ∘ₗ ι) ∘ₗ g =
      ((e : M →ₗ[ℤ] N) ∘ₗ f ∘ₗ (e.symm : N →ₗ[ℤ] M)) ∘ₗ ((e : M →ₗ[ℤ] N) ∘ₗ ι) := by
    apply LinearMap.ext
    intro x
    simp [hfg]
  have key := congrArg LinearMap.det hcomm
  rw [LinearMap.det_comp ((e : M →ₗ[ℤ] N) ∘ₗ ι) g,
    LinearMap.det_comp ((e : M →ₗ[ℤ] N) ∘ₗ f ∘ₗ (e.symm : N →ₗ[ℤ] M)) ((e : M →ₗ[ℤ] N) ∘ₗ ι),
    LinearMap.det_conj] at key
  exact (mul_left_cancel₀ hdet (key.trans (mul_comm _ _))).symm

theorem det_lsmul (E : Type) [Field E] [NumberField E] (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (a : 𝓞 E) :
    LinearMap.det ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ) =
      Algebra.norm ℤ a ^ finrank (𝓞 E) Λ := by
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) Λ
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := Λ)
    (le_refl (finrank (𝓞 E) Λ))
  let L : (Fin (finrank (𝓞 E) Λ) → 𝓞 E) →ₗ[𝓞 E] Λ := Fintype.linearCombination (𝓞 E) v
  have hL : Function.Injective L :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp hv
  have htors : ∀ x : Λ, ∃ b : 𝓞 E, b ≠ 0 ∧ b • x ∈ LinearMap.range L := by
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range L)
    have h2 : finrank (𝓞 E) (LinearMap.range L) = finrank (𝓞 E) Λ := by
      rw [LinearMap.finrank_range_of_inj hL, Module.finrank_fin_fun]
    have h3 : finrank (𝓞 E) (Λ ⧸ LinearMap.range L) = 0 := by omega
    intro x
    obtain ⟨b, hb, hbx⟩ := Module.finrank_eq_zero_iff.mp h3 (Submodule.Quotient.mk x)
    refine ⟨b, hb, ?_⟩
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hbx
  let Lz : (Fin (finrank (𝓞 E) Λ) → 𝓞 E) →ₗ[ℤ] Λ := L.restrictScalars ℤ
  have hLz : Function.Injective Lz := hL
  have htorsZ : ∀ x : Λ, ∃ r : ℤ, r ≠ 0 ∧ r • x ∈ LinearMap.range Lz := by
    intro x
    obtain ⟨b, hb, hbx⟩ := htors x
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hbx
    obtain ⟨r, hr, c, hc⟩ := IsAlgebraic.exists_nonzero_dvd
      (Algebra.IsIntegral.isIntegral (R := ℤ) b).isAlgebraic (mem_nonZeroDivisors_of_ne_zero hb)
    refine ⟨r, hr, LinearMap.mem_range.mpr ⟨c • y, ?_⟩⟩
    show L (c • y) = r • x
    rw [map_smul, hy, ← algebraMap_smul (𝓞 E) r x, hc, mul_comm b c, mul_smul]
  have hrankZ : finrank ℤ (Fin (finrank (𝓞 E) Λ) → 𝓞 E) = finrank ℤ Λ := by
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range Lz)
    have h2 := LinearMap.finrank_range_of_inj hLz
    have h3 : finrank ℤ (Λ ⧸ LinearMap.range Lz) = 0 := by
      rw [Module.finrank_eq_zero_iff]
      intro q
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨r, hr, hrx⟩ := htorsZ x
      refine ⟨r, hr, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hrx
    omega
  have hfg : ∀ y, Lz (((LinearMap.lsmul (𝓞 E) (Fin (finrank (𝓞 E) Λ) → 𝓞 E) a).restrictScalars ℤ) y)
      = ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ) (Lz y) := by
    intro y
    simp only [Lz, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
    exact map_smul L a y
  have hsmul : LinearMap.lsmul (𝓞 E) (Fin (finrank (𝓞 E) Λ) → 𝓞 E) a = a • LinearMap.id :=
    LinearMap.ext fun y => by simp
  rw [PositivityTheory.Xgn.AmalgamKernelBound.det_eq_of_intertwine Lz hLz hrankZ _ _ hfg,
    LinearMap.det_restrictScalars, hsmul, LinearMap.det_smul, LinearMap.det_id, mul_one,
    Module.finrank_fin_fun, map_pow]

theorem charpoly_lsmul (E : Type) [Field E] [NumberField E] (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (a : 𝓞 E) :
    ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ).charpoly =
      (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly ^ finrank (𝓞 E) Λ := by
  apply Polynomial.funext
  intro t
  rw [Polynomial.eval_pow, LinearMap.eval_charpoly, LinearMap.eval_charpoly]
  have h1 : algebraMap ℤ (Module.End ℤ Λ) t - (LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ =
      (LinearMap.lsmul (𝓞 E) Λ (algebraMap ℤ (𝓞 E) t - a)).restrictScalars ℤ := by
    apply LinearMap.ext
    intro x
    simp [sub_smul, Module.algebraMap_end_apply, Int.cast_smul_eq_zsmul]
  have h2 : algebraMap ℤ (Module.End ℤ (𝓞 E)) t - (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)) =
      Algebra.lmul ℤ (𝓞 E) (algebraMap ℤ (𝓞 E) t - a) := by
    rw [map_sub, AlgHom.commutes]
  rw [h1, h2, PositivityTheory.Xgn.AmalgamKernelBound.det_lsmul, ← Algebra.norm_apply ℤ]

theorem corank_le {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : M →ₗ[ℤ] M) (hf : LinearMap.det f ≠ 0) :
    finrank k (LinearMap.ker (LinearMap.baseChange k f)) ≤
      padicValNat p (LinearMap.det f).natAbs := by
  classical
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    by_contra h
    exact hf (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  have hrank : finrank ℤ (LinearMap.range f) = finrank ℤ M := LinearMap.finrank_range_of_inj hinj
  obtain ⟨t, s, d, hst⟩ : ∃ (t : Module.Basis (Fin (finrank ℤ M)) ℤ M)
      (s : Module.Basis (Fin (finrank ℤ M)) ℤ (LinearMap.range f))
      (d : Fin (finrank ℤ M) → ℤ), ∀ i, (s i : M) = d i • t i :=
    ⟨_, _, _, Submodule.smithNormalFormBotBasis_def (Module.finBasis ℤ M) hrank⟩
  obtain ⟨e, he⟩ : ∃ e : M ≃ₗ[ℤ] LinearMap.range f, ∀ x, (e x : M) = f x :=
    ⟨LinearEquiv.ofInjective f hinj, fun x => LinearEquiv.ofInjective_apply f x⟩
  have hfe : f = (LinearMap.range f).subtype ∘ₗ (e : M →ₗ[ℤ] LinearMap.range f) :=
    LinearMap.ext fun x => by simp [he]
  have hD : LinearMap.toMatrix s t (LinearMap.range f).subtype = Matrix.diagonal d := by
    ext i j
    rw [LinearMap.toMatrix_apply, Submodule.subtype_apply, hst j, map_smul,
      Module.Basis.repr_self]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply, Finsupp.single_apply, hij, Ne.symm hij]
  have hQ : IsUnit (LinearMap.toMatrix t s (e : M →ₗ[ℤ] LinearMap.range f)).det := by
    have h1 : LinearMap.toMatrix s t (e.symm : LinearMap.range f →ₗ[ℤ] M) *
        LinearMap.toMatrix t s (e : M →ₗ[ℤ] LinearMap.range f) = 1 := by
      rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id t]
      congr 1
      exact LinearMap.ext fun x => by simp
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one, mul_comm] at h2
    exact isUnit_iff_exists_inv.mpr ⟨_, h2⟩
  have hA : LinearMap.toMatrix t t f =
      Matrix.diagonal d * LinearMap.toMatrix t s (e : M →ₗ[ℤ] LinearMap.range f) := by
    rw [← hD, ← LinearMap.toMatrix_comp, ← hfe]
  have hdvd : (∏ i, d i) ∣ LinearMap.det f := by
    refine ⟨(LinearMap.toMatrix t s (e : M →ₗ[ℤ] LinearMap.range f)).det, ?_⟩
    rw [← LinearMap.det_toMatrix t, hA, Matrix.det_mul, Matrix.det_diagonal]
  have hAk : LinearMap.toMatrix (Algebra.TensorProduct.basis k t) (Algebra.TensorProduct.basis k t)
      (LinearMap.baseChange k f) =
      Matrix.diagonal (fun i => algebraMap ℤ k (d i)) *
        (LinearMap.toMatrix t s (e : M →ₗ[ℤ] LinearMap.range f)).map (algebraMap ℤ k) := by
    rw [LinearMap.toMatrix_baseChange, hA, Matrix.map_mul,
      Matrix.diagonal_map (map_zero (algebraMap ℤ k))]
  have hrange : finrank k (LinearMap.range (LinearMap.baseChange k f)) =
      Fintype.card {i // algebraMap ℤ k (d i) ≠ 0} := by
    rw [← Matrix.toLin_toMatrix (Algebra.TensorProduct.basis k t)
      (Algebra.TensorProduct.basis k t) (LinearMap.baseChange k f),
      ← Matrix.rank_eq_finrank_range_toLin, hAk, Matrix.rank_mul_eq_left_of_isUnit_det]
    · convert Matrix.rank_diagonal (fun i => algebraMap ℤ k (d i))
    · have := hQ.map (algebraMap ℤ k)
      rw [RingHom.map_det] at this
      exact this
  haveI : Module.Finite k (TensorProduct ℤ k M) :=
    Module.Finite.of_basis (Algebra.TensorProduct.basis k t)
  have hsum := LinearMap.finrank_range_add_finrank_ker (LinearMap.baseChange k f)
  rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis k t)] at hsum
  have hcongr : Fintype.card {i // algebraMap ℤ k (d i) ≠ 0} =
      Fintype.card {i // ¬ (p : ℤ) ∣ d i} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
      rw [eq_intCast, ne_eq, CharP.intCast_eq_zero_iff k p])
  have hcompl : Fintype.card {i // ¬ (p : ℤ) ∣ d i} =
      Fintype.card (Fin (finrank ℤ M)) - Fintype.card {i // (p : ℤ) ∣ d i} :=
    Fintype.card_subtype_compl _
  have hle : Fintype.card {i // (p : ℤ) ∣ d i} ≤ Fintype.card (Fin (finrank ℤ M)) :=
    Fintype.card_subtype_le _
  have hpow : (p : ℤ) ^ Fintype.card {i // (p : ℤ) ∣ d i} ∣ LinearMap.det f := by
    rw [Fintype.card_subtype, ← Finset.prod_const]
    refine dvd_trans ?_ hdvd
    refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _
      (fun i hi => (Finset.mem_filter.mp hi).2)) ?_
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  have hne : (LinearMap.det f).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hf
  have hpow' : p ^ Fintype.card {i // (p : ℤ) ∣ d i} ∣ (LinearMap.det f).natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hpow
    rwa [Int.natAbs_pow, Int.natAbs_natCast] at this
  have hv := (padicValNat_dvd_iff_le hne).mp hpow'
  omega

end PositivityTheory.Xgn.AmalgamKernelBound

theorem PositivityTheory.Xgn.kernel_rank_norm_bound : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (a : 𝓞 E), a ≠ 0 → Module.finrank k (LinearMap.ker (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ))) ≤ Module.finrank (𝓞 E) Λ * padicValNat p (Algebra.norm ℤ a).natAbs ∧ (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ)).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ Module.finrank (𝓞 E) Λ := by
  intro E _ _ k _ p _ _ Λ _ _ _ _ a ha
  have hdet := PositivityTheory.Xgn.AmalgamKernelBound.det_lsmul E Λ a
  have hN : Algebra.norm ℤ a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  refine ⟨?_, ?_⟩
  · have h := PositivityTheory.Xgn.AmalgamKernelBound.corank_le k p
      ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ) (by rw [hdet]; exact pow_ne_zero _ hN)
    rw [hdet, Int.natAbs_pow, padicValNat.pow] at h
    exact h
  · rw [LinearMap.charpoly_baseChange, PositivityTheory.Xgn.AmalgamKernelBound.charpoly_lsmul,
      Polynomial.map_pow, algebraMap_int_eq]

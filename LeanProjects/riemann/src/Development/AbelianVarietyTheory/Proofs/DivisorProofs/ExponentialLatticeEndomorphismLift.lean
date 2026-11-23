import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateLatticeSpans
open scoped TensorProduct NumberField

namespace GlobalTheory.TorusTateFree

open scoped nonZeroDivisors in

private theorem finrank_int_tower (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M]
    [Module (𝓞 E) M] : Module.finrank ℤ M = Module.finrank ℚ E * Module.finrank (𝓞 E) M := by
  let f : M →ₗ[𝓞 E] E ⊗[𝓞 E] M := TensorProduct.mk (𝓞 E) E M 1
  have hb : IsBaseChange E f := TensorProduct.isBaseChange _ _ _
  haveI h1 : IsLocalizedModule (𝓞 E)⁰ f := (isLocalizedModule_iff_isBaseChange (𝓞 E)⁰ E f).2 hb
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E :=
    IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)
  haveI h2 : IsLocalizedModule (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) f :=
    (isLocalizedModule_iff_isBaseChange _ E f).2 hb
  haveI h3 : IsLocalizedModule ℤ⁰ (f.restrictScalars ℤ) := IsLocalizedModule.restrictScalars _ f
  rw [← IsLocalizedModule.finrank_eq ℤ⁰ (f.restrictScalars ℤ) le_rfl,
    ← IsLocalizedModule.finrank_eq (𝓞 E)⁰ f le_rfl,
    ← IsLocalization.finrank_eq ℚ ℤ⁰ le_rfl, ← IsLocalization.finrank_eq E (𝓞 E)⁰ le_rfl,
    Module.finrank_mul_finrank]

private theorem exists_span_mod {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (m : R) [Finite (R ⧸ Ideal.span {m})] :
    ∃ v : Fin (Module.finrank R N) → N, ∀ x : N, ∃ (c : Fin (Module.finrank R N) → R) (z : N),
      x = ∑ k, c k • v k + m • z := by
  set I : Ideal R := Ideal.span {m} with hI
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  have h1 : Submodule.span R (Set.range b) = ⊤ := by
    rw [← Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective, b.span_eq,
      Submodule.restrictScalars_top]
  let q := TensorProduct.quotTensorEquivQuotSMul N I
  choose v hv using fun k => Submodule.Quotient.mk_surjective _ (q (b k))
  refine ⟨v, fun x => ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1
    (h1 ▸ Submodule.mem_top : q.symm (Submodule.Quotient.mk x) ∈ Submodule.span R (Set.range b))
  have h2 : x - ∑ k, c k • v k ∈ (I • ⊤ : Submodule R N) := by
    rw [← Submodule.Quotient.eq, ← q.apply_symm_apply (Submodule.Quotient.mk x), ← hc, map_sum,
      ← Submodule.mkQ_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, Submodule.mkQ_apply, hv]
  rw [hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨z, -, hz⟩ := h2
  exact ⟨c, z, by rw [hz]; abel⟩

theorem exists_gens_mod : ∀ (E : Type) [Field E] [NumberField E] (ℓ : ℕ) [Fact ℓ.Prime] (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : 𝓞 E →+* Module.End ℂ W) (L : Submodule ℤ W), (∀ a z, z ∈ L → ρ a z ∈ L) → Module.Finite ℤ L →
    ∀ (κ : Type) [Fintype κ], Module.finrank ℤ L = Fintype.card κ * Module.finrank ℚ E →
    ∃ y : κ → W, (∀ k, y k ∈ L) ∧ ∀ x ∈ L, ∃ (c : κ → 𝓞 E) (z : W), z ∈ L ∧ x = ∑ k, ρ (c k) (y k) + (ℓ : ℂ) • z := by
  intro E _ _ ℓ hℓ W _ _ ρ L hstab hfin κ _ hrk
  letI : Module (𝓞 E) W := Module.compHom W ρ
  have hs : ∀ (a : 𝓞 E) (z : W), a • z = ρ a z := fun _ _ => rfl
  let N : Submodule (𝓞 E) W :=
    { carrier := L
      add_mem' := fun ha hb => L.add_mem ha hb
      zero_mem' := L.zero_mem
      smul_mem' := fun a z hz => hstab a z hz }
  let e : L ≃ₗ[ℤ] N := AddEquiv.toIntLinearEquiv
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have : Module.Finite ℤ N := Module.Finite.equiv e
  have : Module.Finite (𝓞 E) N := Module.Finite.of_restrictScalars_finite ℤ _ _
  have : Module.IsTorsionFree (𝓞 E) W := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun a z h => or_iff_not_imp_left.2 fun ha => ?_
    obtain ⟨b, n, hn, h1⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul ℤ (1 : 𝓞 E) ha
    have h2 : (n : 𝓞 E) = b * a := by rw [mul_comm, ← h1]; simp
    have h3 : (n : ℂ) • z = 0 := by
      rw [Int.cast_smul_eq_zsmul, ← Int.cast_smul_eq_zsmul (𝓞 E), h2, mul_smul, h, smul_zero]
    exact (smul_eq_zero.1 h3).resolve_left (Int.cast_ne_zero.2 hn)
  have : Module.FinitePresentation (𝓞 E) N := Module.finitePresentation_of_finite _ _
  have : Module.Flat (𝓞 E) N := inferInstance
  have : Module.Projective (𝓞 E) N := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 E ⧸ Ideal.span {(ℓ : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hℓ.out.ne_zero)
  have hr : Fintype.card κ = Module.finrank (𝓞 E) N := by
    rw [e.finrank_eq, finrank_int_tower E N, mul_comm] at hrk
    exact (Nat.eq_of_mul_eq_mul_right Module.finrank_pos hrk).symm
  let σ : κ ≃ Fin (Module.finrank (𝓞 E) N) := Fintype.equivFinOfCardEq hr
  obtain ⟨v, hv⟩ := exists_span_mod (N := N) (ℓ : 𝓞 E)
  refine ⟨fun k => v (σ k), fun k => (v (σ k)).2, fun x hx => ?_⟩
  obtain ⟨c, z, h⟩ := hv ⟨x, hx⟩
  refine ⟨fun k => c (σ k), z, z.2, ?_⟩
  have h1 := congrArg N.subtype h
  rw [map_add, map_sum, map_smul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul ℂ,
    ← σ.sum_comp] at h1
  exact h1

theorem exists_tate_gens : ∀ (E : Type) [Field E] [NumberField E] (ℓ : ℕ) [Fact ℓ.Prime] (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : 𝓞 E →+* Module.End ℂ W) (M : Type) [CommGroup M] (ex : W → M), (∀ z w, ex (z + w) = ex z * ex w) →
    Function.Surjective ex → ∀ (L : Submodule ℤ W), (∀ z, ex z = 1 ↔ z ∈ L) →
    ∀ (β : 𝓞 E → (M →* M)), (∀ a z, ex (ρ a z) = β a (ex z)) →
    ∀ (α : 𝓞 E →+* Module.End ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M)), (∀ a t n, (α a t).lev n = β a (t.lev n)) →
    ∀ (κ : Type) [Fintype κ] (y : κ → W), (∀ k, y k ∈ L) →
    (∀ x ∈ L, ∃ (c : κ → 𝓞 E) (z : W), z ∈ L ∧ x = ∑ k, ρ (c k) (y k) + (ℓ : ℂ) • z) →
    ∃ T : κ → GlobalTheory.HTLat.Tate ℓ M, ∀ t : GlobalTheory.HTLat.Tate ℓ M, ∃ (c : κ → 𝓞 E) (s : GlobalTheory.HTLat.Tate ℓ M),
      t = ∑ k, α (c k) (T k) + (ℓ : ℤ_[ℓ]) • s := by
  intro E _ _ ℓ hℓ W _ _ ρ M _ ex hadd hsurj L hL β hβ α hα κ _ y hyL hy
  have h0 : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hℓ.out.ne_zero
  let φ : W →+ Additive M := AddMonoidHom.mk' (fun z => Additive.ofMul (ex z)) hadd
  have hpow : ∀ (z : W) (n : ℕ), ex z ^ n = ex ((n : ℂ) • z) := fun z n => by
    rw [Nat.cast_smul_eq_nsmul]
    exact (map_nsmul φ n z).symm
  let lv : GlobalTheory.HTLat.Tate ℓ M →+ Additive M := AddMonoidHom.mk' (fun t => Additive.ofMul (t.lev 1))
    fun _ _ => rfl
  let T : κ → GlobalTheory.HTLat.Tate ℓ M := fun k =>
    GlobalTheory.HTLat.Tate.mk (fun n => ex (((ℓ : ℂ) ^ n)⁻¹ • y k)) fun n =>
      ⟨by rw [hpow, smul_smul, Nat.cast_pow, mul_inv_cancel₀ (pow_ne_zero _ h0), one_smul, hL]; exact hyL k,
        by rw [hpow, smul_smul, pow_succ', mul_inv, mul_inv_cancel_left₀ h0]⟩
  refine ⟨T, fun t => ?_⟩
  obtain ⟨w, hw⟩ := hsurj (t.lev 1)
  have hwL : (ℓ : ℂ) • w ∈ L := by
    rw [← hL, ← hpow, hw]
    simpa using t.lev_pow 1
  obtain ⟨c, z, hz, h⟩ := hy _ hwL
  have h1 : w = ∑ k, ρ (c k) (((ℓ : ℂ) ^ 1)⁻¹ • y k) + z := by
    rw [← inv_smul_smul₀ h0 w, h, smul_add, inv_smul_smul₀ h0, Finset.smul_sum, pow_one]
    simp only [map_smul]
  have h2 : lv (t - ∑ k, α (c k) (T k)) = 0 := by
    have h3 : lv t = φ w := congrArg Additive.ofMul hw.symm
    have h4 : φ z = 0 := congrArg Additive.ofMul ((hL z).2 hz)
    rw [map_sub, sub_eq_zero, h3, h1, map_add, h4, add_zero, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => congrArg Additive.ofMul ?_
    exact (hβ _ _).trans (hα _ (T k) 1).symm
  obtain ⟨s, hs⟩ := GlobalTheory.TateSpan.exists_eq_p_smul_of_lev_one (t - ∑ k, α (c k) (T k)) h2
  exact ⟨c, s, by rw [← hs]; abel⟩

theorem tate_free_of_lattice : ∀ (E : Type) [Field E] [NumberField E] (ℓ : ℕ) [Fact ℓ.Prime] (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : 𝓞 E →+* Module.End ℂ W) (M : Type) [CommGroup M] (ex : W → M), (∀ z w, ex (z + w) = ex z * ex w) →
    Function.Surjective ex → ∀ (L : Submodule ℤ W), (∀ z, ex z = 1 ↔ z ∈ L) → Module.Finite ℤ L →
    ∀ (β : 𝓞 E → (M →* M)), (∀ a z, ex (ρ a z) = β a (ex z)) →
    ∀ (α : 𝓞 E →+* Module.End ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M)), (∀ a t n, (α a t).lev n = β a (t.lev n)) →
    Module.Free ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) → Module.Finite ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) →
    ∀ (κ : Type) [Fintype κ], Module.finrank ℤ L = Fintype.card κ * Module.finrank ℚ E →
    Module.finrank ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) = Fintype.card κ * Module.finrank ℚ E →
    ∃ f : (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) ≃ₗ[ℤ_[ℓ]] GlobalTheory.HTLat.Tate ℓ M,
      ∀ (a : 𝓞 E) (r : κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E), f (((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] a) • r) = α a (f r) := by
  intro E _ _ ℓ _ W _ _ ρ M _ ex hadd hsurj L hL hfin β hβ α hα hfree hfinT κ _ hrkL hrkT
  have hstab : ∀ a z, z ∈ L → ρ a z ∈ L := fun a z hz => by
    rw [← hL] at hz ⊢
    rw [hβ, hz, map_one]
  obtain ⟨y, hyL, hy⟩ := exists_gens_mod E ℓ W ρ L hstab hfin κ hrkL
  obtain ⟨T, hT⟩ := exists_tate_gens E ℓ W ρ M ex hadd hsurj L hL β hβ α hα κ y hyL hy
  let act : ℤ_[ℓ] ⊗[ℤ] 𝓞 E →ₐ[ℤ_[ℓ]] Module.End ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) α.toIntAlgHom
      (fun x a => Algebra.commute_algebraMap_left x _)
  have hact : ∀ a, act ((1 : ℤ_[ℓ]) ⊗ₜ a) = α a := fun a => by
    refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
    rw [map_one, one_mul]
    rfl
  let F : (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) →ₗ[ℤ_[ℓ]] GlobalTheory.HTLat.Tate ℓ M :=
    { toFun := fun r => ∑ k, act (r k) (T k)
      map_add' := fun r s => by
        simp only [Pi.add_apply, map_add, LinearMap.add_apply, Finset.sum_add_distrib]
      map_smul' := fun c r => by
        simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply, Finset.smul_sum, RingHom.id_apply] }
  have hF : ∀ r, F r = ∑ k, act (r k) (T k) := fun r => rfl
  have hmem : ∀ c : κ → 𝓞 E, ∑ k, α (c k) (T k) ∈ LinearMap.range F := fun c =>
    ⟨fun k => (1 : ℤ_[ℓ]) ⊗ₜ c k, by simp only [hF, hact]⟩
  have hI : IsLocalRing.maximalIdeal ℤ_[ℓ] ≤ (⊥ : Ideal ℤ_[ℓ]).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hle : (⊤ : Submodule ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M)) ≤
      LinearMap.range F ⊔ IsLocalRing.maximalIdeal ℤ_[ℓ] • ⊤ := by
    intro t _
    obtain ⟨c, s, rfl⟩ := hT t
    refine Submodule.add_mem_sup (hmem c) (Submodule.smul_mem_smul ?_ trivial)
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  have hsurjF : Function.Surjective F := LinearMap.range_eq_top.1
    (top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI hle))
  have hrkR : Module.finrank ℤ_[ℓ] (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) = Fintype.card κ * Module.finrank ℚ E := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Module.finrank_baseChange, NumberField.RingOfIntegers.rank]
  let e := LinearEquiv.ofFinrankEq (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) (GlobalTheory.HTLat.Tate ℓ M) (hrkR.trans hrkT.symm)
  have hinj : Function.Injective F := by
    have h := OrzechProperty.injective_of_surjective_endomorphism (e.symm.toLinearMap ∘ₗ F)
      (e.symm.surjective.comp hsurjF)
    rw [LinearMap.coe_comp] at h
    exact h.of_comp
  refine ⟨LinearEquiv.ofBijective F ⟨hinj, hsurjF⟩, fun a r => ?_⟩
  change F _ = α a (F r)
  rw [hF, hF, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, hact]
  rfl

end GlobalTheory.TorusTateFree

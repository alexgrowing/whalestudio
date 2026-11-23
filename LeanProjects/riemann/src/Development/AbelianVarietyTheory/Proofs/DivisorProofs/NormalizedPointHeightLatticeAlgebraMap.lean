import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.HeightExt

open NumberField IsDedekindDomain GlobalTheory.ChowHt GlobalTheory.Adelic

section Places

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def locDeg (K : Type) [Field K] [NumberField K] [Algebra K L] (w : HeightOneSpectrum (𝓞 L)) : ℕ :=
  w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)

theorem mk_algebraMap (w : HeightOneSpectrum (𝓞 L)) (x : K) :
    FinitePlace.mk w (algebraMap K L x) = FinitePlace.mk (w.under (𝓞 K)) x ^ locDeg K w := by
  set v := w.under (𝓞 K) with hv
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have he : 0 < w.asIdeal.ramificationIdx (𝓞 K) := Ideal.ramificationIdx_pos _ _
  have hf : 0 < w.asIdeal.inertiaDeg (𝓞 K) := Ideal.inertiaDeg_pos _ _
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, map_zero, map_zero, locDeg, zero_pow (Nat.mul_pos he hf).ne']
  have hn := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot
  rw [Ideal.inertiaDeg'_eq_inertiaDeg] at hn
  have h0 : v.valuation K x ≠ 0 := (v.valuation K).ne_zero_iff.2 hx
  rw [FinitePlace.mk_apply, FinitePlace.mk_apply, FinitePlace.norm_embedding', FinitePlace.norm_embedding',
    ← HeightOneSpectrum.valuation_liesOver L v w x, map_pow, WithZeroMulInt.toNNReal_neg_apply _ h0,
    WithZeroMulInt.toNNReal_neg_apply _ h0, Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot, hn, locDeg]
  push_cast
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_mul]
  congr 1
  push_cast
  ring

theorem finite_fiber (v : HeightOneSpectrum (𝓞 K)) :
    {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) = v}.Finite := by
  have h : (v.asIdeal.primesOver (𝓞 L)).Finite := Set.toFinite _
  refine (h.preimage (f := fun w : HeightOneSpectrum (𝓞 L) => w.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset fun w hw => ?_
  exact ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩

theorem sum_locDeg (v : HeightOneSpectrum (𝓞 K)) :
    ∑ w ∈ (finite_fiber (L := L) v).toFinset, locDeg K w = Module.finrank K L := by
  classical
  have hsumN : ∑ q : v.asIdeal.primesOver (𝓞 L), q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) =
      Module.finrank K L := by
    rw [Ideal.sum_ramification_inertia_eq_finrank, IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]
  rw [← hsumN]
  refine Finset.sum_bij (fun w hw => ⟨w.asIdeal, w.isPrime,
    ⟨(congrArg HeightOneSpectrum.asIdeal (((finite_fiber (L := L) v).mem_toFinset).1 hw)).symm⟩⟩) (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => HeightOneSpectrum.ext (congrArg Subtype.val h)) (fun q _ => ?_) fun _ _ => rfl
  refine ⟨⟨q.1, q.2.1, fun h0 => v.ne_bot ?_⟩, (Set.Finite.mem_toFinset _).2 (HeightOneSpectrum.ext q.2.2.over.symm),
    rfl⟩
  have h1 : v.asIdeal = q.1.comap (algebraMap (𝓞 K) (𝓞 L)) := q.2.2.over
  rw [h1, h0]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

theorem finsum_locDeg_mul (g : HeightOneSpectrum (𝓞 K) → ℝ) (hg : (Function.support g).Finite) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 L), (locDeg K w : ℝ) * g (w.under (𝓞 K)) = Module.finrank K L * ∑ᶠ v, g v := by
  classical
  have hS : {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ Function.support g}.Finite :=
    (hg.biUnion fun v _ => finite_fiber (L := L) v).subset fun w hw => Set.mem_biUnion hw rfl
  rw [finsum_eq_sum_of_support_subset _ (s := hS.toFinset) fun w hw => by
      simpa using right_ne_zero_of_mul hw,
    finsum_eq_sum g hg, Finset.mul_sum,
    ← Finset.sum_fiberwise_of_maps_to (t := hg.toFinset) (g := fun w => w.under (𝓞 K)) fun w hw => by simpa using hw]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [← sum_locDeg v, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr ?_ fun w hw => by rw [(Set.Finite.mem_toFinset _).1 hw]
  ext w
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv ⊢
  exact ⟨fun h => h.2, fun h => ⟨h ▸ hv, h⟩⟩

theorem sum_comp_algebraMap (f : (K →+* ℂ) → ℝ) :
    ∑ σ : L →+* ℂ, f (σ.comp (algebraMap K L)) = Module.finrank K L * ∑ τ : K →+* ℂ, f τ := by
  classical
  have hfib : ∀ τ : K →+* ℂ, (Finset.univ.filter fun σ : L →+* ℂ => σ.comp (algebraMap K L) = τ).card =
      Module.finrank K L := by
    intro τ
    let _ : Algebra K ℂ := τ.toAlgebra
    let e : {σ : L →+* ℂ // σ.comp (algebraMap K L) = τ} ≃ (L →ₐ[K] ℂ) :=
      { toFun := fun σ => ⟨σ.1, fun a => congrFun (congrArg DFunLike.coe σ.2) a⟩
        invFun := fun φ => ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩
        left_inv := fun σ => rfl
        right_inv := fun φ => rfl }
    rw [← Fintype.card_subtype, Fintype.card_congr e, AlgHom.card]
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : L →+* ℂ => σ.comp (algebraMap K L))
    (fun σ => f (σ.comp (algebraMap K L))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_congr rfl fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2], Finset.sum_const, hfib τ,
    nsmul_eq_mul]

end Places

theorem iSup_pow {ι : Type} [Finite ι] [Nonempty ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (m : ℕ) :
    ⨆ i, a i ^ m = (⨆ i, a i) ^ m := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := a)
  refine le_antisymm (ciSup_le fun j => pow_le_pow_left₀ (ha j) (le_ciSup (Set.finite_range _).bddAbove j) m) ?_
  rw [← hi]
  exact le_ciSup (f := fun i => a i ^ m) (Set.finite_range _).bddAbove i

theorem finite_support_log_iSup {K ι : Type} [Field K] [NumberField K] [Finite ι] {z : ι → K} (hz : z ≠ 0) :
    (Function.support fun v : FinitePlace K => Real.log (⨆ k, v (z k))).Finite := by
  obtain ⟨k₀, hk₀⟩ := Function.ne_iff.1 hz
  have : Nonempty ι := ⟨k₀⟩
  refine (Set.finite_iUnion fun k : {k // z k ≠ 0} => FinitePlace.hasFiniteMulSupport k.2).subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at h
  refine hv ?_
  have : ⨆ k, v (z k) = 1 := le_antisymm (ciSup_le fun k => by
      rcases eq_or_ne (z k) 0 with h0 | h0
      · rw [h0, map_zero]; exact zero_le_one
      · exact (h ⟨k, h0⟩).le)
    ((h ⟨k₀, hk₀⟩).ge.trans (le_ciSup (f := fun k => v (z k)) (Set.finite_range _).bddAbove k₀))
  simp only [this, Real.log_one]

theorem finsum_log_iSup_algebraMap {K L ι : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Finite ι] {z : ι → K} (hz : z ≠ 0) :
    ∑ᶠ w : FinitePlace L, Real.log (⨆ k, w (algebraMap K L (z k))) =
      Module.finrank K L * ∑ᶠ v : FinitePlace K, Real.log (⨆ k, v (z k)) := by
  obtain ⟨k₀, -⟩ := Function.ne_iff.1 hz
  have : Nonempty ι := ⟨k₀⟩
  rw [← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := L)).symm,
    ← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm,
    ← finsum_locDeg_mul _ ((finite_support_log_iSup hz).preimage
      (FinitePlace.equivHeightOneSpectrum (K := K)).symm.injective.injOn)]
  refine finsum_congr fun w => ?_
  rw [← Real.log_pow, ← iSup_pow _ fun _ => apply_nonneg _ _]
  exact congrArg Real.log (iSup_congr fun k => mk_algebraMap w (z k))

theorem pointHeight_algebraMap : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
    Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K'] (y : Fin N → K),
      y ≠ 0 → pointHeight w A (fun j => algebraMap K K' (y j)) = pointHeight w A y := by
  intro F K _ _ _ _ _ N n w A hw _ K' _ _ _ _ _ y hy
  classical
  have hz : (fun k => ∑ j, algebraMap F K (w j k) * y j) ≠ 0 := fun h => by
    have hp := finSize_pos hw (algebraMap F K) AbsoluteValue.trivial hy
    have h' : ∀ k, ∑ j, algebraMap F K (w j k) * y j = 0 := congrFun h
    simp [finSize, h'] at hp
  have h₁ := finsum_log_iSup_algebraMap (L := K') hz
  have h₂ := sum_comp_algebraMap (L := K')
    fun τ : K →+* ℂ => Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ (y j))
  simp only [map_sum, map_mul, ← IsScalarTower.algebraMap_apply] at h₁
  simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, RingHom.comp_apply] at h₂
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hKL : (0 : ℝ) < Module.finrank K K' := by exact_mod_cast Module.finrank_pos
  rw [pointHeight_eq, pointHeight_eq, h₂, ← Module.finrank_mul_finrank ℚ K K']
  simp only [finSize, ← FinitePlace.coe_apply]
  rw [h₁]
  push_cast
  field_simp

end GlobalTheory.Adelic.HeightExt

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DictionaryStatement

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.SphereCover

section Abstract

variable {K : Type} [NormedField K] [IsUltrametricDist K] [ProperSpace K]

theorem exists_sphere {T : Type} [AddCommGroup T] [Module K T] [Module.Finite K T]
    [TopologicalSpace T] [IsModuleTopology K T] (π : K) (h0 : π ≠ 0) (h1 : ‖π‖ < 1)
    (hv : ∀ a : K, a ≠ 0 → ∃ j : ℤ, ‖a‖ = ‖π‖ ^ j) (A : Set T) (hA : IsCompact A) :
    ∃ (P : Set T) (k : ℕ), IsCompact P ∧ IsOpen P ∧ (0 : T) ∉ P ∧
      ∀ X ∈ A, X ≠ 0 → ∃ (i : ℕ), ∃ Y ∈ P, X = (π ^ ((i : ℤ) - k)) • Y := by
  haveI : ContinuousAdd T := IsModuleTopology.toContinuousAdd K T
  haveI : ContinuousSMul K T := IsModuleTopology.toContinuousSMul K T
  let c : T ≃ₗ[K] (Fin (Module.finrank K T) → K) := (Module.finBasis K T).equivFun
  have hc : Continuous c := IsModuleTopology.continuous_of_linearMap c.toLinearMap
  have hc' : Continuous c.symm := IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap
  obtain ⟨C, hC⟩ : ∃ C, ∀ X ∈ A, ‖c X‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hA.image hc).isBounded.exists_norm_le
    exact ⟨C, fun X hX => hC _ ⟨X, hX, rfl⟩⟩
  have hπ : 0 < ‖π‖ := norm_pos_iff.2 h0
  obtain ⟨k, hk⟩ : ∃ k : ℕ, C < (‖π‖⁻¹) ^ k :=
    pow_unbounded_of_one_lt C ((one_lt_inv₀ hπ).2 h1)
  have himg : c.symm '' Metric.sphere 0 1 = c ⁻¹' Metric.sphere 0 1 := by
    ext X
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hX
      exact ⟨c X, hX, by simp⟩
  refine ⟨c.symm '' Metric.sphere 0 1, k, (isCompact_sphere _ _).image hc', ?_, ?_, ?_⟩
  · rw [himg]
    exact (IsUltrametricDist.isClopen_sphere 0 one_ne_zero).isOpen.preimage hc
  · rw [himg]
    simp
  · intro X hX hX0
    have hw : c X ≠ 0 := by simpa using hX0
    obtain ⟨l, hl⟩ : ∃ l, c X l ≠ 0 := Function.ne_iff.1 hw
    haveI : Nonempty (Fin (Module.finrank K T)) := ⟨l⟩
    obtain ⟨m, -, hm⟩ := Finset.exists_mem_eq_sup (Finset.univ) Finset.univ_nonempty
      (fun i => ‖c X i‖₊)
    have hnorm : ‖c X‖ = ‖c X m‖ := by
      rw [← coe_nnnorm, Pi.nnnorm_def, hm, coe_nnnorm]
    have hm0 : c X m ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnorm
      exact hw (norm_eq_zero.1 hnorm)
    obtain ⟨j, hj⟩ := hv _ hm0
    rw [← hnorm] at hj
    have hjk : -(k : ℤ) ≤ j := by
      have : ‖π‖ ^ j ≤ ‖π‖ ^ (-(k : ℤ)) := by
        rw [← hj, zpow_neg, zpow_natCast, ← inv_pow]
        exact ((hC X hX).trans hk.le)
      exact (zpow_le_zpow_iff_right_of_lt_one₀ hπ h1).1 this
    have hY : ‖c ((π ^ (-j)) • X)‖ = 1 := by
      rw [map_smul, norm_smul, norm_zpow, hj, ← zpow_add₀ hπ.ne']
      simp
    refine ⟨(j + k).toNat, (π ^ (-j)) • X, ?_, ?_⟩
    · rw [himg]
      simpa using hY
    · have : (((j + k).toNat : ℕ) : ℤ) - k = j := by
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      rw [this, smul_smul, ← zpow_add₀ h0]
      simp

end Abstract

section Cover

variable {K R : Type} [NormedField K] [IsUltrametricDist K] [ProperSpace K] [CommRing R]
  [Algebra K R] [Module.Finite K R] [TopologicalSpace R] [IsModuleTopology K R]

theorem linearIndependent_of_ne_zero (hR : IsField R) {M : ℕ} {X : Fin 1 → Fin M → R}
    (hX : X ≠ 0) : LinearIndependent R X := by
  haveI : IsDomain R := hR.isDomain
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have h0 : X 0 ≠ 0 := fun h => hX (funext fun p => by
    obtain rfl : p = 0 := Subsingleton.elim _ _
    exact h)
  obtain ⟨l, hl⟩ : ∃ l, X 0 l ≠ 0 := Function.ne_iff.1 h0
  have h1 := congrFun hg l
  simp only [Fin.sum_univ_one, Fin.isValue, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
  exact (mul_eq_zero.1 h1).resolve_right hl

theorem exists_cover (hR : IsField R) (π : K) (h0 : π ≠ 0) (h1 : ‖π‖ < 1)
    (hv : ∀ a : K, a ≠ 0 → ∃ j : ℤ, ‖a‖ = ‖π‖ ^ j) {M : ℕ} (hM : 2 ≤ M)
    (A : Set (Fin 1 → Fin M → R)) (hA : IsCompact A) :
    ∃ (ι : Type) (_ : Countable ι) (P : Set (Fin 1 → Fin M → R)) (u : ι → Rˣ),
      IsCompact P ∧ IsOpen P ∧ P ⊆ {X : Fin 1 → Fin M → R | LinearIndependent R X} ∧
      Summable (fun i => ‖Algebra.norm K (u i : R)‖₊ ^ (M - 1)) ∧
      A ∩ {X : Fin 1 → Fin M → R | LinearIndependent R X} ⊆
        ⋃ i, (fun (X : Fin 1 → Fin M → R) (p : Fin 1) (k : Fin M) => (u i : R) * X p k) '' P := by
  haveI : Nontrivial R := ⟨hR.exists_pair_ne⟩
  obtain ⟨P, k, hPc, hPo, hP0, hcov⟩ := exists_sphere π h0 h1 hv A hA
  let w : Kˣ := Units.mk0 π h0
  let u : ℕ → Rˣ := fun i => Units.map (algebraMap K R).toMonoidHom (w ^ ((i : ℤ) - k))
  have hu : ∀ i : ℕ, (u i : R) = algebraMap K R (π ^ ((i : ℤ) - k)) := fun i => by
    change algebraMap K R ((w ^ ((i : ℤ) - k) : Kˣ) : K) = _
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  refine ⟨ℕ, inferInstance, P, u, hPc, hPo, ?_, ?_, ?_⟩
  · intro X hX
    exact linearIndependent_of_ne_zero hR fun h => hP0 (h ▸ hX)
  · have hd : 0 < Module.finrank K R := Module.finrank_pos
    have hπ : 0 < ‖π‖₊ := nnnorm_pos.2 h0
    have hlt : ‖π‖₊ < 1 := by exact_mod_cast h1
    set e : ℕ := Module.finrank K R * (M - 1) with he
    have he0 : e ≠ 0 := Nat.mul_ne_zero hd.ne' (by omega)
    have hq : ‖π‖₊ ^ e < 1 := pow_lt_one₀ hπ.le hlt he0
    have hs := (NNReal.summable_geometric hq).mul_left ((‖π‖₊ ^ (-(k : ℤ))) ^ e)
    refine hs.congr fun i => ?_
    rw [hu, Algebra.norm_algebraMap, nnnorm_pow, nnnorm_zpow, sub_eq_add_neg,
      zpow_add₀ hπ.ne', zpow_natCast, he]
    ring
  · rintro X ⟨hXA, hXf⟩
    have hX0 : X ≠ 0 := by
      intro h
      have h2 : LinearIndependent R X := hXf
      exact h2.ne_zero 0 (by rw [h]; rfl)
    obtain ⟨i, Y, hY, hXY⟩ := hcov X hXA hX0
    refine Set.mem_iUnion.2 ⟨i, Y, hY, ?_⟩
    rw [hXY]
    funext p l
    simp [hu, Algebra.smul_def]

end Cover

theorem exists_uniformizer {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : Fv F v, π ≠ 0 ∧ ‖π‖ < 1 ∧ ∀ a : Fv F v, a ≠ 0 → ∃ j : ℤ, ‖a‖ = ‖π‖ ^ j := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  let ϖ : Fv F v := (π : Fv F v)
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have h1 : Valued.v ϖ < 1 := by
    rw [hϖ]
    decide
  refine ⟨ϖ, hϖ0, Valued.toNormedField.norm_lt_one_iff.2 h1, fun a ha => ?_⟩
  have hva : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  set k : ℤ := WithZero.log (Valued.v a) with hk
  have hu : Valued.v (a * ϖ ^ k) = 1 := by
    rw [map_mul, map_zpow₀, hϖ, ← WithZero.exp_log hva, ← WithZero.exp_zsmul, ← WithZero.exp_add,
      ← hk, ← WithZero.exp_zero]
    congr 1
    simp
  have hn : ‖a * ϖ ^ k‖ = 1 := le_antisymm (Valued.toNormedField.norm_le_one_iff.2 hu.le)
    (not_lt.1 fun h => (Valued.toNormedField.norm_lt_one_iff.1 h).ne hu)
  have hϖn : ‖ϖ‖ ≠ 0 := norm_ne_zero_iff.2 hϖ0
  refine ⟨-k, ?_⟩
  rw [norm_mul, norm_zpow] at hn
  rw [zpow_neg]
  exact eq_inv_of_mul_eq_one_left hn

theorem coverF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 2 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)), IsField (Fv F v ⊗[F] E) → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact A → ∃ (ι : Type) (_ : Countable ι) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (u : ι → (Fv F v ⊗[F] E)ˣ), IsCompact P ∧ IsOpen P ∧ P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧ Summable (fun i => ‖Algebra.norm (Fv F v) (u i : Fv F v ⊗[F] E)‖₊ ^ (M - 1)) ∧ A ∩ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ⊆ ⋃ i, (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u i : Fv F v ⊗[F] E) * X p k) '' P := by
  intro F E _ _ _ _ _ σ h M hM v hF A hA
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
  haveI : ProperSpace (Fv F v) := GlobalTheory.CompanionTheory.DictLoc.properSpace_Fv v
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨π, h0, h1, hv⟩ := exists_uniformizer v
  exact exists_cover hF π h0 h1 hv hM A hA

end GlobalTheory.CompanionTheory.WeilSiegel.SphereCover

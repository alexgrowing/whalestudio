import Formalism.BranchSandwichDivisors.StatementL
import Formalism.HarderNarasimhan.ShiftInvariance

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.BranchingDeterminantCap

open Formalism.HN

section SlopeTestRemainingChoices

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

theorem ms_rkK_bot : rkK (⊥ : Submodule (𝓞 K) V) = 0 := by
  unfold Formalism.HN.rkK
  simp

theorem ms_rkK_pos (b : Basis ι K V) {L : Submodule (𝓞 K) V} (hL : L ≠ ⊥) : 0 < rkK L := by
  haveI : FiniteDimensional K V := Module.Finite.of_basis b
  obtain ⟨x, hxL, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
  unfold Formalism.HN.rkK
  rw [Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨⟨x, Submodule.subset_span hxL⟩, ?_⟩
  intro h
  exact hx0 (congrArg Subtype.val h)

theorem ms_nPl_pos : 0 < nPl K := by
  unfold Formalism.HN.nPl
  exact Fintype.card_pos

theorem ms_htQ_bot (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (A : Submodule (𝓞 K) V) : htQ b X A ⊥ = ht b X A := by
  have hz : zl (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = ⊥ := by
    unfold Formalism.HN.zl
    simp
  have hq : ∀ L : Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)),
      Formalism.F.quot L ⊥ = L := by
    intro L
    unfold Formalism.F.quot
    have hp : ∀ y : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2),
        (Submodule.span ℝ ((⊥ : Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) :
          Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))))ᗮ.starProjection y = y := by
      intro y
      simp only [Submodule.bot_coe, Submodule.span_zero_singleton, Submodule.bot_orthogonal_eq_top]
      first
        | (rw [Submodule.starProjection_eq_self_iff]; exact Submodule.mem_top)
        | simp [Submodule.starProjection_top]
        | exact Submodule.starProjection_top_apply y
    ext x
    simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, ContinuousLinearMap.coe_coe, hp]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  unfold Formalism.HN.htQ Formalism.HN.ht
  rw [ms_rkK_bot, hz, hq]
  simp only [Nat.cast_zero, sub_zero]
  congr 2
  rw [← Real.rpow_natCast, Nat.cast_mul]

theorem ms_mu_eq [IsTotallyComplex K] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hfg : L.FG) (hL : L ≠ ⊥) :
    muDef b X L = -(Real.log (ht b X L) / ((nPl K : ℝ) * (rkK L : ℝ))) := by
  have h := size_maximal_slope K V ι b X hX L hfg hL
  obtain ⟨-, h2, -⟩ := h
  obtain ⟨-, -, hpos⟩ := place_lattice_structure K V ι b X hX L hfg
  have hf : (0 : ℝ) < nPl K := by exact_mod_cast ms_nPl_pos
  have hj : (0 : ℝ) < rkK L := by exact_mod_cast ms_rkK_pos b hL
  rw [h2]
  unfold size
  rw [Real.log_rpow hpos]
  field_simp

theorem ms_opNorm_nat [Nonempty ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (n : ℕ) (v : InfinitePlace K) :
    opNormAt b X b X v ((n : K) • (LinearMap.id : V →ₗ[K] V)) = n := by
  have h1 : (LinearMap.toMatrix b b ((n : K) • (LinearMap.id : V →ₗ[K] V))).map v.embedding
      = (n : ℂ) • (1 : Matrix ι ι ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [LinearMap.toMatrix_id, Matrix.one_apply, h]
  have hM : (X v)⁻¹ * (LinearMap.toMatrix b b ((n : K) • (LinearMap.id : V →ₗ[K] V))).map
      v.embedding * X v = (n : ℂ) • (1 : Matrix ι ι ℂ) := by
    rw [h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.nonsing_inv_mul _ (hX v)]
  have h3 : Matrix.toEuclideanLin (1 : Matrix ι ι ℂ) = LinearMap.id := by
    first
      | exact Matrix.toEuclideanLin_one
      | (ext x i; simp [Matrix.toEuclideanLin_apply])
      | (simp [Matrix.toEuclideanLin, Matrix.toLin'_one])
  have h4 : LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((n : ℂ) • (1 : Matrix ι ι ℂ)))
      = (n : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ ι) := by
    rw [map_smul, h3, map_smul]
    congr 1
  unfold Formalism.HN.opNormAt
  rw [hM, h4, norm_smul]
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hid : ‖ContinuousLinearMap.id ℂ (EuclideanSpace ℂ ι)‖ = 1 := by
    first
      | exact ContinuousLinearMap.norm_id
      | (apply ContinuousLinearMap.norm_id_of_nontrivial_seminorm
         exact ⟨EuclideanSpace.single i 1, by simp⟩)
  rw [hid, mul_one]
  simp

theorem ms_htMap_nat [Nonempty ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (n : ℕ) :
    htMap b X b X ((n : K) • (LinearMap.id : V →ₗ[K] V)) = 2 * Real.log n := by
  unfold Formalism.HN.htMap
  simp_rw [ms_opNorm_nat b X hX n]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.log_pow]
  have hc : (0 : ℝ) < (Fintype.card (InfinitePlace K) : ℝ) := by exact_mod_cast Fintype.card_pos
  simp only [Formalism.HN.nPl]
  field_simp
  push_cast
  ring

end SlopeTestRemainingChoices

theorem map_slope_mu : MapMu := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B hA hB hA0 hinj hAB hrk
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have hker : A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxk⟩
    have hx0 : φ x = 0 := hxk
    exact (Submodule.mem_bot _).2 (hinj hxA A.zero_mem (by rw [hx0, map_zero]))
  have hrkI : rkK (A.map (φ.restrictScalars (𝓞 K))) = rkK A := by
    have h := sizeIneq_rk φ A
    rw [hker, ms_rkK_bot, add_zero] at h
    exact h
  obtain ⟨-, hht⟩ := height_image_formula K V ι W κ b X b' X' hX hX' φ A hA
  rw [hker, ms_htQ_bot, hrkI] at hht
  set I := A.map (φ.restrictScalars (𝓞 K)) with hI
  have hIfg : I.FG := hA.map _
  have hI0 : I ≠ ⊥ := by
    intro h
    have h0 := ms_rkK_pos b hA0
    rw [← hrkI, h, ms_rkK_bot] at h0
    exact lt_irrefl _ h0
  have hB0 : B ≠ ⊥ := fun h => hI0 (le_bot_iff.mp (h ▸ hAB))
  have hmono : ht b' X' B ≤ ht b' X' I :=
    (size_maximal_slope K W κ b' X' hX' I hIfg hI0).2.2.2.2.2 B hAB hB (hrk.trans hrkI.symm)
  obtain ⟨-, -, hposA⟩ := place_lattice_structure K V ι b X hX A hA
  obtain ⟨-, -, hposB⟩ := place_lattice_structure K W κ b' X' hX' B hB
  obtain ⟨-, -, hposI⟩ := place_lattice_structure K W κ b' X' hX' I hIfg
  have hj : 0 < rkK A := ms_rkK_pos b hA0
  have hop : ∀ v, 0 < opNormAt b X b' X' v φ := by
    intro v
    have hnn : 0 ≤ opNormAt b X b' X' v φ := norm_nonneg _
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exfalso
      have hz : (∏ v, opNormAt b X b' X' v φ ^ (2 * rkK A)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ v)
        rw [← h]
        exact zero_pow (by omega)
      rw [hz, zero_mul] at hht
      exact absurd hposI (not_lt.2 hht)
  have hlog : Real.log (ht b' X' B) ≤
      (rkK A : ℝ) * (∑ v, Real.log (opNormAt b X b' X' v φ ^ 2)) + Real.log (ht b X A) := by
    have h1 : Real.log (ht b' X' B) ≤ Real.log ((∏ v, opNormAt b X b' X' v φ ^ (2 * rkK A)) *
        ht b X A) := Real.log_le_log hposB (hmono.trans hht)
    have hpp : (∏ v, opNormAt b X b' X' v φ ^ (2 * rkK A)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hop v).ne'
    rw [Real.log_mul hpp hposA.ne', Real.log_prod (fun v _ => pow_ne_zero _ (hop v).ne')] at h1
    have h2 : (∑ v, Real.log (opNormAt b X b' X' v φ ^ (2 * rkK A))) =
        (rkK A : ℝ) * (∑ v, Real.log (opNormAt b X b' X' v φ ^ 2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Real.log_pow, Real.log_pow]
      push_cast
      ring
    rw [h2] at h1
    exact h1
  rw [ms_mu_eq b X hX hA hA0, ms_mu_eq b' X' hX' hB hB0, hrk]
  unfold htMap
  have hf : (0 : ℝ) < nPl K := by exact_mod_cast ms_nPl_pos
  have hj' : (0 : ℝ) < rkK A := by exact_mod_cast hj
  set S := ∑ v, Real.log (opNormAt b X b' X' v φ ^ 2) with hS
  have key : (Real.log (ht b' X' B) - Real.log (ht b X A)) / ((nPl K : ℝ) * (rkK A : ℝ)) ≤
      1 / (nPl K : ℝ) * S := by
    rw [div_le_iff₀ (mul_pos hf hj')]
    have : 1 / (nPl K : ℝ) * S * ((nPl K : ℝ) * (rkK A : ℝ)) = (rkK A : ℝ) * S := by
      field_simp
    rw [this]
    linarith
  rw [sub_div] at key
  linarith

theorem scale_sandwich_bound : ScaleSandwich := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX A B n hA hA0 hn hBA hnA
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    apply hA0
    rw [eq_bot_iff]
    intro x _
    have : x = 0 := b.repr.injective (by ext i; exact (h.false i).elim)
    exact (Submodule.mem_bot _).2 this
  have hBfg : B.FG := by
    have : IsNoetherian (𝓞 K) A := isNoetherian_of_fg_of_noetherian A hA
    exact (isNoetherian_submodule.1 this) B hBA
  set φ : V →ₗ[K] V := (n : K) • (LinearMap.id : V →ₗ[K] V) with hφ
  have hφx : ∀ x, φ x = (n : 𝓞 K) • x := by
    intro x
    simp [hφ, Nat.cast_smul_eq_nsmul]
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  have hinj : Function.Injective φ := by
    intro x y hxy
    simp only [hφ, LinearMap.smul_apply, LinearMap.id_apply] at hxy
    exact smul_right_injective V hnK hxy
  have hmap : A.map (φ.restrictScalars (𝓞 K)) ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    show φ x ∈ B
    rw [hφx]
    exact hnA x hx
  have hmap0 : A.map (φ.restrictScalars (𝓞 K)) ≠ ⊥ := by
    intro h
    apply hA0
    rw [eq_bot_iff]
    intro x hx
    have h1 : φ x ∈ A.map (φ.restrictScalars (𝓞 K)) := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    exact (Submodule.mem_bot _).2 (hinj (by rw [h1, map_zero]))
  have hB0 : B ≠ ⊥ := fun h => hmap0 (le_bot_iff.mp (h ▸ hmap))
  have hrk : rkK B = rkK A := by
    have hspan : Submodule.span K (B : Set V) = Submodule.span K (A : Set V) := by
      apply le_antisymm (Submodule.span_mono hBA)
      rw [Submodule.span_le]
      intro x hx
      have h1 : (n : K) • x ∈ Submodule.span K (B : Set V) := by
        apply Submodule.subset_span
        have := hnA x hx
        rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul K] at this
      have h2 := Submodule.smul_mem _ ((n : K)⁻¹) h1
      rwa [smul_smul, inv_mul_cancel₀ hnK, one_smul] at h2
    unfold rkK
    rw [hspan]
  have hht := ms_htMap_nat b X hX n
  have hht1 : htMap b X b X (LinearMap.id : V →ₗ[K] V) = 0 := by
    have := ms_htMap_nat b X hX 1
    simpa using this
  have hmapid : B.map ((LinearMap.id : V →ₗ[K] V).restrictScalars (𝓞 K)) = B := by
    ext x
    simp
  refine ⟨hrk, ?_, ?_, ?_, ?_⟩
  · have := map_slope_mu K V ι V ι b X b X hX hX LinearMap.id B A hBfg hA hB0
      (Function.injective_id.injOn) (by rw [hmapid]; exact hBA) hrk.symm
    rw [hht1] at this
    linarith
  · have := map_slope_mu K V ι V ι b X b X hX hX φ A B hA hBfg hA0 hinj.injOn hmap hrk
    rw [hht] at this
    exact this
  · have := ((slope_inequality_mean K V ι V ι b X b X hX hX LinearMap.id B hBfg
      (by rw [hmapid]; exact hB0)).2 A hA (by rw [hmapid]; exact hBA)).2 Function.injective_id.injOn
    rw [hht1] at this
    linarith
  · have := ((slope_inequality_mean K V ι V ι b X b X hX hX φ A hA hmap0).2 B hBfg hmap).2 hinj.injOn
    rw [hht] at this
    exact this

theorem levelCompare_statement : LevelCompare := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX R R' h hR hR'0 hh hle hhR
  have hR0 : R ≠ ⊥ := fun e => hR'0 (le_bot_iff.mp (e ▸ hle))
  have hR'fg : R'.FG := by
    have : IsNoetherian (𝓞 K) R := isNoetherian_of_fg_of_noetherian R hR
    exact (isNoetherian_submodule.1 this) R' hle
  obtain ⟨-, h1, h2, h3, h4⟩ := scale_sandwich_bound K V ι b X hX R R' h hR hR0 hh hle hhR
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.2 hh'
  have htw := twist K V ι b X (fun _ => Real.sqrt h) hX (fun _ => hs) R' hR'fg
  obtain ⟨e1, e2, -⟩ := htw.2.2.1 hR'0
  have hf : (0 : ℝ) < nPl K := by exact_mod_cast ms_nPl_pos
  have ht : 2 * ((1 / (nPl K : ℝ)) * ∑ _v : InfinitePlace K, Real.log (Real.sqrt h)) =
      Real.log h := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.log_sqrt hh'.le]
    unfold nPl at hf ⊢
    field_simp
  have e1' : muDef b (scaleFrame (Real.sqrt h) X) R' = muDef b X R' + Real.log h := by
    rw [← ht]; exact e1
  have e2' : muMaxDef b (scaleFrame (Real.sqrt h) X) R' = muMaxDef b X R' + Real.log h := by
    rw [← ht]; exact e2
  rw [e1', e2']
  constructor <;> rw [abs_le] <;> constructor <;> linarith

end Formalism.BranchingDeterminantCap

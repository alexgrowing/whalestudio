import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlMapStandardLatticeEqIffMemGLintAdicStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlMapDiagUniformizerElementarySublatticeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsMore

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG

namespace GlobalTheory.ElemCartan

section Dvr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] {r : ℕ}

theorem coord_of_mem_std {x : Fin r → K} (hx : x ∈ (std O K r).1) (i : Fin r) :
    ∃ a : O, algebraMap O K a = x i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases h : i = j
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp [h]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [ha, hb]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by simp [ha, Algebra.smul_def]⟩

end Dvr

section Adic

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem zpow_mem_iff {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (m : ℤ) :
    ϖ ^ m ∈ w.adicCompletionIntegers E ↔ 0 ≤ m := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_zpow₀, hϖ, ← WithZero.coe_zpow,
    ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zsmul, ← ofAdd_zero, Multiplicative.ofAdd_le,
    smul_eq_mul]
  omega

theorem ne_zero_of_unif {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) : ϖ ≠ 0 := by
  intro h
  rw [IsUnifV, h, map_zero] at hϖ
  exact WithZero.zero_ne_coe hϖ

theorem antitone_zero_one {n j : ℕ} (a : Fin n → ℤ) (ha : Antitone a)
    (h01 : ∀ i, a i = 0 ∨ a i = 1)
    (hS : (Finset.univ.filter fun i => a i = 1).card = j) (i : Fin n) :
    a i = 1 ↔ (i : ℕ) < j := by
  first
  | exact @_root_.GlobalTheory.ClosedSubgroupCriterion.main
  | exact _root_.GlobalTheory.ClosedSubgroupCriterion.main
  | (apply _root_.GlobalTheory.ClosedSubgroupCriterion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosedSubgroupCriterion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosedSubgroupCriterion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosedSubgroupCriterion.main ..)

end Adic

theorem mem_doubleCoset_of_subElem : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (j : ℕ), j ≤ n → ∀ (g : GL (Fin n) (w.adicCompletion E)), haveI := GlobalTheory.RowSatakeBound.finite_residue w; glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈ Subtype.val '' subElem j (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) → ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w), (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
  intro E _ _ w n ϖ hϖ j _ g hg
  haveI := GlobalTheory.RowSatakeBound.finite_residue w
  obtain ⟨M₀, hM, hMg⟩ := hg
  set L := std (w.adicCompletionIntegers E) (w.adicCompletion E) n with hLdef
  set M : Lat (w.adicCompletionIntegers E) (w.adicCompletion E) n := M₀ with hMdef
  have hϖ0 := ne_zero_of_unif w hϖ
  have hϖO : ϖ ∈ Ov E w := by
    have := (zpow_mem_iff w hϖ 1).2 zero_le_one
    simpa using this
  obtain ⟨a, ha, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp E w n ϖ hϖO hϖ g
  have hs₁ : glMap k₁⁻¹ L.1 = L.1 := (GlobalTheory.T.glMap_standardLattice_eq_iff_mem_GLint_adic E w n k₁⁻¹).2 (inv_mem hk₁)
  have hs₂ : glMap k₂⁻¹ L.1 = L.1 := (GlobalTheory.T.glMap_standardLattice_eq_iff_mem_GLint_adic E w n k₂⁻¹).2 (inv_mem hk₂)
  set D : GL (Fin n) (w.adicCompletion E) := k₁⁻¹ * g * k₂⁻¹ with hDdef
  have hD : (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = diagPow E w ϖ a := by
    rw [hDdef, Units.val_mul, Units.val_mul, e]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

  have hDL : glMap D L.1 = (k₁⁻¹ • M).1 := by
    rw [smul_def, glLat_val, hMg, hDdef, glMap_mul, glMap_mul, hs₂]
  have hMD : k₁⁻¹ • M ∈ subElem j L := by
    have h := (smul_mem_subElem_iff k₁⁻¹ j M L).2 hM
    have hL : k₁⁻¹ • L = L := GlobalTheory.LatHecke.Lat.ext (by rw [smul_def, glLat_val, hs₁])
    rwa [hL] at h
  obtain ⟨⟨hle, hidx⟩, hmax⟩ := hMD
  rw [← hDL] at hle hidx hmax
  have hDe : ∀ (x : Fin n → w.adicCompletion E) (i : Fin n),
      Matrix.toLin' (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x i = ϖ ^ (a i) * x i := by
    intro x i
    rw [Matrix.toLin'_apply, hD, diagPow, Matrix.mulVec_diagonal]

  have hpos : ∀ i, 0 ≤ a i := by
    intro i
    have hmem : Matrix.toLin' (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Pi.basisFun (w.adicCompletion E) (Fin n) i) ∈ glMap D L.1 :=
      ⟨_, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := coord_of_mem_std (hle hmem) i
    rw [hDe] at hc
    simp only [Pi.basisFun_apply, Pi.single_eq_same, mul_one] at hc
    rw [← zpow_mem_iff w hϖ, ← hc]
    exact c.2

  have hle1 : ∀ i, a i ≤ 1 := by
    intro i
    have hϖm : (⟨ϖ, hϖO⟩ : w.adicCompletionIntegers E) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) := by
      apply (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))))).2
      show Valued.v ϖ < 1
      rw [hϖ, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
      omega
    have hmem : (⟨ϖ, hϖO⟩ : w.adicCompletionIntegers E) • Pi.basisFun (w.adicCompletion E) (Fin n) i ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) • L.1 :=
      Submodule.smul_mem_smul hϖm (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨x, hx, hxe⟩ := hmax hmem
    obtain ⟨c, hc⟩ := coord_of_mem_std hx i
    have hxi := congrFun hxe i
    simp only [LinearMap.coe_restrictScalars] at hxi
    rw [hDe] at hxi
    have hval : (((⟨ϖ, hϖO⟩ : w.adicCompletionIntegers E) • Pi.basisFun (w.adicCompletion E) (Fin n) i) i) = ϖ := by
      simp [Algebra.smul_def]
    rw [hval] at hxi
    have hx' : x i = ϖ ^ (1 - a i) := by
      rw [zpow_sub₀ hϖ0, zpow_one, eq_div_iff (zpow_ne_zero (a i) hϖ0), mul_comm]
      exact hxi
    rw [← sub_nonneg, ← zpow_mem_iff w hϖ, ← hx', ← hc]
    exact c.2
  have h01 : ∀ i, a i = 0 ∨ a i = 1 := fun i => by
    have := hpos i; have := hle1 i; omega

  set S : Finset (Fin n) := Finset.univ.filter fun i => a i = 1 with hSdef
  have hdiag : (fun i => ϖ ^ (a i)) = fun i => if i ∈ S then ϖ else 1 := by
    funext i
    rcases h01 i with h | h <;> simp [hSdef, h]
  have hD' : (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal fun i => if i ∈ S then ϖ else 1 := by
    rw [hD, diagPow, hdiag]
  obtain ⟨M₂, ⟨⟨-, hidx₂⟩, -⟩, hM₂⟩ := GlobalTheory.T.glMap_diagUniformizer_elementarySublattice E w n ϖ hϖ S D hD'
  rw [hM₂] at hidx₂
  have hcard : S.card = j := by
    have h := hidx₂.symm.trans hidx
    exact Nat.pow_right_injective (two_le_qRes (O := w.adicCompletionIntegers E)) h
  have hkey := antitone_zero_one a ha h01 hcard
  refine ⟨k₁, hk₁, k₂, hk₂, ?_⟩
  rw [e]
  congr 2
  rw [diagPow, diagJ]
  congr 1
  funext i
  by_cases hi : (i : ℕ) < j
  · rw [if_pos hi, (hkey i).2 hi, zpow_one]
  · rw [if_neg hi]
    have : a i = 0 := (h01 i).resolve_right fun h => hi ((hkey i).1 h)
    rw [this, zpow_zero]

end GlobalTheory.ElemCartan

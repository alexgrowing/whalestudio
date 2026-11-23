import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteTopologyRatN
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSlowlyIncreasing

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.AutGrowth

namespace GlobalTheory.ConstTermGrowth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_pInf_alt : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_mapInf : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_alt)

theorem continuous_mapFin : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))

omit [IsTotallyComplex E] in

theorem height_mul_left_le {Ω : Set (GL (Fin a) (Cinf E))} (hΩ : IsCompact Ω) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c ∈ Ω, ∀ y : GL (Fin a) (Cinf E), height (c * y) ≤ B * height y := by
  have c1 : Continuous fun u : GL (Fin a) (Cinf E) => toL u.val :=
    (Units.continuous_val : Continuous fun u : GL (Fin a) (Cinf E) => u.val)
  have c2 : Continuous fun u : GL (Fin a) (Cinf E) => toL (u⁻¹).val :=
    (Units.continuous_coe_inv : Continuous fun u : GL (Fin a) (Cinf E) => (u⁻¹).val)
  obtain ⟨M1, h1⟩ := hΩ.exists_bound_of_continuousOn c1.continuousOn
  obtain ⟨M2, h2⟩ := hΩ.exists_bound_of_continuousOn c2.continuousOn
  have M0 : (0 : ℝ) ≤ max 0 (max M1 M2) := le_max_left _ _
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  refine ⟨1 + a * max 0 (max M1 M2), by positivity, fun c hc y => ?_⟩
  have m1 : ‖toL c.val‖ ≤ max 0 (max M1 M2) := (h1 c hc).trans ((le_max_left _ _).trans (le_max_right _ _))
  have m2 : ‖toL (c⁻¹).val‖ ≤ max 0 (max M1 M2) := (h2 c hc).trans ((le_max_right _ _).trans (le_max_right _ _))
  have e2 : ((c * y)⁻¹ : GL (Fin a) (Cinf E)).val = (y⁻¹).val * (c⁻¹).val := by
    rw [_root_.mul_inv_rev]; rfl
  have p1 := norm_toL_mul_le c.val y.val
  have p2 := norm_toL_mul_le (y⁻¹).val (c⁻¹).val
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have q1 : (a : ℝ) * (‖toL c.val‖ * ‖toL y.val‖) ≤ a * max 0 (max M1 M2) * ‖toL y.val‖ := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right m1 n1) ha
  have q2 : (a : ℝ) * (‖toL (y⁻¹).val‖ * ‖toL (c⁻¹).val‖) ≤ a * max 0 (max M1 M2) * ‖toL (y⁻¹).val‖ := by
    calc (a : ℝ) * (‖toL (y⁻¹).val‖ * ‖toL (c⁻¹).val‖) ≤ a * (‖toL (y⁻¹).val‖ * max 0 (max M1 M2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m2 n2) ha
      _ = _ := by ring
  have aM : (0 : ℝ) ≤ a * max 0 (max M1 M2) := by positivity
  unfold height
  rw [show toL (c * y).val = toL (c.val * y.val) from rfl, e2]
  nlinarith

theorem uniform_growth (φ : Sm E a) (hopen : IsOpen {k | finRep E a k φ = φ})
    (hgr : ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N)
    {Ω : Set (GA E a)} (hΩ : IsCompact Ω) :
    ∃ (C : ℝ) (N : ℕ), ∀ h ∈ Ω, ∀ y, ‖φ.1 (h * infGL E a y)‖ ≤ C * height y ^ N := by
  have hS : ∀ s : GL (Fin a) (Af E), finRep E a s φ = φ → ∀ x, φ.1 (x * finGL E a s) = φ.1 x := fun s hs x => by
    have := congrFun (congrArg Subtype.val hs) x
    exact this
  have hU : ∀ t : GL (Fin a) (Af E), IsOpen ((fun k => t⁻¹ * k) ⁻¹' {k | finRep E a k φ = φ}) := fun t =>
    hopen.preimage (continuous_const.mul continuous_id)
  have hKf : IsCompact (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E) '' Ω) := hΩ.image continuous_mapFin
  obtain ⟨T, hT⟩ := hKf.elim_finite_subcover (fun t => (fun k => t⁻¹ * k) ⁻¹' {k | finRep E a k φ = φ}) hU
    (fun k _ => Set.mem_iUnion.2 ⟨k, by
      change finRep E a (k⁻¹ * k) φ = φ
      rw [inv_mul_cancel, map_one]; rfl⟩)
  choose C N hCN using hgr
  obtain ⟨B, hB0, hB⟩ := height_mul_left_le (hΩ.image (continuous_mapInf (E := E) (a := a)))
  refine ⟨∑ t ∈ T, |C (finGL E a t)| * B ^ N (finGL E a t), ∑ t ∈ T, N (finGL E a t), fun h hh y => ?_⟩
  obtain ⟨t, htT, hkt⟩ := Set.mem_iUnion₂.1 (hT ⟨h, hh, rfl⟩)
  have e : h * infGL E a y = finGL E a t * infGL E a (Matrix.GeneralLinearGroup.map (pInf E) h * y) *
      finGL E a (t⁻¹ * Matrix.GeneralLinearGroup.map (pFin E) h) := by
    apply ga_ext
    · simp only [map_mul, pInf_infGL, pInf_finGL, one_mul, mul_one]
    · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul, mul_one, mul_inv_cancel_left]
  rw [e, hS _ hkt]
  have hcy := hB _ ⟨h, hh, rfl⟩ y
  have h0 := one_le_height (Matrix.GeneralLinearGroup.map (pInf E) h * y)
  have hy := one_le_height y
  calc ‖φ.1 (finGL E a t * infGL E a (Matrix.GeneralLinearGroup.map (pInf E) h * y))‖
      ≤ C (finGL E a t) * height (Matrix.GeneralLinearGroup.map (pInf E) h * y) ^ N (finGL E a t) := hCN _ _
    _ ≤ |C (finGL E a t)| * (B * height y) ^ N (finGL E a t) :=
        mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (by linarith) hcy _) (pow_nonneg (by linarith) _) (abs_nonneg _)
    _ = |C (finGL E a t)| * B ^ N (finGL E a t) * height y ^ N (finGL E a t) := by ring
    _ ≤ |C (finGL E a t)| * B ^ N (finGL E a t) * height y ^ (∑ t ∈ T, N (finGL E a t)) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy
          (Finset.single_le_sum (f := fun t => N (finGL E a t)) (fun _ _ => Nat.zero_le _) htT))
          (mul_nonneg (abs_nonneg _) (pow_nonneg hB0 _))
    _ ≤ (∑ t ∈ T, |C (finGL E a t)| * B ^ N (finGL E a t)) * height y ^ (∑ t ∈ T, N (finGL E a t)) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun t => |C (finGL E a t)| * B ^ N (finGL E a t))
          (fun _ _ => mul_nonneg (abs_nonneg _) (pow_nonneg hB0 _)) htT) (pow_nonneg (by linarith) _)

theorem norm_constTerm_le : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N) →
    ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖∫ x in 𝓕, φ.1 (unip x * (g * infGL E a y)) ∂μ‖ ≤ C * height y ^ N := by
  intro E _ _ _ a r _ _ μ 𝓕 _ _ h1 φ hleft hopen hgr g
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E a r
  have hc : Continuous fun x : BlockIx a r → Ad E => unip x * g :=
    GlobalTheory.CuspRep.CuspidalL2GL.continuous_unip.mul continuous_const
  obtain ⟨C, N, hC⟩ := uniform_growth φ hopen hgr (hK.image hc)
  refine ⟨C, N, fun y => ?_⟩
  have hb : ∀ x : BlockIx a r → Ad E, ‖φ.1 (unip x * (g * infGL E a y))‖ ≤ C * height y ^ N := by
    intro x
    obtain ⟨γ, ⟨z, rfl⟩, hγ⟩ := hcov x
    have hu : unip ((AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) z) =
        ratGL E a (unip z) := unip_algebraMap z
    have e : φ.1 (unip (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r) z + x) * g *
        infGL E a y) = φ.1 (unip x * (g * infGL E a y)) := by
      rw [unip_add, hu]
      simp only [mul_assoc]
      exact hleft _ _
    rw [← e]
    exact hC _ ⟨_, hγ, rfl⟩ y
  have hfin : μ 𝓕 < ⊤ := by rw [h1]; exact ENNReal.one_lt_top
  calc _ ≤ C * height y ^ N * (μ 𝓕).toReal := norm_setIntegral_le_of_norm_le_const hfin (fun x _ => hb x)
    _ = C * height y ^ N := by rw [h1]; simp

end GlobalTheory.ConstTermGrowth

end

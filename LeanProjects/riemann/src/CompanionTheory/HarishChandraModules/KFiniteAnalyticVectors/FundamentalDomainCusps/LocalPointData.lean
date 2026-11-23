import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.LogNormEstimates
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.MemIntegersOfMemIntAd

open Matrix MeasureTheory NumberField Topology Module
open scoped TensorProduct

noncomputable section

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.SG.Pf.Tau PIW.AdelClassFin

theorem atV_sum (I : AutInst) (v : InfinitePlace I.F) {d : ℕ} (a : Fin d → I.E) (w : Fin d → Fin I.n → I.E) :
    atV I v (∑ i, a i • w i) = ∑ i, I.φ v (a i) • atV I v (w i) := by
  simp only [atV, ← mulVec_smul, ← mulVec_sum]; congr 1; funext i; simp [map_sum]

theorem exists_near (I : AutInst) : ∃ C : ℝ, 0 < C ∧ ∀ β : InfinitePlace I.F → ℂ,
    ∃ a : I.E, IsIntegral ℤ a ∧ ∀ v, ‖β v - I.φ v a‖ ≤ C := by
  let b := embeddingBasis I
  refine ⟨∑ k, ‖b k‖ + 1, by positivity, fun β => ⟨∑ k, (⌊b.repr β k⌋ : I.E) * integralBasis I.E k,
    IsIntegral.sum _ fun k _ => (isIntegral_intCast _).mul ?_, fun v => ?_⟩⟩
  · rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
  · have e : β v - I.φ v (∑ k, (⌊b.repr β k⌋ : I.E) * integralBasis I.E k) =
        ∑ k, ((Int.fract (b.repr β k) : ℝ) : ℂ) * b k v := by
      rw [show β v = (∑ k, b.repr β k • b k) v by rw [b.sum_repr β], map_sum, Finset.sum_apply,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Int.fract, map_mul, map_intCast, Pi.smul_apply, Complex.real_smul]
      simp only [b, embeddingBasis_apply]
      push_cast
      ring
    rw [e]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => ?_).trans (le_add_of_nonneg_right zero_le_one))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le).trans (norm_le_pi_norm _ v)

theorem covolume_span : CovSpan := by
  intro I
  obtain ⟨C, hC, hn⟩ := exists_near I
  refine ⟨(I.n + 1) * C, by positivity, fun y d w s hd hs hw b hb => ?_⟩
  have h1 : ∀ v, ∃ β : Fin d → ℂ, ∑ i, β i • atV I v (w i) = b v := fun v => by
    refine (Submodule.mem_span_range_iff_exists_fun ℂ).1 (Submodule.span_le.2 ?_ (hb v))
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun I.E).1 hu
    rw [atV_sum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose β hβ using h1
  choose a ha hae using fun i => hn fun v => β v i
  refine ⟨∑ i, a i • w i, fun j => ?_, Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), (pi_norm_le_iff_of_nonneg (by positivity)).2 fun v => ?_⟩
  · rw [Finset.sum_apply]
    exact IsIntegral.sum _ fun i _ => (ha i).mul ((hw i).1 j)
  · have e : ((fun v => uMat (y v)⁻¹ *ᵥ b v) - vecAt I y (∑ i, a i • w i)) v =
        ∑ i, (β v i - I.φ v (a i)) • vecAt I y (w i) v := by
      simp only [Pi.sub_apply, vecAt, ← hβ v, atV_sum, mulVec_sum, mulVec_smul, sub_smul, Finset.sum_sub_distrib]
    rw [e]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (C * s) fun i _ => ?_).trans ?_)
    · rw [norm_smul]
      exact mul_le_mul (hae i v) ((norm_le_pi_norm _ v).trans (hw i).2) (norm_nonneg _) hC.le
    · rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
      have : (d : ℝ) ≤ I.n + 1 := by exact_mod_cast hd.trans (Nat.le_succ _)
      gcongr

theorem exists_sandwich (I : AutInst) : ∃ c : ℕ, 1 ≤ c ∧ (∀ l ∈ I.L, (c : I.E) • l ∈ IntV I) ∧
    ∀ u ∈ IntV I, (c : I.E) • u ∈ I.L := by
  classical
  obtain ⟨d, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.1 I.L_fg
  obtain ⟨c₁, hc₁, h₁⟩ := exists_denD fun p : Fin d × Fin I.n => w p.1 p.2
  choose e he he' using fun j : Fin I.n => TraceIntegralityAlt.exists_nat_smul_mem_L I (Pi.single j 1)
  have hp : 1 ≤ ∏ j, e j := Finset.one_le_prod' fun j _ => he j
  refine ⟨c₁ * ∏ j, e j, Nat.mul_pos hc₁ hp, fun l hl i => ?_, fun u hu => ?_⟩
  · rw [← hw] at hl
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hl
    rw [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
    refine IsIntegral.sum _ fun k _ => ?_
    have : ((c₁ * ∏ j, e j : ℕ) : I.E) * (a k • w k) i = ((∏ j, e j : ℕ) : I.E) * (a k : I.E) * (c₁ * w k i) := by
      rw [Pi.smul_apply, Algebra.smul_def, Nat.cast_mul]; ring
    rw [this]
    exact ((isIntegral_natCast _).mul (RingOfIntegers.isIntegral_coe _)).mul (h₁ (k, i))
  · conv => arg 2; rw [← Finset.univ_sum_single u, Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem e (Finset.mem_univ j)
    have h2 := I.L.smul_mem (⟨u j, hu j⟩ : 𝓞 I.E) (TraceIntegralityAlt.natCast_smul_mem I (c₁ * q) (he' j))
    convert h2 using 1
    funext i
    rw [hq]
    show _ = u j * (((c₁ * q : ℕ) : I.E) * ((e j : I.E) * (Pi.single j (1 : I.E) : Fin I.n → I.E) i))
    by_cases hi : i = j
    · subst hi; simp; ring
    · simp [Pi.single_eq_of_ne hi]

theorem iv_mulVec (I : AutInst) (A : Matrix (Fin I.n) (Fin I.n) I.E) (l : Fin I.n → I.E) :
    A.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *ᵥ iv I l = iv I (A *ᵥ l) := by
  funext i
  simp [iv, mulVec, dotProduct, map_sum]

theorem cong_Lf (I : AutInst) {c g : ℕ} (h1 : ∀ l ∈ I.L, (c : I.E) • l ∈ IntV I) (h2 : ∀ u ∈ IntV I, (c : I.E) • u ∈ I.L)
    {A : Matrix (Fin I.n) (Fin I.n) I.E} (hA : Cong I (g * c * c) A) : ∀ y ∈ I.Lf, ∃ z ∈ I.Lf,
      (A.map (Formalism.UG.inclE (F := I.F) (Af I.F)) - 1) *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • z := by
  choose a ha ha' using hA
  let B : Matrix (Fin I.n) (Fin I.n) I.E := ((c : I.E) * c) • Matrix.of a
  have hB : I.L ≤ DictGen.lamM I (B.map (Formalism.UG.inclE (F := I.F) (Af I.F))) := fun l hl => by
    show _ ∈ I.Lf
    rw [iv_mulVec]
    refine DictGen.iv_mem I ?_
    have : B *ᵥ l = (c : I.E) • (Matrix.of a *ᵥ ((c : I.E) • l)) := by
      simp only [B, smul_mulVec, mulVec_smul, smul_smul]
    rw [this]
    refine h2 _ fun i => ?_
    show IsIntegral ℤ (∑ j, a i j * ((c : I.E) • l) j)
    exact IsIntegral.sum _ fun j _ => (ha i j).mul (h1 l hl j)
  refine fun y hy => ⟨_, DictGen.mulVec_mem_of_le I hB y hy, ?_⟩
  rw [← smul_mulVec]
  congr 1
  ext i j
  have := congrArg (Formalism.UG.inclE (F := I.F) (Af I.F)) (ha' i j)
  rw [Matrix.sub_apply, map_sub] at this
  rw [Matrix.sub_apply, Matrix.map_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply]
  rw [Matrix.one_apply, apply_ite (Formalism.UG.inclE (F := I.F) (Af I.F)), map_one, map_zero] at this
  rw [this]
  simp only [B, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, map_mul, map_natCast, Nat.cast_mul]
  ring

theorem congruence_subgroup_compact_open : CongK := by
  intro I U hU
  obtain ⟨g, hg, hsub⟩ := I.topf_basis U hU
  obtain ⟨c, hc, h1, h2⟩ := exists_sandwich I
  refine ⟨g * c * c, Nat.mul_pos (Nat.mul_pos hg hc) hc, ?_⟩
  rintro x ⟨γ, hγ, hx⟩
  have hf : Formalism.UG.bc (Formalism.UG.inclE (F := I.F) (Af I.F)) γ ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) :=
    Formalism.UG.Final.RatPtsLe I.F I.E (Fin I.n) I.cm.sig I.J (Af I.F) (Subgroup.mem_map_of_mem _ hγ.1)
  have st : ∀ {A : Matrix (Fin I.n) (Fin I.n) I.E}, Cong I (g * c * c) A → ∀ y ∈ I.Lf,
      A.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *ᵥ y ∈ I.Lf := fun hA y hy => by
    obtain ⟨z, hz, e⟩ := cong_Lf I h1 h2 hA y hy
    rw [sub_mulVec, one_mulVec, sub_eq_iff_eq_add] at e
    rw [e]
    exact I.Lf.add_mem (DictGen.natSmul_mem I g hz) hy
  refine ⟨⟨_, hf⟩, hsub ⟨fun y => ⟨st hγ.2.1 y, fun hy => ?_⟩, cong_Lf I h1 h2 hγ.2.1⟩, γ, hγ.1, hx, rfl⟩
  have := st hγ.2.2 _ hy
  change _ *ᵥ ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) *ᵥ y) ∈ I.Lf at this
  rwa [mulVec_mulVec, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _), one_mulVec] at this

end CompanionTheory.D.gk.RF

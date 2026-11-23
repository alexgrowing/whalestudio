import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConduct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedZetaSumGLCosets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumQuotientTransportStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightInvariantEqSumOpenSubgroupCosetsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupIsoGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingUnramifiedHeckeEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDoublingZetaValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalUnramifiedIntegralValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLFactorUnramifiedCharacterStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)

noncomputable section

namespace GlobalTheory.ThK.Bot.SplitVal

theorem integral_mul_conj_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    [MeasurableSpace (κ → AF F)] [hB : BorelSpace (κ → AF F)] (m : Measure (κ → AF F)) (hm : m.IsAddHaarMeasure)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (h0 : Φ ≠ 0) : ∫ x, Φ x * starRingEnd ℂ (Φ x) ∂m ≠ 0 := by
  obtain ⟨rfl⟩ := hB
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  have hL : MemLp Φ 2 m := GlobalTheory.WeilM.schA_memLp_two F κ m hm Φ hΦ
  have hc := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ
  have hi : Integrable (fun x => ‖Φ x‖ ^ 2) m := (memLp_two_iff_integrable_sq_norm hL.1).1 hL
  have e : ∫ x, Φ x * starRingEnd ℂ (Φ x) ∂m = ((∫ x, ‖Φ x‖ ^ 2 ∂m : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e, Complex.ofReal_ne_zero]
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  exact (integral_pos_of_integrable_nonneg_nonzero (x := x) (hc.norm.pow 2) hi (fun y => sq_nonneg ‖Φ y‖)
    (by simpa using hx)).ne'

theorem pow_combine {q : ℕ} (hq : 0 < q) (a : ℤ) (d : ℕ) (z : ℂ) :
    (((q : ℝ) ^ (-((d : ℝ) / 2) * (a : ℝ)) : ℝ) : ℂ) * ((((q : ℝ) ^ (-a) : ℝ)) : ℂ) ^ z =
      (q : ℂ) ^ (-((d : ℂ) / 2 + z) * (a : ℂ)) := by
  have h0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [← Real.rpow_intCast, ← Complex.cpow_mul_ofReal_nonneg h0, Complex.ofReal_cpow h0, Complex.ofReal_natCast,
    ← Complex.cpow_add _ _ h1]
  congr 1
  push_cast
  ring

theorem zetaOn_split : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ → min r s' = 0 → min r₁ s₁ = 0 → 1 ≤ n → n < d → Even d →
    ∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ K : Subgroup (UA σ X.J), IsStab B K → ∀ f ∈ M.Pol B.ψ B.emb, ∀ φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → pure f φ ≠ 0 →
    ∀ v : Pl F, (¬ ∃ w, Formalism.UG.IsInertAt F E v w) → (∀ w ∈ aboveF (L := E) F v, UnrAt χW w) → φ v = M.vac v →
    ∀ μ : Measure (UAtSub σ X (evFin F v)), μ.IsHaarMeasure → μ {g | g.1 ∈ K} = 1 → ∀ s : ℂ, (n : ℝ) / 2 < s.re →
      zetaOn m om (pure f φ) i K₂ _ μ s = (∏ j ∈ Finset.range n, Lv (charFam χW) v (s + (n : ℂ) / 2 - (j : ℂ))) * denInv E n v s := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s' r₁ s₁ hP _ _ _ _ _ X₂ i K₂ hD _ _ m hm K hK f _ φ hSB hev hne v hv
    hU hφ μ hμ hμK s hs
  classical
  have hcm := hP.base.cm
  haveI := hP.base.unram
  have hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v :=
    GlobalTheory.LFun.isUnram_iff.2 fun w _ => Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
  obtain ⟨w, w', hww, h1, h2⟩ := GlobalTheory.LFun.isSplit_iff.1 ((GlobalTheory.LFun.InertChart.isSplit_or_isInertAt hun).resolve_right hv)
  obtain ⟨t, -⟩ := (GlobalTheory.AdelicU.existsUnique_splitPrime_eq hcm hww h1 h2).exists
  haveI := hP.herm.lat
  obtain ⟨b, hb⟩ := exists_isSplitBasis t X.L hcm
  have hUt : UnrAt χW (splitPrime t) := hU _ (GlobalTheory.LFun.mem_aboveF.2 (splitPrime_under t))
  obtain ⟨e, he, heK⟩ := GlobalTheory.T.local_unitary_group_iso_GL F E σ B n X hcm ⟨hP.herm.herm, GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hP.herm⟩
    hP.herm.lat v (GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B n X r s' hP.base hP.herm v) K hK t b hb
  have hstd : ∀ᶠ w in cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    (hev.and hP.good.std).mono fun w hw => hw.1.trans hw.2
  obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  have hR : ∀ φ' ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ' ρ := fun φ' hφ' => ⟨hρ, by
    rw [hρt]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) ?_
    · by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ'
      · rw [Function.update_of_ne hw]; exact hSB w
    · filter_upwards [hstd, Filter.eventually_cofinite_ne v] with w hw hne
      rw [Function.update_of_ne hne]; exact hw⟩
  have hpure : pure f φ = tens (evFin F v) (M.vac v) ρ := by rw [← hφ, hρt, Function.update_eq_self]
  have hsch : pure f φ ∈ schA F (Fin n × Fin d) := GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  have hc1 : coef m om (pure f φ) 1 ≠ 0 := by
    have := integral_mul_conj_ne_zero m hm hsch hne
    unfold coef
    rwa [show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one]
  obtain ⟨ϖ₀, hϖ₀⟩ := GlobalTheory.LFun.exists_isUnifV v
  let ϖ : (Fv F v)ˣ := Units.mk0 ϖ₀ (GlobalTheory.LFun.SatCompare.ne_zero_of_isUnifV hϖ₀)
  obtain ⟨hsm, -, hunr⟩ := GlobalTheory.ChrWLocal.chrW_local F E χW hP.hW v t
  have hq : 0 < qV F v := Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero v)
  set I : UAtSub σ X (evFin F v) → ℂ := fun g => coef m om (pure f φ) g.1 / coef m om (pure f φ) 1 *
    (((hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (g.1, 1)) : ℝ≥0) : ℝ) : ℂ) ^
      (s - ((d : ℂ) - (n : ℂ)) / 2) with hI
  obtain ⟨hinv, hsum⟩ := GlobalTheory.T.spherical_unramified_integral_value F v n s hs (chrW χW t ϖ) (fun x => I (e.symm x)) (hsm.2 _) (by
    intro ϖ' hϖ' a T hT k₁ hk₁ k₂ hk₂
    have hg : GlobalTheory.KSplit.locMat t b (e.symm (k₁ * T * k₂)).1 = k₁ * T * k₂ := by rw [← he, e.apply_symm_apply]
    have hz : chrW χW t ϖ' = chrW χW t ϖ := by
      have := hunr.2 hUt (ϖ' * ϖ⁻¹) ((GlobalTheory.ChrWLocal.valuation_eq_one_iff _).2 (by
        have a1 : Valued.v ϖ'.1 = Valued.v ϖ.1 := Eq.trans hϖ' (Eq.symm hϖ₀)
        rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, a1, mul_inv_cancel₀ (by simp)]))
      rwa [map_mul, map_inv, mul_inv_eq_one] at this
    simp only [hI]
    rw [GlobalTheory.T.doubling_unramified_hecke_eigen F E σ B n X r s' hP.base hP.herm X₂ i K₂ hD v t b hb ϖ' hϖ' a T hT k₁ hk₁ k₂ hk₂ _ (e.symm _).2 hg]
    rw [hpure] at hc1 ⊢
    rw [GlobalTheory.T.local_doubling_zeta_value hKP.base F E σ B n d X W M χX χW om r s' r₁ s₁ hP m hm v ρ hR t b hb hUt ϖ' hϖ' a T hT k₁ hk₁ k₂ hk₂ _
      (e.symm _).2 hg, mul_div_assoc, div_self hc1, mul_one, mul_assoc, pow_combine hq, hz]
    congr 2
    ring)
  have hinv' : ∀ g, ∀ k ∈ K.subgroupOf (UAtSub σ X (evFin F v)), I (g * k) = I g := fun g k hk => by
    have := hinv (e g) (e k) ((heK k).1 hk)
    simpa only [← map_mul, e.symm_apply_apply] using this
  have hsum' := GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient _ _ e.toMulEquiv (K.subgroupOf (UAtSub σ X (evFin F v))) (KGL v n) heK I hinv' _ hsum
  have hopen : IsOpen (K.subgroupOf (UAtSub σ X (evFin F v)) : Set (UAtSub σ X (evFin F v))) := by
    have : (K.subgroupOf (UAtSub σ X (evFin F v)) : Set (UAtSub σ X (evFin F v))) = e ⁻¹' (KGL v n : Set _) :=
      Set.ext heK
    rw [this]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (w := v) (n := n)).1.preimage e.continuous
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (UA σ X.J) := inferInstanceAs (IsTopologicalGroup (UG (cA σ) (incM F X.J)))
  haveI := hμ
  obtain ⟨-, hE⟩ := GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets _ μ _ hopen hμK I _ hinv' hsum'
  refine Eq.trans hE ?_
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [GlobalTheory.T.local_l_factor_unramified_character F E σ hcm χW d hP.resW v t hU ϖ hϖ₀]
  · simp only [denInv, etaAt, if_neg hv, one_pow, one_mul]
    rfl

end GlobalTheory.ThK.Bot.SplitVal

end

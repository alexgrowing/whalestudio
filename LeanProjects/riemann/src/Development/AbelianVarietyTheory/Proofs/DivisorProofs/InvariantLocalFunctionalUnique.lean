import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApplyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelHeisenbergOperatorsTranslationCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorIsometrySchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryLiftTendstoOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCharacterOfTrivialNearOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalSphericalValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenIntegrabilityFullRankOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableZetaIntegrand
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL

noncomputable section

namespace GlobalTheory.ExtCoinv

section LinAlg

theorem exists_ext_ker {V : Type} [AddCommGroup V] [Module ℂ V] (A N : Submodule ℂ V) (l : V →ₗ[ℂ] ℂ)
    (h : ∀ x ∈ A, x ∈ N → l x = 0) : ∃ l' : V →ₗ[ℂ] ℂ, N ≤ LinearMap.ker l' ∧ ∀ x ∈ A, l' x = l x := by
  let f : V →ₗ.[ℂ] ℂ := ⟨A, l.comp A.subtype⟩
  let g : V →ₗ.[ℂ] ℂ := ⟨N, 0⟩
  have hfg : ∀ (x : f.domain) (y : g.domain), (x : V) = y → f x = g y := by
    intro x y hxy
    exact h x x.2 (hxy ▸ y.2)
  obtain ⟨l', hl'⟩ := LinearMap.exists_extend (f.sup g hfg).toFun
  have key : ∀ z : (f.sup g hfg).domain, l' z = (f.sup g hfg) z := fun z => LinearMap.congr_fun hl' z
  refine ⟨l', fun x hx => ?_, fun x hx => ?_⟩
  · have hle := LinearPMap.right_le_sup f g hfg
    rw [LinearMap.mem_ker, key ⟨x, hle.1 hx⟩, ← hle.2 (x := ⟨x, hx⟩) rfl]
    rfl
  · have hle := LinearPMap.left_le_sup f g hfg
    rw [key ⟨x, hle.1 hx⟩, ← hle.2 (x := ⟨x, hx⟩) rfl]
    rfl

end LinAlg

section Local

open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv
open GlobalTheory.SplitWeil (nabs volM volGL KO)
open scoped Matrix

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem integrable_char_pow [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ)
    (hs : GlobalTheory.SmGL.IsSmoothChar ν) (hu : GlobalTheory.SmGL.IsUnitaryChar ν) (z : ℂ) (hz : (n : ℝ) ≤ z.re)
    (φ : Matrix (Fin n) (Fin n) k → ℂ) (hl : IsLocallyConstant φ) (hK : HasCompactSupport φ) :
    Integrable (fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (haarVol (KO k (Fin n))) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let μ : Measure k := Measure.addHaar
  have : (volGL μ (Fin n)).IsHaarMeasure := GlobalTheory.SplitWeil.isHaarMeasure_volGL _
  rw [Measure.isMulLeftInvariant_eq_smul (haarVol (KO k (Fin n))) (volGL μ (Fin n))]
  refine Integrable.smul_measure_nnreal ?_
  obtain ⟨B, hB⟩ := GlobalTheory.ZetaConvergence.exists_nabs_le (IsCompact.image hK
    (f := fun x : Matrix (Fin n) (Fin n) k => x.det) continuous_id.matrix_det)
  have : BorelSpace (Matrix (Fin n) (Fin n) k) := inferInstanceAs (BorelSpace (Fin n → Fin n → k))
  have : (volM μ (Fin n) (Fin n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hE := GlobalTheory.SplitWeil.Model.measurableEmbedding_val (k := k) (Fin n)
  have hd := GlobalTheory.SplitWeil.continuous_density_volGL (k := k) (n := Fin n)
  have hI : Integrable (fun g : GL (Fin n) k => φ g.val)
      ((volM μ (Fin n) (Fin n)).comap fun g : GL (Fin n) k => g.val) := by
    have h1 : Integrable φ (volM μ (Fin n) (Fin n)) := hl.continuous.integrable_of_hasCompactSupport hK
    refine (hE.integrable_map_iff (g := φ)).1 ?_
    rw [hE.map_comap]
    exact h1.restrict
  have hchar : IsLocallyConstant fun x : kˣ => ((ν x : ℂˣ) : ℂ) := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x0 => ?_
    have hn : (fun x => x0⁻¹ * x) ⁻¹' (ν.ker : Set kˣ) ∈ nhds x0 :=
      (IsOpen.preimage (continuous_const.mul continuous_id) hs).mem_nhds (by simp)
    filter_upwards [hn] with x hx
    have hx' : ν (x0⁻¹ * x) = 1 := hx
    rw [map_mul, map_inv, inv_mul_eq_one] at hx'
    rw [hx']
  have hcont : Continuous fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z := by
    refine ((hl.continuous.comp Units.continuous_val).mul
      (hchar.continuous.comp Matrix.GeneralLinearGroup.continuous_det)).mul ?_
    exact (((GlobalTheory.SplitWeil.isLocallyConstant_nabs k).comp fun r : ℝ => (r : ℂ) ^ z).continuous).comp
      Matrix.GeneralLinearGroup.continuous_det
  unfold volGL
  rw [integrable_withDensity_iff_integrable_smul' hd.measurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine (hI.norm.mul_const (B ^ (z.re - n))).mono'
    (hd.measurable.ennreal_toReal.aestronglyMeasurable.smul hcont.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g => ?_)
  have hp : 0 < nabs k (gdet g) := NNReal.coe_pos.mpr distribHaarChar_pos
  by_cases h0 : φ g.val = 0
  · simp [h0]
  have h1 : nabs k (gdet g) ≤ B := hB _ ⟨g.val, subset_tsupport _ h0, rfl⟩
  have h2 : nabs k (gdet g) ^ (z.re - n) ≤ B ^ (z.re - n) := Real.rpow_le_rpow hp.le h1 (sub_nonneg.2 hz)
  show ‖(ENNReal.ofReal (nabs k (gdet g) ^ (-(Fintype.card (Fin n) : ℝ)))).toReal • _‖ ≤ _
  rw [norm_smul, ENNReal.toReal_ofReal (Real.rpow_nonneg hp.le _), Real.norm_of_nonneg (Real.rpow_nonneg hp.le _),
    norm_mul, norm_mul, hu, mul_one, apow, Complex.norm_cpow_eq_rpow_re_of_pos hp, Fintype.card_fin]
  calc nabs k (gdet g) ^ (-(n : ℝ)) * (‖φ g.val‖ * nabs k (gdet g) ^ z.re)
      = ‖φ g.val‖ * nabs k (gdet g) ^ (z.re - n) := by
        rw [show z.re - n = -(n : ℝ) + z.re by ring, Real.rpow_add hp]; ring
    _ ≤ ‖φ g.val‖ * B ^ (z.re - n) := by gcongr

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem Y0_mul_transpose (n d : ℕ) (hnd : n ≤ d) : Y0 k n d * (Y0 k n d)ᵀ = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨d - n + i, by omega⟩ : Fin d)]
  · simp [FullRankCoinv.Y0, Matrix.one_apply, Fin.ext_iff]
  · intro b _ hb
    rw [FullRankCoinv.Y0, Matrix.of_apply, if_neg, zero_mul]
    intro hh; exact hb (Fin.ext hh)
  · simp

theorem integrable_fibre_all [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (hnd : 2 * n ≤ d) (ν : kˣ →* ℂˣ)
    (hs : GlobalTheory.SmGL.IsSmoothChar ν) (hu : GlobalTheory.SmGL.IsUnitaryChar ν)
    (Ψ : Matrix (Fin n) (Fin d) k → ℂ) (hΨ : Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k)) (h : GL (Fin d) k) :
    Integrable (fun g : GL (Fin n) k => Ψ (g.val * (Y0 k n d * h.val)) * (ν (gdet g) : ℂ) *
      apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) (haarVol (KO k (Fin n))) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  obtain ⟨hl, hK⟩ : IsLocallyConstant Ψ ∧ HasCompactSupport Ψ := hΨ
  refine integrable_char_pow n ν hs hu _ ?_ (fun x => Ψ (x * (Y0 k n d * h.val)))
    (hl.comp_continuous (by fun_prop)) ?_
  · have : (2 * n : ℝ) ≤ d := by exact_mod_cast hnd
    simp only [Fintype.card_fin, Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  · refine HasCompactSupport.intro (hK.image (f := fun y => y * ((h⁻¹).val * (Y0 k n d)ᵀ)) (by fun_prop))
      fun x hx => ?_
    by_contra h0
    apply hx
    refine ⟨_, subset_tsupport _ h0, ?_⟩
    show x * (Y0 k n d * h.val) * ((h⁻¹).val * (Y0 k n d)ᵀ) = x
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, Units.mul_inv, Matrix.one_mul,
      Y0_mul_transpose n d (by omega), Matrix.mul_one]

theorem lact_mem_SB {n d : ℕ} (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) {Ψ : Matrix (Fin n) (Fin d) k → ℂ}
    (hΨ : Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k)) : lact ν g Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := by
  have hmem : (fun Y => Ψ ((g.1)ᵀ * Y)) ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := by
    let e : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k :=
      { toFun := fun X => (g.1)ᵀ * X
        invFun := fun X => ((g⁻¹).1)ᵀ * X
        left_inv := fun X => by
          simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
            Matrix.one_mul]
        right_inv := fun X => by
          simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
            Matrix.one_mul]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact ⟨hΨ.1.comp_continuous e.continuous, hΨ.2.comp_homeomorph e⟩
  exact Submodule.smul_mem _ ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) hmem

theorem mem_augRk_of_mem_span (n d : ℕ) (hnd : 2 * n ≤ d) (ν : kˣ →* ℂˣ)
    (hs : GlobalTheory.SmGL.IsSmoothChar ν) (hu : GlobalTheory.SmGL.IsUnitaryChar ν) (Ψ : Matrix (Fin n) (Fin d) k → ℂ)
    (hΨ : Ψ ∈ fullRk k n d)
    (hN : Ψ ∈ Submodule.span ℂ {z | ∃ g : GL (Fin n) k, ∃ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k), z = lact ν g Φ - Φ}) :
    Ψ ∈ augRk n d ν := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  refine GlobalTheory.T.full_rank_zeta_kernel k n d ν (by omega) hs Ψ hΨ fun h => ?_
  have hint := fun Φ hΦ => integrable_fibre_all n d hnd ν hs hu Φ hΦ h
  have hadd : ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k), ∀ Φ' ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k), ∀ c : ℂ,
      smallF (haarVol (KO k (Fin n))) ν (c • Φ + Φ') (Y0 k n d * h.val) =
        c * smallF (haarVol (KO k (Fin n))) ν Φ (Y0 k n d * h.val) +
          smallF (haarVol (KO k (Fin n))) ν Φ' (Y0 k n d * h.val) := by
    intro Φ hΦ Φ' hΦ' c
    simp only [smallF, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul, ← integral_add ((hint Φ hΦ).const_mul c) (hint Φ' hΦ')]
    congr 1; funext g; ring
  have hzero : smallF (haarVol (KO k (Fin n))) ν (0 : Matrix (Fin n) (Fin d) k → ℂ) (Y0 k n d * h.val) = 0 := by
    simp [smallF]
  suffices H : Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) ∧
      smallF (haarVol (KO k (Fin n))) ν Ψ (Y0 k n d * h.val) = 0 from H.2
  clear hΨ
  induction hN using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, Φ, hΦ, rfl⟩ := hx
    refine ⟨sub_mem (lact_mem_SB ν g hΦ) hΦ, ?_⟩
    rw [show lact ν g Φ - Φ = (-1 : ℂ) • Φ + lact ν g Φ by rw [neg_one_smul]; abel,
      hadd _ hΦ _ (lact_mem_SB ν g hΦ), UnitMinor.smallF_lact]
    ring
  | zero => exact ⟨zero_mem _, hzero⟩
  | add x y _ _ hx hy =>
    refine ⟨add_mem hx.1 hy.1, ?_⟩
    rw [← one_smul ℂ x, hadd _ hx.1 _ hy.1, hx.2, hy.2]; ring
  | smul c x _ hx =>
    refine ⟨Submodule.smul_mem _ c hx.1, ?_⟩
    rw [← add_zero (c • x), hadd _ hx.1 _ (zero_mem _), hx.2, hzero]; ring

end Local

section Global

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology
open scoped GlobalTheory.VacAny

theorem model_at : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∃ ν₀ : (Fv F v)ˣ →* ℂˣ, GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), φ ∈ G.M'.SoLoc B.ψ t ↔
        ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F v), Y.rank ≠ a' → ι φ Y = 0) ∧
      (∀ g₀ : GL (Fin a') (Fv F v), ∃ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.FullRankCoinv.lact ν₀ g₀ (ι φ)) ∧
      ∀ g ∈ UAt σ G.V' (evFin F v), ∃ g₀ : GL (Fin a') (Fv F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁,
        Acts (evFin F v) (om' (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.FullRankCoinv.lact ν₀ g₀ (ι φ) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv t ι hι
  have hcm : IsCMExt F E σ := hT.base.cm
  let B' : Base F E := { B with v₁ := v, τ₁ := t }
  have hT' : IsTriple B' G X om om' :=
    { base := { hT.base with }
      geo := { hT.geo with hV := { hT.geo.hV with }, hV' := { hT.geo.hV' with }, hW := { hT.geo.hW with } }
      chars := { hT.chars with good := hv }
      weil := hT.weil
      weil' := hT.weil' }
  have hι' : G.M'.IsLinBar B'.ψ B'.τ₁ 1 1 ι := hι

  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdet : IsUnit (G.V'.J.map t).det :=
    GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V'.J t (B.emb w).1 1 one_ne_zero (G.V'.θ w)
      (by rw [one_smul]; exact hT.geo.hV'.cartan w)
  have herm : ∀ i j, σ (G.V'.J j i) = algebraMap F E 1 * G.V'.J i j := fun i j => by
    rw [map_one, one_mul]; exact hT.geo.hV'.herm i j
  let K := GlobalTheory.SplitUnitLift.liftU hcm t G.V'.J 1 herm hdet
  have hK : ∀ g, K g ∈ UAt σ G.V' (evFin F B'.v₁) ∧ (mat (K g)).map (piW B'.τ₁) = g.val ∧
      (mat (K g)).map (piW (B'.τ₁.comp σ)) = (G.V'.J.map B'.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map B'.τ₁ :=
    fun g => ⟨GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.V' 1 herm hdet g, GlobalTheory.SplitUnitLift.liftU_piW hcm t G.V'.J 1 herm hdet g,
      GlobalTheory.SplitUnitLift.liftU_piW_comp hcm t G.V'.J 1 herm hdet g⟩

  choose S hS using fun g => GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hT v (K g) (hK g).1
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a' × Fin (a + a')) v
  have eqR : ∀ φ₁ φ₂ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R → φ₁ = φ₂ := by
    intro φ₁ φ₂ h
    have hRc := (hR 0 (Submodule.zero_mem _)).1
    funext y
    have hp : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
    have e := congrFun h (fun i => GlobalTheory.LatVac.liftV v (y i))
    have e2 : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by simpa using hRc 0 _ hp
    simp only [tens, GlobalTheory.LatVac.evFin_liftV, e2] at e
    exact mul_right_cancel₀ hR0 e
  have hSR : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), om' (K g, 1) (tens (evFin F v) φ R) = tens (evFin F v) (S g φ) R :=
    fun g φ hφ => (hS g φ hφ).2 R (hR φ hφ)
  have h1 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S g φ ∈ SB _ := fun g φ hφ => (hS g φ hφ).1
  have tensLin : ∀ (c : ℂ) (φ φ' : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • φ + φ') R = c • tens (evFin F v) φ R + tens (evFin F v) φ' R := by
    intro c φ φ'; funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hlin : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ c : ℂ,
      S g (c • φ + φ') = c • S g φ + S g φ' := by
    intro g φ hφ φ' hφ' c
    have hm : c • φ + φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v) := Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'
    apply eqR
    rw [← hSR g _ hm, tensLin, map_add, map_smul, hSR g φ hφ, hSR g φ' hφ', tensLin]
  have h2 : ∀ g g', ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S (g * g') φ = S g (S g' φ) := by
    intro g g' φ hφ
    apply eqR
    have e1 : ((K (g * g'), (1 : UA σ G.W.J))) = (K g, 1) * (K g', 1) := by rw [map_mul, Prod.mk_mul_mk, one_mul]
    rw [← hSR _ φ hφ, e1, map_mul, Module.End.mul_apply, hSR g' φ hφ, hSR g _ (h1 g' φ hφ)]
  have h3 : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S 1 φ = φ := by
    intro φ hφ
    apply eqR
    have e1 : ((K 1, (1 : UA σ G.W.J))) = 1 := by rw [map_one]; rfl
    rw [← hSR _ φ hφ, e1, map_one, Module.End.one_apply]
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'
  have atAct : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F v) γ →
      At (evFin F v) (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ) := by
    intro g γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have restS : ∀ g φ r, φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) → Rest (evFin F v) φ r → Rest (evFin F v) (S g φ) r :=
    fun g φ r hφ hr => ⟨hr.1, by rw [← (hS g φ hφ).2 r hr]; exact hSplit.pres _ _ hr.2⟩
  have h4 : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F v) γ → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v)
            (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ)) (S g φ) := by
    intro g γ hγ φ hφ
    have hw := GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v (GlobalTheory.LatVac.locCo G.M'.co v γ) φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v γ hγ φ r hr
    have hRw : Rest (evFin F v) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M' B.ψ hT.base.std γ _ hr.2⟩
    rw [← (hS g _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS g φ hφ).2 r hr,
      GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v _ (atAct g γ hγ) (S g φ) r (restS g φ r hφ hr)]
  have h5 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → Fv F v) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ :=
    fun g φ hφ μ hμ => GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat B G X om om' hT v (K g) (hK g).1 φ (S g φ) hφ (h1 g φ hφ) (hS g φ hφ).2 μ hμ
  obtain ⟨ν, α, hν, hC⟩ := GlobalTheory.T.heisenbergIntertwiner_eq_twisted_weilOperator B' G X om om' hT' K hK S h1 hlin h2 h3 h4 h5
  obtain ⟨hψc, hψ1, wT, wM, hA⟩ := GlobalTheory.T.linearModel_heisenbergOperators_translation_char B' G X om om' hT' K hK S h1 h4
  obtain ⟨hTι, hMι, -, -⟩ := hA ι hι'

  have hvac := hT.geo.hM'.vac v
  have hιv : ι (G.M'.vac v) ≠ 0 := fun h0 =>
    hvac.2.1 (hι.bij.injOn hvac.1 (Submodule.zero_mem _) (by rw [h0, map_zero]))
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.mp hιv
  set φ₀ := GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) (wT Y₀) (G.M'.vac v) with hφ₀def
  have hφ₀ : φ₀ ∈ SB (Fin a' × Fin (a + a') → Fv F v) := GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v _ _ hvac.1
  have hφ₀0 : ι φ₀ 0 ≠ 0 := by
    have e := congrFun (hTι Y₀ _ hvac.1) 0
    simp only [zero_add] at e
    rw [e]; exact hY₀

  obtain ⟨-, -, hcont⟩ := GlobalTheory.T.theta_action_exists hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' G.q (a' - G.q)
    (a + a' - (G.p + G.q)) (G.p + G.q) (GlobalTheory.ThK.Inhab.pairV' hT) v
  obtain ⟨U, hU, hUact⟩ := hcont φ₀ hφ₀
  have hKt : Tendsto K (𝓝 1) (𝓝 1) := GlobalTheory.T.split_unitary_lift_tendsto_one hcm t G.V'.J 1 herm hdet
  have hP1 : {g : GL (Fin a') (Fv F v) | (K g, (1 : UA σ G.W.J)) ∈ U} ∈ 𝓝 1 :=
    (hKt.prodMk_nhds tendsto_const_nhds) hU
  have hone : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := fun u _ => by simp [mat]
  have hsm : ∀ g ∈ {g : GL (Fin a') (Fv F v) | (K g, (1 : UA σ G.W.J)) ∈ U},
      (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2) = 1 := by
    intro g hg
    have hact := hUact (K g, 1) hg (hK g).1 hone
    have hfix : S g φ₀ = φ₀ := eqR _ _ (by rw [← hSR g φ₀ hφ₀]; exact hact R (hR φ₀ hφ₀))
    have e := congrFun (hC ι hι' g φ₀ hφ₀) 0
    rw [hfix] at e
    simp only [GlobalTheory.SplitFlip.omB, map_one, Units.val_one, mul_one, GlobalTheory.SplitFlip.apow_one, Matrix.mul_zero,
      Matrix.zero_mul] at e
    have e2 : ι φ₀ 0 * 1 = ι φ₀ 0 * ((ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2)) := by
      rw [mul_one]; nth_rw 1 [e]; ring
    exact (mul_left_cancel₀ hφ₀0 e2).symm
  have hsmooth : GlobalTheory.SmGL.IsSmoothChar ν := GlobalTheory.T.smooth_character_of_trivial_near_one (by have := (GlobalTheory.ThK.Inhab.two_le_rank hT).1; omega) ν _ _ hP1 hsm

  have hSo : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), φ ∈ G.M'.SoLoc B.ψ t ↔
      ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F v), Y.rank ≠ a' → ι φ Y = 0 := by
    intro φ hφ
    constructor
    · rintro ⟨-, ι₂, hι₂, hvan⟩ Y hY
      have hι₂' : G.M'.IsLinBar B'.ψ B'.τ₁ 1 1 ι₂ := hι₂
      obtain ⟨hT₂, hM₂, -, -⟩ := hA ι₂ hι₂'
      obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin a' × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) hψc hψ1 ι₂ ι
        hι₂.bij (fun x _ y _ c => by rw [map_add, map_smul])
        (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) (wT C))
        (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) (wM l))
        (fun C x hx => ⟨GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v _ x hx, hT₂ C x hx, hTι C x hx⟩)
        (fun l x hx => ⟨GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v _ x hx, hM₂ l x hx, hMι l x hx⟩)
      rw [hc φ hφ, Pi.smul_apply, hvan Y hY, smul_zero]
    · intro h
      exact ⟨hφ, ι, hι, h⟩
  have hL : ∀ g₀, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ι (S g₀ φ) = GlobalTheory.FullRankCoinv.lact ν g₀ (ι φ) := by
    intro g₀ φ hφ
    rw [hC ι hι' g₀ φ hφ]
    funext Y
    simp only [GlobalTheory.SplitFlip.omB, GlobalTheory.FullRankCoinv.lact, map_one, Units.val_one, mul_one, GlobalTheory.SplitFlip.apow_one,
      Matrix.mul_one, Fintype.card_fin]
  refine ⟨ν, hsmooth, hν, hSo, fun g₀ => ⟨K g₀, (hK g₀).1, fun φ hφ =>
    ⟨S g₀ φ, h1 g₀ φ hφ, (hS g₀ φ hφ).2, hL g₀ φ hφ⟩⟩, fun g hg => ?_⟩
  obtain ⟨g₀, rfl⟩ : ∃ g₀, g = K g₀ := ⟨_, GlobalTheory.SchurCharV.eq_liftU_of_UAt hcm t G.V' herm hdet g hg⟩
  refine ⟨g₀, fun φ hφ φ₁ hA₁ => ?_⟩
  rw [← hL g₀ φ hφ, eqR φ₁ (S g₀ φ) (by rw [← hSR g₀ φ hφ]; exact (hA₁ R (hR φ hφ)).symm)]

theorem exists_ext : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → ∀ t : E →ₐ[F] Fv F v, ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, (∀ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ G.M'.SoLoc B.ψ t, ∀ φ₁ ∈ G.M'.SoLoc B.ψ t, Acts (evFin F v) (om' (g, 1)) φ φ₁ → l φ₁ = l φ) → ∃ l' : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, augAt om' v ≤ LinearMap.ker l' ∧ ∀ φ ∈ G.M'.SoLoc B.ψ t, l' φ = l φ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv t l hl
  by_cases hex : ∃ ι, G.M'.IsLinBar B.ψ t 1 1 ι
  swap
  · exact ⟨0, by simp, fun φ hφ => absurd ⟨_, hφ.2.choose_spec.1⟩ hex⟩
  obtain ⟨ι, hι⟩ := hex
  obtain ⟨ν, hs, hu, hSo, hex, hall⟩ := model_at hP F E σ B a a' G X om om' hT v hv t ι hι
  let A : Submodule ℂ ((Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
    SB _ ⊓ (GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a')).comap ι
  have hA : ∀ φ, φ ∈ A ↔ φ ∈ G.M'.SoLoc B.ψ t := fun φ =>
    ⟨fun h => (hSo φ h.1).2 h.2.2, fun h => ⟨h.1, hι.bij.mapsTo h.1, (hSo φ h.1).1 h⟩⟩
  have hN : augAt om' v ≤ (Submodule.span ℂ {z | ∃ g : GL (Fin a') (Fv F v),
      ∃ Φ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)), z = GlobalTheory.FullRankCoinv.lact ν g Φ - Φ}).comap ι := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, φ, hφ, φ₁, -, hact, rfl⟩
    obtain ⟨g₀, hg₀⟩ := hall g hg
    exact Submodule.subset_span ⟨g₀, ι φ, hι.bij.mapsTo hφ, by rw [map_sub, hg₀ φ hφ φ₁ hact]⟩
  have hR : GlobalTheory.FullRankCoinv.augRk a' (a + a') ν ≤ (SB _ ⊓ LinearMap.ker l).map ι := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g₀, Ψ, hΨ, rfl⟩
    obtain ⟨φ, hφ, rfl⟩ := hι.bij.surjOn hΨ.1
    obtain ⟨g, hg, hact⟩ := hex g₀
    obtain ⟨φ₁, hφ₁, hA₁, hE⟩ := hact φ hφ
    have h0 : φ ∈ G.M'.SoLoc B.ψ t := (hA φ).1 ⟨hφ, hΨ⟩
    have h1 : φ₁ ∈ G.M'.SoLoc B.ψ t := (hA φ₁).1 ⟨hφ₁, by
      show ι φ₁ ∈ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a')
      rw [hE]; exact GlobalTheory.FullRankCoinv.Reduce.lact_mem ν g₀ hΨ⟩
    refine ⟨φ₁ - φ, ⟨sub_mem hφ₁ hφ, ?_⟩, by rw [map_sub, hE]⟩
    show l (φ₁ - φ) = 0
    rw [map_sub, hl g hg φ h0 φ₁ h1 hA₁, sub_self]
  obtain ⟨l', h1, h2⟩ := exists_ext_ker A (augAt om' v) l fun φ hφA hφN => by
    obtain ⟨φ', ⟨hφ', hl'⟩, he⟩ := hR (mem_augRk_of_mem_span a' (a + a') (by have := hT.geo.lt; omega) ν hs hu (ι φ)
      hφA.2 (hN hφN))
    rw [← hι.bij.injOn hφ' hφA.1 he]
    exact hl'
  exact ⟨l', h1, fun φ hφ => h2 φ ((hA φ).2 hφ)⟩

end Global

end GlobalTheory.ExtCoinv

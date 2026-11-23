import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuousStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.IdemProj

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [SigmaFinite μ]

theorem integral_inv_of_support (K : Subgroup G) (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G))
    (f : G → ℂ) (hf : Continuous f) (hs : ∀ x, f x ≠ 0 → x ∈ K) :
    ∫ x, f x⁻¹ ∂μ = ∫ x, f x ∂μ := by
  have hKcl : IsClosed (K : Set G) := K.isClosed_of_isOpen ho
  have hu : Continuous ((K : Set G).indicator fun _ => (1 : ℂ)) :=
    (IsClopen.continuous_indicator ⟨hKcl, ho⟩ continuous_const)
  set u : G → ℂ := (K : Set G).indicator fun _ => (1 : ℂ) with hu_def

  set Φ : G × G → ℂ := fun z => f z.2⁻¹ * u (z.1 * z.2) with hΦ_def
  have hΦc : Continuous Φ := (hf.comp continuous_snd.inv).mul (hu.comp continuous_mul)
  have hΦs : HasCompactSupport Φ := by
    refine HasCompactSupport.intro (hc.prod hc) fun z hz => ?_
    by_cases h2 : f z.2⁻¹ = 0
    · simp [hΦ_def, h2]
    · have hb : z.2 ∈ K := by simpa using K.inv_mem (hs _ h2)
      have ha : z.1 ∉ K := fun ha => hz ⟨ha, hb⟩
      have : z.1 * z.2 ∉ K := fun h => ha ((K.mul_mem_cancel_right hb).1 h)
      simp [hΦ_def, hu_def, this]
  have hΦi : Integrable Φ (μ.prod μ) := hΦc.integrable_of_hasCompactSupport hΦs
  have hT := measurePreserving_prod_inv_mul_swap μ μ
  have hΦTi : Integrable (fun z : G × G => Φ (z.2, z.2⁻¹ * z.1)) (μ.prod μ) :=
    (hT.integrable_comp hΦc.aestronglyMeasurable).2 hΦi
  have hswap : ∫ z, Φ (z.2, z.2⁻¹ * z.1) ∂(μ.prod μ) = ∫ z, Φ z ∂(μ.prod μ) := by
    conv_rhs => rw [← hT.map_eq]
    rw [integral_map hT.measurable.aemeasurable]
    rw [hT.map_eq]; exact hΦc.aestronglyMeasurable
  set c : ℂ := ∫ a, u a ∂μ with hc_def
  have hcne : c ≠ 0 := by
    rw [hc_def, hu_def, integral_indicator_const _ hKcl.measurableSet]
    have hpos : 0 < μ (K : Set G) := ho.measure_pos μ ⟨1, K.one_mem⟩
    have hfin : μ (K : Set G) ≠ ⊤ := hc.measure_lt_top.ne
    have : μ.real (K : Set G) ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hpos.ne', hfin⟩
    simpa [Complex.real_smul] using this
  have hleft : ∫ z, Φ z ∂(μ.prod μ) = (∫ b, f b⁻¹ ∂μ) * c := by
    rw [integral_prod_symm Φ hΦi, ← integral_mul_const]
    congr 1; funext b
    simp only [hΦ_def]
    rw [integral_const_mul]
    by_cases h2 : f b⁻¹ = 0
    · simp [h2]
    · have hb : b ∈ K := by simpa using K.inv_mem (hs _ h2)
      congr 1
      rw [hc_def]
      congr 1; funext a
      classical
      simp only [hu_def, Set.indicator_apply, SetLike.mem_coe, K.mul_mem_cancel_right hb]
  have hright : ∫ z, Φ (z.2, z.2⁻¹ * z.1) ∂(μ.prod μ) = (∫ x, f x ∂μ) * c := by
    rw [integral_prod _ hΦTi]
    simp only [hΦ_def, _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    rw [hc_def, ← integral_const_mul]
    congr 1; funext x
    rw [integral_mul_const, integral_mul_left_eq_self (fun y => f y) x⁻¹]
  have := hswap
  rw [hleft, hright] at this
  exact (mul_right_cancel₀ hcne this).symm

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] in

theorem inner_rep (π : G → (H →L[ℂ] H)) (h1 : π 1 = 1) (hm : ∀ a b, π (a * b) = π a * π b)
    (hn : ∀ g v, ‖π g v‖ = ‖v‖) (g : G) (x y : H) : ⟪x, π g y⟫_ℂ = ⟪π g⁻¹ x, y⟫_ℂ := by
  have hback : π g (π g⁻¹ x) = x := by
    have := congrArg (fun S : H →L[ℂ] H => S x) (hm g g⁻¹)
    simp only [mul_inv_cancel, h1, ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply] at this
    exact this.symm
  let U : H →ₗᵢ[ℂ] H := ⟨(π g).toLinearMap, hn g⟩
  calc ⟪x, π g y⟫_ℂ = ⟪U (π g⁻¹ x), U y⟫_ℂ := by
        show ⟪x, π g y⟫_ℂ = ⟪π g (π g⁻¹ x), π g y⟫_ℂ
        rw [hback]
    _ = ⟪π g⁻¹ x, y⟫_ℂ := U.inner_map_map _ _

theorem op_idem (K : Subgroup G) (hc : IsCompact (K : Set G))
    (π : G → (H →L[ℂ] H)) (h1 : π 1 = 1) (hm : ∀ a b, π (a * b) = π a * π b)
    (hn : ∀ g v, ‖π g v‖ = ‖v‖) (hπ : ∀ v, Continuous fun g => π g v)
    (e : G → ℂ) (he : Continuous e) (hs : ∀ x, e x ≠ 0 → x ∈ K)
    (hee : ∀ x, ∫ y, e y * e (y⁻¹ * x) ∂μ = e x) (T : H →L[ℂ] H)
    (hT : ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, e g * ⟪x, π g y⟫_ℂ ∂μ) : T.comp T = T := by
  ext y
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, hT x (T y)]
  have step : ∀ g, ⟪x, π g (T y)⟫_ℂ = ∫ h, e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ ∂μ := by
    intro g
    have shift := integral_mul_left_eq_self (μ := μ) (fun h => e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ) g
    simp only [inv_mul_cancel_left] at shift
    rw [inner_rep π h1 hm hn g, hT, ← shift]
    congr 1; funext h
    rw [hm, ContinuousLinearMap.mul_apply, inner_rep π h1 hm hn g]
  have hint : Integrable (Function.uncurry fun g h => e g * (e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ))
      (μ.prod μ) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (he.comp continuous_fst).mul ((he.comp (continuous_fst.inv.mul continuous_snd)).mul
        (continuous_const.inner ((hπ y).comp continuous_snd)))
    · refine HasCompactSupport.intro (hc.prod hc) ?_
      rintro ⟨g, h⟩ hgh
      simp only [Function.uncurry_apply_pair]
      by_cases hg : g ∈ K
      · have hh : h ∉ K := fun hh => hgh ⟨hg, hh⟩
        have h0 : e (g⁻¹ * h) = 0 := by
          by_contra hne
          exact hh (by simpa using K.mul_mem hg (hs _ hne))
        simp [h0]
      · have h0 : e g = 0 := by
          by_contra hne
          exact hg (hs _ hne)
        simp [h0]
  calc ∫ g, e g * ⟪x, π g (T y)⟫_ℂ ∂μ
      = ∫ g, ∫ h, e g * (e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ) ∂μ ∂μ := by
        congr 1; funext g
        rw [step g, integral_const_mul]
    _ = ∫ h, ∫ g, e g * (e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ h, e h * ⟪x, π h y⟫_ℂ ∂μ := by
        congr 1; funext h
        simp_rw [← mul_assoc]
        rw [integral_mul_const, hee]
    _ = ⟪x, T y⟫_ℂ := (hT x y).symm

theorem op_symm (K : Subgroup G) (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G))
    (π : G → (H →L[ℂ] H)) (h1 : π 1 = 1) (hm : ∀ a b, π (a * b) = π a * π b)
    (hn : ∀ g v, ‖π g v‖ = ‖v‖) (hπ : ∀ v, Continuous fun g => π g v)
    (e : G → ℂ) (he : Continuous e) (hs : ∀ x, e x ≠ 0 → x ∈ K)
    (hst : ∀ x, e x⁻¹ = star (e x)) (T : H →L[ℂ] H)
    (hT : ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, e g * ⟪x, π g y⟫_ℂ ∂μ) (x y : H) :
    ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
  have hF : Continuous fun g => e g * ⟪x, π g y⟫_ℂ := he.mul (continuous_const.inner (hπ y))
  have hFs : ∀ g, e g * ⟪x, π g y⟫_ℂ ≠ 0 → g ∈ K := fun g hg => hs g (left_ne_zero_of_mul hg)
  conv_lhs => rw [← inner_conj_symm]
  rw [hT y x, ← integral_conj, hT x y, ← integral_inv_of_support μ K hc ho _ hF hFs]
  congr 1; funext g
  show (starRingEnd ℂ) (e g * ⟪y, π g x⟫_ℂ) = e g⁻¹ * ⟪x, π g⁻¹ y⟫_ℂ
  rw [map_mul, inner_conj_symm, starRingEnd_apply, ← hst g, inner_rep π h1 hm hn g⁻¹, inv_inv]

omit [T2Space G] in

theorem op_fixed (π : G → (H →L[ℂ] H)) (h1 : π 1 = 1) (hm : ∀ a b, π (a * b) = π a * π b)
    (hn : ∀ g v, ‖π g v‖ = ‖v‖) (e : G → ℂ) (T : H →L[ℂ] H)
    (hT : ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, e g * ⟪x, π g y⟫_ℂ ∂μ) (k : G) (hk : ∀ h, e (k * h) = e h) :
    (π k).comp T = T := by
  ext y
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, inner_rep π h1 hm hn k, hT, hT]
  have key : ∀ g, e g * ⟪π k⁻¹ x, π g y⟫_ℂ = e (k * g) * ⟪x, π (k * g) y⟫_ℂ := by
    intro g
    rw [hk g, hm, ContinuousLinearMap.mul_apply, inner_rep π h1 hm hn k]
  simp_rw [key]
  exact integral_mul_left_eq_self (fun h => e h * ⟪x, π h y⟫_ℂ) k

omit [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in

theorem eventually_left_inv (K : Subgroup G) (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G))
    (e : G → ℂ) (he : IsLocallyConstant e) (hs : ∀ x, e x ≠ 0 → x ∈ K) :
    ∀ᶠ k in nhds (1 : G), ∀ h, e (k * h) = e h := by
  have hloc : ∀ h ∈ (K : Set G), ∀ᶠ z : G × G in nhds ((1 : G), h), e (z.1 * z.2) = e z.2 := by
    intro h _
    have hfib : ∀ᶠ y in nhds h, e y = e h := he.eventually_eq h
    have ht : Filter.Tendsto (fun z : G × G => z.1 * z.2) (nhds ((1 : G), h)) (nhds h) := by
      simpa using (continuous_mul (M := G)).tendsto ((1 : G), h)
    have ha := ht.eventually hfib
    have hb : ∀ᶠ z : G × G in nhds ((1 : G), h), e z.2 = e h :=
      (continuous_snd.tendsto ((1 : G), h)).eventually hfib
    filter_upwards [ha, hb] with z hz1 hz2
    rw [hz1, hz2]
  have hK : ∀ᶠ k in nhds (1 : G), ∀ h ∈ (K : Set G), e (k * h) = e h :=
    hc.eventually_forall_of_forall_eventually hloc
  have hmem : ∀ᶠ k in nhds (1 : G), k ∈ (K : Set G) := ho.mem_nhds K.one_mem
  filter_upwards [hK, hmem] with k hk hkK h
  by_cases hh : h ∈ (K : Set G)
  · exact hk h hh
  · have e1 : e h = 0 := by
      by_contra hne
      exact hh (hs h hne)
    have e2 : e (k * h) = 0 := by
      by_contra hne
      exact hh (by simpa using K.mul_mem (K.inv_mem hkK) (hs _ hne))
    rw [e1, e2]

end General

theorem re_orth_proj : ∀ B : RowsAut, IsOrthProjOnto B.Re (LinearMap.range (B.Re : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) ∧ (∀ g : B.I.Ginf, B.Re.comp (B.R (g, 1)) = (B.R (g, 1)).comp B.Re) ∧ ∃ g : ℕ, 1 ≤ g ∧ ∀ k ∈ B.I.Kg g, (B.R (1, k)).comp B.Re = B.Re := by
  intro B
  obtain ⟨hT2, -, hSC, hKc, hKo, ⟨K, hK⟩, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨hR1, hRm, hRn, hRc, -⟩ := GlobalTheory.T.rightRegularRep_unitary_stronglyContinuous B
  obtain ⟨hlc, hconv, hst, -, hsupp, -, -⟩ := B.e_adm
  obtain ⟨-, hRe⟩ := B.Re_spec
  have hKc' : IsCompact (K : Set B.I.Gf) := by rw [hK]; exact hKc
  have hKo' : IsOpen (K : Set B.I.Gf) := by rw [hK]; exact hKo
  have hs : ∀ x, B.e x ≠ 0 → x ∈ K := by
    intro x hx
    rw [← SetLike.mem_coe, hK]
    exact hsupp x hx
  have h1 : B.R (1, 1) = 1 := hR1
  have hm : ∀ a b : B.I.Gf, B.R (1, a * b) = B.R (1, a) * B.R (1, b) := by
    intro a b
    rw [← hRm, Prod.mk_mul_mk, one_mul]
  have hn : ∀ (g : B.I.Gf) v, ‖B.R (1, g) v‖ = ‖v‖ := fun g v => hRn _ v
  have hπ : ∀ v, Continuous fun g : B.I.Gf => B.R (1, g) v :=
    fun v => (hRc v).comp (continuous_const.prodMk continuous_id)
  have he : Continuous B.e := hlc.continuous
  have hee : ∀ x, ∫ y, B.e y * B.e (y⁻¹ * x) ∂B.μf = B.e x := fun x => congrFun hconv x
  have hT : ∀ x y : B.I.L2 B.μf B.fund,
      ⟪x, B.Re y⟫_ℂ = ∫ g, B.e g * ⟪x, B.R (1, g) y⟫_ℂ ∂B.μf := hRe
  refine ⟨?_, ?_, ?_⟩
  · show B.Re.comp B.Re = B.Re ∧ (∀ x y, ⟪B.Re x, y⟫_ℂ = ⟪x, B.Re y⟫_ℂ) ∧ _
    exact ⟨op_idem B.μf K hKc' (fun g => B.R (1, g)) h1 hm hn hπ B.e he hs hee B.Re hT,
      fun x y => op_symm B.μf K hKc' hKo' (fun g => B.R (1, g)) h1 hm hn hπ B.e he hs hst B.Re hT x y,
      rfl⟩
  · intro g
    refine ContinuousLinearMap.ext fun y => ?_
    refine ext_inner_left ℂ fun x => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hT x,
      inner_rep B.R hR1 hRm hRn (g, 1) x, hT]
    congr 1; funext k
    have hcomm : ((1 : B.I.Ginf), k) * (g, 1) = (g, 1) * ((1 : B.I.Ginf), k) := by
      simp only [Prod.mk_mul_mk, one_mul, mul_one]
    rw [← inner_rep B.R hR1 hRm hRn (g, 1), ← ContinuousLinearMap.mul_apply,
      ← ContinuousLinearMap.mul_apply, ← hRm, ← hRm, hcomm]
  · obtain ⟨g, hg1, hgsub⟩ := B.I.topf_basis _ (eventually_left_inv K hKc' hKo' B.e hlc hs)
    exact ⟨g, hg1, fun k hk => op_fixed B.μf (fun g => B.R (1, g)) h1 hm hn B.e B.Re hT k
      (hgsub hk)⟩

end GlobalTheory.IdemProj

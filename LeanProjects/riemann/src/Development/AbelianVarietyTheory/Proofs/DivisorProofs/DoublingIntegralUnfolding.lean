import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIOneSubEInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftSchwartzCompactInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftHaarIntegralConvergentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftHaarIntegralFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingHeightFunctionInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingHeightFunctionContinuousStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.ThK.ConeEuler

noncomputable section

namespace GlobalTheory.ThK.Bot.Euler

theorem euler_of_majorant {X V Ya : Type} {Yf : V → Type} [Group X] [Group Ya] [∀ v, Group (Yf v)]
    [TopologicalSpace X] [TopologicalSpace Ya] [∀ v, TopologicalSpace (Yf v)] [Countable V]
    [MeasurableSpace X] [MeasurableSpace Ya] [∀ v, MeasurableSpace (Yf v)]
    [BorelSpace X] [BorelSpace Ya] [∀ v, BorelSpace (Yf v)] [IsTopologicalGroup X] [IsTopologicalGroup Ya]
    [∀ v, IsTopologicalGroup (Yf v)] [LocallyCompactSpace X] [LocallyCompactSpace Ya] [∀ v, LocallyCompactSpace (Yf v)]
    [SecondCountableTopology X] [SecondCountableTopology Ya] [∀ v, SecondCountableTopology (Yf v)] [T2Space Ya]
    {pa : X →* Ya} {pf : ∀ v, X →* Yf v} {K : ∀ v, Subgroup (Yf v)}
    (h : GlobalTheory.RestrMeas.IsRestrGroup (W := Unit) (fun _ => pa) pf K) (μ : Measure X) [μ.IsHaarMeasure]
    (μa : Measure Ya) [μa.IsHaarMeasure] (μf : ∀ v, Measure (Yf v)) [∀ v, (μf v).IsHaarMeasure]
    (h1 : ∀ v, μf v (K v) = 1) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ (S₀ : Finset V) (G : X → ℂ) (ga : Ya → ℂ) (gf : ∀ v, Yf v → ℂ) (A : X → ℝ≥0∞) (a : Ya → ℝ≥0∞)
      (b : ∀ v, Yf v → ℝ≥0∞), Measurable ga → (∀ v, Measurable (gf v)) → Measurable a → (∀ v, Measurable (b v)) →
      (∀ y, ‖ga y‖ₑ ≤ a y) → (∀ v y, ‖gf v y‖ₑ ≤ b v y) → (∀ y, a y ≠ 0) → (∀ v, ∀ y ∈ K v, b v y = 1) →
      (∀ v ∉ S₀, ∀ y ∈ K v, gf v y = 1) →
      (∀ (T : Finset V) x, S₀ ⊆ T → (∀ v ∉ T, pf v x ∈ K v) → G x = ga (pa x) * ∏ v ∈ T, gf v (pf v x)) →
      (∀ (T : Finset V) x, (∀ v ∉ T, pf v x ∈ K v) → A x = a (pa x) * ∏ v ∈ T, b v (pf v x)) →
      ∫⁻ x, A x ∂μ ≠ ⊤ →
      ∃ P : ℂ, HasProd (fun v => ∫ y, gf v y ∂μf v) P ∧ ∫ x, G x ∂μ = c * (∫ y, ga y ∂μa) * P := by
  classical
  obtain ⟨ν, ⟨-, -, hν, hc⟩, -⟩ := h.existsUnique_isHaarProd (fun _ => μa) μf (Eventually.of_forall h1)
  have hμ := Measure.isMulLeftInvariant_eq_smul μ ν
  have hc0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν).ne'
  refine ⟨_, hc0, fun S₀ G ga gf A a b mga mgf ma mb hga hgf ha0 hb1 hg1 hG hA hfin => ?_⟩
  generalize Measure.haarScalarFactor μ ν = c at hμ hc0 ⊢
  subst hμ
  have hfin' : ∫⁻ x, A x ∂ν ≠ ⊤ := fun e => hfin (by
    rw [lintegral_smul_measure, e, ENNReal.smul_def, smul_eq_mul, ENNReal.mul_top (by simpa using hc0)])
  have ha : ∀ _ : Unit, Measurable pa := fun w => (h.continuous_pa w).measurable
  have hf : ∀ v, Measurable (pf v) := fun v => (h.continuous_pf v).measurable
  have hK : ∀ v, MeasurableSet (K v : Set (Yf v)) := fun v => (h.isOpen_K v).measurableSet
  have hA' : ∀ x, A x = (∏ _w : Unit, a (pa x)) * ∏ᶠ v, b v (pf v x) := fun x => by
    obtain ⟨T, hT⟩ := GlobalTheory.RestrMeas.exists_finset_of_eventually (h.eventually_mem x)
    rw [hA T x hT, GlobalTheory.RestrMeas.finprod_eq_prod_of_mem (K := fun v => (K v : Set (Yf v))) (pf := fun v => pf v)
      (S := T) (fun v _ => hb1 v) hT, Finset.univ_unique, Finset.prod_singleton]
  have hG' : G = fun x => (∏ _w : Unit, ga (pa x)) * ∏ᶠ v, gf v (pf v x) := funext fun x => by
    obtain ⟨T, hT⟩ := GlobalTheory.RestrMeas.exists_finset_of_eventually (h.eventually_mem x)
    have hT' : ∀ v ∉ S₀ ∪ T, pf v x ∈ K v := fun v hv => hT v fun e => hv (Finset.mem_union_right _ e)
    rw [hG (S₀ ∪ T) x Finset.subset_union_left hT',
      GlobalTheory.RestrMeas.finprod_eq_prod_of_mem (K := fun v => (K v : Set (Yf v))) (pf := fun v => pf v)
      (S := S₀ ∪ T) (fun v hv => hg1 v fun e => hv (Finset.mem_union_left _ e)) hT', Finset.univ_unique,
      Finset.prod_singleton]
  set L := ∫⁻ x, A x ∂ν with hL
  set I := ∫⁻ y, a y ∂μa with hI
  have hbd : ∀ T : Finset V, I * ∏ v ∈ T, ∫⁻ y, b v y ∂μf v ≤ L := fun T => by
    have := hc.setLIntegral_tensor ha hf hK (fa := fun _ => a) (ff := b) (S := T) (fun v _ => h1 v)
      (fun v _ => hb1 v) (fun _ => ma.aemeasurable) (fun v _ => (mb v).aemeasurable)
    rw [Finset.univ_unique, Finset.prod_singleton] at this
    rw [← this, hL]
    refine (setLIntegral_le_lintegral _ _).trans (le_of_eq (lintegral_congr fun x => ?_))
    rw [hA' x, Finset.univ_unique]
  have hI0 : I ≠ 0 := fun e => by
    have := (lintegral_eq_zero_iff ma).1 e
    obtain ⟨y, hy⟩ := this.exists
    exact ha0 y hy
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top hfin' (by simpa using hbd ∅)
  have hbd' : ∀ T : Finset V, ∏ v ∈ T, ∫⁻ y, b v y ∂μf v ≤ L / I := fun T =>
    (ENNReal.le_div_iff_mul_le (Or.inl hI0) (Or.inl hItop)).2 (by rw [mul_comm]; exact hbd T)
  have hLI : L / I ≠ ⊤ := ENNReal.div_ne_top hfin' hI0
  have hbtop : ∀ v, ∫⁻ y, b v y ∂μf v ≠ ⊤ := fun v => ne_top_of_le_ne_top hLI (by simpa using hbd' {v})
  have iga : Integrable ga μa := ⟨mga.aestronglyMeasurable, (lintegral_mono hga).trans_lt hItop.lt_top⟩
  have igf : ∀ v, Integrable (gf v) (μf v) := fun v =>
    ⟨(mgf v).aestronglyMeasurable, (lintegral_mono (hgf v)).trans_lt (hbtop v).lt_top⟩
  have hC : ∀ S : Finset V, S₀ ⊆ S → ∏ v ∈ S, ∫ y, ‖gf v y‖ ∂μf v ≤ (L / I).toReal := fun S _ => by
    refine le_trans ?_ (ENNReal.toReal_mono hLI (hbd' S))
    rw [ENNReal.toReal_prod]
    refine Finset.prod_le_prod (fun v _ => integral_nonneg fun _ => norm_nonneg _) fun v _ => ?_
    rw [integral_norm_eq_lintegral_enorm (igf v).1]
    exact ENNReal.toReal_mono (hbtop v) (lintegral_mono (hgf v))
  have hm := GlobalTheory.RestrMeas.multipliable_integral (K := fun v => (K v : Set (Yf v))) hK (fun v _ => h1 v) hg1 igf hC
  have he := hc.integral_tensor_eq_tprod ha hf hK (fa := fun _ => ga) h.eventually_mem (fun v _ => h1 v) hg1
    (fun _ => iga) igf hC
  refine ⟨_, hm.hasProd, ?_⟩
  rw [integral_smul_nnreal_measure, hG', he, Finset.univ_unique, Finset.prod_singleton, mul_assoc]
  rfl

theorem cpow_prod {ι : Type} (T : Finset ι) (a : ι → ℝ≥0) (z : ℂ) :
    (((∏ v ∈ T, a v : ℝ≥0) : ℝ) : ℂ) ^ z = ∏ v ∈ T, ((a v : ℝ) : ℂ) ^ z := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert v T hv ih =>
    rw [Finset.prod_insert hv, Finset.prod_insert hv, NNReal.coe_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), ih]

theorem zeta_euler : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ → min r s' = 0 → min r₁ s₁ = 0 → 1 ≤ n → n < d → Even d →
    ∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ K : Subgroup (UA σ X.J), IsStab B K → ∀ f ∈ M.Pol B.ψ B.emb, ∀ φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → pure f φ ≠ 0 →
    ∀ (μ : Measure (⊤ : Subgroup (UA σ X.J))) (μi : Measure (UAtSub σ X (evI F))) (μv : ∀ v : Pl F, Measure (UAtSub σ X (evFin F v))),
      μ.IsHaarMeasure → μi.IsHaarMeasure → (∀ v, (μv v).IsHaarMeasure ∧ μv v {g | g.1 ∈ K} = 1) →
      ∃ (c : ℂ) (R : ℝ), c ≠ 0 ∧ ∀ s : ℂ, R < s.re → ∃ P : ℂ, HasProd (fun v : Pl F => zetaOn m om (pure f φ) i K₂ _ (μv v) s) P ∧
        zetaOn m om (pure f φ) i K₂ ⊤ μ s = c * zetaOn m om (pure f φ) i K₂ _ μi s * P := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s' r₁ s₁ hP _ _ _ _ _ X₂ i K₂ hD _ _ m hm K hK f _ φ hSB hvac hne
    μ μi μv hμ hμi hμv
  classical
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  haveI : LocallyCompactSpace (UAtSub σ X (evI F)) := (isClosed_UAtSub X _).locallyCompactSpace
  haveI : ∀ v : Pl F, LocallyCompactSpace (UAtSub σ X (evFin F v)) := fun v => (isClosed_UAtSub X _).locallyCompactSpace
  haveI : ∀ v : Pl F, BorelSpace (UAtSub σ X (evFin F v)) := fun v => inferInstance
  haveI : ∀ v : Pl F, IsTopologicalGroup (UAtSub σ X (evFin F v)) := fun v => inferInstance
  haveI : ∀ v : Pl F, SecondCountableTopology (UAtSub σ X (evFin F v)) := fun v => inferInstance
  haveI := fun v => (hμv v).1
  have hR := GlobalTheory.T.restricted_product_unitary_group F E σ B n r s' X hP.base hP.herm K hK
  have hΦ : pure f φ ∈ schA F (Fin n × Fin d) := GlobalTheory.ConeMeasV.pure_mem_schA hP.good f φ hSB hvac
  obtain ⟨hc1, hcb, hcm⟩ := GlobalTheory.T.theta_lift_haar_integral_formula F E σ B n d X W M χX χW om r s' r₁ s₁ hP m hm _ hΦ hne
  have hcf := GlobalTheory.T.theta_lift_haar_integral_convergent hKP F E σ B n d X W M χX χW om r s' r₁ s₁ hP m hm f φ hSB hvac hc1
  have hcpt : IsCompact {k : UA σ X.J | compArch σ X.J k = 1 ∧ ∀ v, compAt σ X.J v k ∈ K} := by
    convert hR.isCompact_level (fun _ => {1}) (fun _ => isCompact_singleton) using 1
    ext k
    exact ⟨fun h => ⟨fun _ => Subtype.ext h.1, h.2⟩, fun h => ⟨congrArg Subtype.val (h.1 ()), h.2⟩⟩
  obtain ⟨S₀, hfix⟩ := GlobalTheory.T.theta_lift_schwartz_compact_invariant hKP F E σ B n d X W M χX χW om r s' r₁ s₁ hP K hcpt _ hΦ
  obtain ⟨hH1, hHm⟩ := GlobalTheory.T.doubling_height_function_invariant F E σ B n r s' X hP.base hP.herm X₂ i K₂ hD K hK
  obtain ⟨hHc, R, hHi⟩ := GlobalTheory.T.doubling_height_function_continuous F E σ B n r s' X hP.base hP.herm X₂ i K₂ hD
  set Φ := pure f φ with hΦdef
  have hHpos : ∀ g : UA σ X.J,
      0 < hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (g, 1)) := fun g => hgtOf_pos _
  unfold zetaOn
  generalize hHdef : (fun g : UA σ X.J =>
    hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (g, 1))) = H at hHc
  have hHe : ∀ g : UA σ X.J,
      hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (g, 1)) = H g := fun g => congrFun hHdef g
  simp only [hHe] at hH1 hHm hHi hHpos ⊢
  have hmul : ∀ g k : UA σ X.J, om (k, 1) Φ = Φ → coef m om Φ (g * k) = coef m om Φ g := fun g k hk => by
    unfold coef
    rw [show (g * k, (1 : UA σ W.J)) = (g, 1) * (k, 1) by simp, map_mul, Module.End.mul_apply, hk]
  have hcK : ∀ v ∉ S₀, ∀ k ∈ K, k ∈ UAt σ X (evFin F v) → coef m om Φ k = coef m om Φ 1 := fun v hv k hk hkv => by
    obtain ⟨h1, h2, h3⟩ := (SuppOne.comp_of_supp F E σ n X k).1 v hkv
    have := hmul 1 k (hfix k h2 (fun w => by
      by_cases e : w = v
      · rw [e, h1]; exact hk
      · rw [h3 w e]; exact one_mem _) fun w hw => h3 w fun e => hv (e ▸ hw))
    rwa [one_mul] at this
  have hcT : ∀ (T : Finset (Pl F)) (g : UA σ X.J), S₀ ⊆ T → (∀ v ∉ T, compAt σ X.J v g ∈ K) →
      coef m om Φ g / coef m om Φ 1 = coef m om Φ (compArch σ X.J g) / coef m om Φ 1 *
        ∏ v ∈ T, coef m om Φ (compAt σ X.J v g) / coef m om Φ 1 := fun T g hT hg => by
    obtain ⟨x, hxa, hxf⟩ := hR.exists_eq (fun _ => ⟨compArch σ X.J g, compArch_mem g⟩)
      (fun v => if v ∈ T then ⟨compAt σ X.J v g, compAt_mem v g⟩ else 1)
      (GlobalTheory.RestrMeas.eventually_of_finset T fun v hv => by rw [if_neg hv]; exact one_mem _)
    have ea : compArch σ X.J x = compArch σ X.J g := congrArg Subtype.val (hxa ())
    have e1 : ∀ v ∈ T, compAt σ X.J v x = compAt σ X.J v g := fun v hv => by
      have := hxf v; rw [if_pos hv] at this; exact congrArg Subtype.val this
    have e2 : ∀ v ∉ T, compAt σ X.J v x = 1 := fun v hv => by
      have := hxf v; rw [if_neg hv] at this; exact congrArg Subtype.val this
    have hk := hfix (x⁻¹ * g) (by rw [map_mul, map_inv, ea, inv_mul_cancel]) (fun v => by
      by_cases hv : v ∈ T
      · rw [map_mul, map_inv, e1 v hv, inv_mul_cancel]; exact one_mem _
      · rw [map_mul, map_inv, e2 v hv, inv_one, one_mul]; exact hg v hv)
      fun v hv => by rw [map_mul, map_inv, e1 v (hT hv), inv_mul_cancel]
    have := hmul x _ hk
    rw [mul_inv_cancel_left] at this
    rw [this, hcf T x e2, ea]
    exact congrArg _ (Finset.prod_congr rfl fun v hv => by rw [e1 v hv])
  have hemb : MeasurableEmbedding (Subtype.val : (⊤ : Subgroup (UA σ X.J)) → UA σ X.J) :=
    MeasurableEmbedding.subtype_coe (s := ((⊤ : Subgroup (UA σ X.J)) : Set (UA σ X.J))) MeasurableSet.univ
  haveI hμ' : (μ.map (Subtype.val : (⊤ : Subgroup (UA σ X.J)) → UA σ X.J)).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μ (Subgroup.topEquiv (G := UA σ X.J)) continuous_subtype_val
      (continuous_id.subtype_mk _)
  obtain ⟨c, hc0, hE⟩ := euler_of_majorant hR (μ.map Subtype.val) μi μv (fun v => (hμv v).2)
  refine ⟨c, R + ((d : ℝ) - n) / 2, by exact_mod_cast hc0, fun s hs => ?_⟩
  set z := s - ((d : ℂ) - (n : ℂ)) / 2 with hz
  have hzre : R < z.re := by
    have : z.re = s.re - ((d : ℝ) - n) / 2 := by simp [hz]
    linarith
  let G : UA σ X.J → ℂ := fun g => coef m om Φ g / coef m om Φ 1 * (((H g : ℝ≥0) : ℝ) : ℂ) ^ z
  let A : UA σ X.J → ℝ≥0∞ := fun g => ENNReal.ofReal ((H g : ℝ) ^ z.re)
  have hp : ∀ g, (0 : ℝ) < H g := hHpos
  have mH : Measurable fun g => (H g : ℝ) := (NNReal.continuous_coe.comp hHc).measurable
  have mG : Measurable G := (hcm.div_const _).mul ((Complex.measurable_ofReal.comp mH).pow_const _)
  have mA : Measurable A := (mH.pow_const _).ennreal_ofReal
  have hGA : ∀ g, ‖G g‖ₑ ≤ A g := fun g => by
    rw [← ofReal_norm_eq_enorm]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [G]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hp g), norm_div]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (hp g).le _) (div_le_one_of_le₀ (hcb g) (norm_nonneg _))
  obtain ⟨P, hP1, hP2⟩ := hE S₀ G (fun y => G y.1) (fun v y => G y.1) A (fun y => A y.1) (fun v y => A y.1)
    (mG.comp measurable_subtype_coe) (fun v => mG.comp measurable_subtype_coe) (mA.comp measurable_subtype_coe)
    (fun v => mA.comp measurable_subtype_coe) (fun y => hGA _) (fun v y => hGA _)
    (fun y => (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (hp _) _)).ne')
    (fun v y hy => by simp [A, hH1 y.1 hy])
    (fun v hv y hy => by simp [G, hH1 y.1 hy, hcK v hv y.1 hy y.2, div_self hc1])
    (fun T x hT hx => by
      change G x = G (compArch σ X.J x) * ∏ v ∈ T, G (compAt σ X.J v x)
      simp only [G]
      rw [hcT T x hT hx, hHm T x hx, Finset.prod_mul_distrib, NNReal.coe_mul, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), cpow_prod]
      ring)
    (fun T x hx => by
      change A x = A (compArch σ X.J x) * ∏ v ∈ T, A (compAt σ X.J v x)
      simp only [A]
      rw [hHm T x hx, NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _),
        ENNReal.ofReal_mul (Real.rpow_nonneg (NNReal.coe_nonneg _) _), NNReal.coe_prod,
        ← Real.finset_prod_rpow _ _ (fun _ _ => NNReal.coe_nonneg _),
        ENNReal.ofReal_prod_of_nonneg fun _ _ => Real.rpow_nonneg (NNReal.coe_nonneg _) _])
    (hHi _ hμ' _ hzre).lintegral_lt_top.ne
  refine ⟨P, hP1, ?_⟩
  rw [hemb.integral_map] at hP2
  exact hP2

end GlobalTheory.ThK.Bot.Euler

end

import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateOperatorLevelComplementStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTateMaximalIdealKillsFirstCohomologyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc.LogClass

variable {l : ℕ} [Fact l.Prime]

theorem ks_le_kinf (K : FinExt l) (s : ℕ) : Ks K s ≤ Kinf K :=
  sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun (x : Om l) (hx : x ^ (l ^ s) = 1) =>
    (⟨s, hx⟩ : ∃ j : ℕ, x ^ (l ^ j) = 1)) _

theorem hinf_le_gj (K : FinExt l) (s : ℕ) : Hinf K ≤ Gj K s :=
  IntermediateField.fixingSubgroup_antitone (ks_le_kinf K s)

theorem gj_le (K : FinExt l) (s : ℕ) : Gj K s ≤ (K0 K).fixingSubgroup :=
  IntermediateField.fixingSubgroup_antitone (show K0 K ≤ Ks K s from le_sup_left)

theorem act_inC {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {g : GQ l} (hg : g ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ inC F) : act g y = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [ha.1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x hx]

theorem algebraMap_eq (q : ℚ_[l]) :
    algebraMap ℚ_[l] (PadicComplex l) q = ((algebraMap ℚ_[l] (Om l) q : Om l) : PadicComplex l) :=
  IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l) q

theorem act_algebraMap {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    (g : GQ l) (q : ℚ_[l]) :
    act g (algebraMap ℚ_[l] (PadicComplex l) q) = algebraMap ℚ_[l] (PadicComplex l) q := by
  rw [algebraMap_eq, ha.1, AlgEquiv.commutes]

theorem norm_algMap (q : ℚ_[l]) : ‖algebraMap ℚ_[l] (PadicComplex l) q‖ = ‖q‖ := by
  rw [algebraMap_eq, PadicComplex.norm_extends, PadicAlgCl.norm_extends]

theorem continuous_algMap : Continuous (algebraMap ℚ_[l] (PadicComplex l)) :=
  (AddMonoidHomClass.isometry_of_norm _ norm_algMap).continuous

theorem chiC_mul (χ : GQ l →* ℚ_[l]ˣ) (j : ℤ) (g h : GQ l) :
    chiC χ j (g * h) = chiC χ j g * chiC χ j h := by
  simp only [chiC, map_mul, mul_zpow, Units.val_mul]

theorem norm_l_lt : ‖(l : PadicComplex l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicComplex l)), norm_algMap]
  exact Padic.norm_p_lt_one

theorem norm_l_pow (n : ℕ) : ‖(l : PadicComplex l) ^ n‖ = (l : ℝ) ^ (-(n : ℤ)) := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicComplex l)), ← map_pow, norm_algMap]
  exact Padic.norm_p_pow n

theorem ohat_norm (K : FinExt l) {y : PadicComplex l} (hy : y ∈ Ohat K) : ‖y‖ ≤ 1 := by
  have : closure (intC (Kinf K)) ⊆ {y : PadicComplex l | ‖y‖ ≤ 1} :=
    closure_minimal (fun _ h => h.2) (isClosed_le continuous_norm continuous_const)
  exact this hy

theorem exists_zeta (K : FinExt l) (s : ℕ) (hs : 1 ≤ s) :
    ∃ ζ : PadicComplex l, IsPrimitiveRoot ζ l ∧ ζ ∈ inC (Ks K s) ∧
      ‖(l : PadicComplex l)‖ ≤ ‖ζ - 1‖ := by
  have hp : l.Prime := Fact.out
  haveI : NeZero l := ⟨hp.ne_zero⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hz' : IsPrimitiveRoot (z : PadicComplex l) l :=
    hz.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _)
  refine ⟨z, hz', ⟨z, ?_, rfl⟩, ?_⟩
  · apply (show _ ≤ Ks K s from le_sup_right)
    apply IntermediateField.subset_adjoin
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
    simp [pow_add, pow_mul, hz.pow_eq_one]
  · generalize (z : PadicComplex l) = ζ at hz'
    have hn : ‖ζ‖ = 1 := by
      have := congrArg norm hz'.pow_eq_one
      rw [norm_pow, norm_one] at this
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hp.ne_zero).1 this
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hp.two_le
    have hm' : l = (m + 1) + 1 := by omega
    have h2 : IsPrimitiveRoot ζ ((m + 1) + 1) := hm' ▸ hz'
    have h3 := h2.prod_one_sub_pow_eq_order
    have h4 : (l : PadicComplex l) = ((m + 1 : ℕ) : PadicComplex l) + 1 := by
      rw [← Nat.cast_succ]; exact congrArg Nat.cast hm'
    rw [h4, ← h3, Finset.prod_range_succ', norm_mul, norm_prod, norm_sub_rev ζ]
    simp only [zero_add, pow_one]
    refine mul_le_of_le_one_left (norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) ?_)
    intro i _
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    simp [hn]

theorem vanish {G M : Type} [Group G] [TopologicalSpace G] [AddCommGroup M] [TopologicalSpace M]
    [T1Space M] (S H : Subgroup G) (hHS : H ≤ S) (A : G → M → M) (hA0 : ∀ g, A g 0 = 0)
    (d : G → M) (hc : ContinuousOn d S)
    (hd : ∀ g ∈ S, ∀ h ∈ S, d (g * h) = d g + A g (d h)) (γ : G) (hγ : γ ∈ S)
    (dense : (S : Set G) ⊆ closure {x | ∃ h ∈ H, ∃ a : ℕ, x = h * γ ^ a})
    (hH : ∀ h ∈ H, d h = 0) (hdγ : d γ = 0) : ∀ σ ∈ S, d σ = 0 := by
  have hpow : ∀ a : ℕ, d (γ ^ a) = 0 := by
    intro a
    induction a with
    | zero => simpa using hH 1 H.one_mem
    | succ a ih => rw [pow_succ, hd _ (S.pow_mem hγ a) _ hγ, ih, hdγ, hA0, add_zero]
  intro σ hσ
  have hsub : {x | ∃ h ∈ H, ∃ a : ℕ, x = h * γ ^ a} ⊆ (S : Set G) := by
    rintro _ ⟨h, hh, a, rfl⟩
    exact S.mul_mem (hHS hh) (S.pow_mem hγ a)
  have h1 := ((hc σ hσ).mono hsub).mem_closure_image (dense hσ)
  have h2 : d '' {x | ∃ h ∈ H, ∃ a : ℕ, x = h * γ ^ a} ⊆ {0} := by
    rintro _ ⟨_, ⟨h, hh, a, rfl⟩, rfl⟩
    rw [Set.mem_singleton_iff, hd _ (hHS hh) _ (S.pow_mem hγ a), hH h hh, hpow, hA0, add_zero]
  exact closure_minimal h2 isClosed_singleton h1

theorem norm_chiC {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (j : ℤ) (g : GQ l) : ‖chiC χ j g‖ = 1 := by
  rw [chiC, norm_algMap, Units.val_zpow_eq_zpow_val, norm_zpow, (GlobalTheory.Cyc.cyc_basic l χ hχ).1,
    one_zpow]

theorem continuous_chiC {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (j : ℤ) : Continuous (chiC χ j) := by
  unfold chiC
  refine continuous_algMap.comp ?_
  simp only [Units.val_zpow_eq_zpow_val]
  exact (GlobalTheory.Cyc.cyc_basic l χ hχ).2.1.zpow₀ j fun g => Or.inl (Units.ne_zero _)

theorem chi_hinf {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) {h : GQ l} (hh : h ∈ Hinf K) :
    χ h = 1 :=
  ((GlobalTheory.Cyc.cyc_basic l χ hχ).2.2 K h (gj_le K 0 (hinf_le_gj K 0 hh))).2.1 hh

theorem conj_hinf {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) (s : ℕ) {g h : GQ l}
    (hg : g ∈ Gj K s) (hh : h ∈ Hinf K) : g⁻¹ * h * g ∈ Hinf K := by
  have h1 : g⁻¹ * h * g ∈ Gj K s :=
    (Gj K s).mul_mem ((Gj K s).mul_mem ((Gj K s).inv_mem hg) (hinf_le_gj K s hh)) hg
  refine ((GlobalTheory.Cyc.cyc_basic l χ hχ).2.2 K _ (gj_le K s h1)).2.2 ?_
  simp [chi_hinf hχ K hh]

theorem modify {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
    (ha : IsActC act) (hχ : IsCyc χ) (S : Subgroup (GQ l)) (j : ℤ) (n : ℕ)
    (c : GQ l → PadicComplex l)
    (hc : CocOn S (fun g y => chiC χ j g * act g y) {y | ‖y‖ ≤ 1} c) (x : PadicComplex l)
    (hx : ‖x‖ ≤ 1) :
    CocOn S (fun g y => chiC χ j g * act g y) {y | ‖y‖ ≤ 1}
      (fun g => (l : PadicComplex l) ^ n * c g - (chiC χ j g * act g x - x)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (continuousOn_const.mul hc.1).sub
      (((continuous_chiC hχ j).mul (GlobalTheory.Cyc.IsActC.continuous_orbit l act ha x)).sub continuous_const).continuousOn
  · intro g hg
    have h1 : ‖c g‖ ≤ 1 := hc.2.1 g hg
    have h2 : ‖(l : PadicComplex l) ^ n * c g‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) norm_l_lt.le) (norm_nonneg _) h1
    have h3 : ‖chiC χ j g * act g x‖ ≤ 1 := by
      rw [norm_mul, norm_chiC hχ, ha.2, one_mul]; exact hx
    have sub : ∀ a b : PadicComplex l, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖a - b‖ ≤ 1 := by
      intro a b h h'
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_neg]; exact max_le h h'
    exact sub _ _ h2 (sub _ _ h3 hx)
  · intro g hg h hh
    have hfix : act g (chiC χ j h) = chiC χ j h := act_algebraMap ha g _
    have := hc.2.2 g hg h hh
    simp only at this ⊢
    rw [this, chiC_mul]
    simp only [map_mul, map_sub, map_pow, map_natCast, hfix, RingAut.mul_apply]
    ring

theorem mem_inC_iff (F : IntermediateField ℚ_[l] (Om l)) (y : PadicComplex l) :
    y ∈ inC F ↔ y ∈ F.toSubfield.map (algebraMap (Om l) (PadicComplex l)) := Iff.rfl

theorem algebraMap_mem_inC (F : IntermediateField ℚ_[l] (Om l)) (u : ℚ_[l]) :
    algebraMap ℚ_[l] (PadicComplex l) u ∈ inC F :=
  ⟨algebraMap ℚ_[l] (Om l) u, F.algebraMap_mem u, rfl⟩

theorem exists_scale (y : PadicComplex l) : ∃ n : ℕ, ‖(l : PadicComplex l) ^ n * y‖ ≤ 1 := by
  have hl : ‖(l : PadicComplex l)‖ < 1 := by
    have h1 : ‖algebraMap ℚ_[l] (PadicComplex l) (l : ℚ_[l])‖ = ‖(l : ℚ_[l])‖ := norm_algebraMap' _ _
    rw [map_natCast] at h1
    rw [h1]
    exact Padic.norm_p_lt_one
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const ‖y‖
  rw [zero_mul] at h
  obtain ⟨n, hn⟩ := (h.eventually (ge_mem_nhds (zero_lt_one' ℝ))).exists
  exact ⟨n, by rwa [norm_mul, norm_pow]⟩

def logC (χ : GQ l →* ℚ_[l]ˣ) (σ : GQ l) : PadicComplex l :=
  algebraMap ℚ_[l] (PadicComplex l) (logZl l (χ σ : ℚ_[l]))

theorem logC_mul {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (g h : GQ l) :
    logC χ (g * h) = logC χ g + logC χ h := by
  have hn := (GlobalTheory.Cyc.cyc_basic l χ hχ).1
  rw [logC, map_mul, Units.val_mul, (GlobalTheory.PadicLogUnits.logZl_hom l).1 _ _ (hn g) (hn h), map_add]
  rfl

theorem logC_hinf {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) {h : GQ l}
    (hh : h ∈ Hinf K) : logC χ h = 0 := by
  have h1 := logC_mul hχ 1 1
  rw [mul_one] at h1
  have h2 : logC χ h = logC χ 1 := by rw [logC, logC, chi_hinf hχ K hh, map_one χ]
  rw [h2]
  linear_combination -h1

theorem continuous_logC {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) : Continuous (logC χ) :=
  continuous_algMap.comp ((GlobalTheory.PadicLogUnits.logZl_hom l).2.1.comp_continuous
    (GlobalTheory.Cyc.cyc_basic l χ hχ).2.1 (GlobalTheory.Cyc.cyc_basic l χ hχ).1)

theorem norm_logC {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {s : ℕ} (hs : Lev l s) {γ : GQ l}
    (hγ : IsGen χ K s γ) : ‖logC χ γ‖ = (l : ℝ) ^ (-(s : ℤ)) := by
  rw [logC, norm_algMap, (GlobalTheory.PadicLogUnits.logZl_hom l).2.2.2 s hs.1 hs.2 _ hγ.2.le,
    hγ.2]

theorem logC_ne_zero {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {s : ℕ} (hs : Lev l s) {γ : GQ l}
    (hγ : IsGen χ K s γ) : logC χ γ ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_logC hs hγ]
  exact (zpow_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos : (0 : ℝ) < l) _).ne'

theorem logC_mem (χ : GQ l →* ℚ_[l]ˣ) (F : IntermediateField ℚ_[l] (Om l)) (σ : GQ l) :
    logC χ σ ∈ inC F := algebraMap_mem_inC F _

theorem exists_coeff {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
    (ha : IsActC act) (hχ : IsCyc χ) (K : FinExt l) (s : ℕ) (hs : Lev l s)
    (c : GQ l → PadicComplex l) (hc : CocOn (Gj K s) (fun g y => act g y) {y | ‖y‖ ≤ 1} c) :
    ∃ α ∈ inC (Ks K s), ‖α‖ ≤ (l : ℝ) ^ (1 + s) ∧ ∃ b : PadicComplex l,
      ∀ σ ∈ Gj K s, c σ = logC χ σ * α + (act σ b - b) := by
  have hp : l.Prime := Fact.out
  have hle := hinf_le_gj K s
  have hl0 : (l : PadicComplex l) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hlR : (0 : ℝ) < l := by exact_mod_cast hp.pos
  obtain ⟨x, hx, hx2⟩ := GlobalTheory.T.cyclotomic_tate_maximalIdeal_kills_first_cohomology l act ha K 1 (l : PadicComplex l)
    ⟨l, natCast_mem (Kinf K) l, by simp⟩ norm_l_lt (fun g _ => c g)
    ⟨continuousOn_pi.2 fun _ => hc.1.mono hle, fun g hg _ => hc.2.1 g (hle hg),
      fun g hg h hh => by
        funext k
        exact hc.2.2 g (hle hg) h (hle hh)⟩
  have hx3 : ∀ h ∈ Hinf K, (l : PadicComplex l) * c h = act h (x 0) - x 0 := fun h hh => by
    simpa using congrFun (hx2 h hh) 0
  have hc1 : CocOn (Gj K s) (fun g y => act g y) {y | ‖y‖ ≤ 1}
      (fun g => (l : PadicComplex l) * c g - (act g (x 0) - x 0)) := by
    have := modify ha hχ (Gj K s) 0 1 c (by simpa [chiC] using hc) (x 0) (hx 0)
    simpa [chiC] using this
  set c1 : GQ l → PadicComplex l :=
    fun g => (l : PadicComplex l) * c g - (act g (x 0) - x 0) with hc1def
  have hc1H : ∀ h ∈ Hinf K, c1 h = 0 := fun h hh => by
    simp only [hc1def, hx3 h hh, sub_self]
  obtain ⟨⟨γ, hγ⟩, hgen⟩ := GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties l act χ ha hχ K s hs
  have hO : c1 γ ∈ Ohat K := by
    refine (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K _ (hc1.2.1 γ hγ.1)).1 fun h hh => ?_
    have hconj := conj_hinf hχ K s hγ.1 hh
    have e1 := hc1.2.2 h (hle hh) γ hγ.1
    have e2 := hc1.2.2 γ hγ.1 _ (hle hconj)
    have e3 : γ * (γ⁻¹ * h * γ) = h * γ := by group
    rw [e3, e1, hc1H h hh, hc1H _ hconj] at e2
    simpa using e2
  obtain ⟨T1a, -, T1c, -⟩ := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ ha hχ K s hs.1
  obtain ⟨y, hy, w, hw, hyw⟩ := T1a _ hO
  obtain ⟨ζ, hζ, hζK, -⟩ := exists_zeta K s hs.1
  have hζ0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (hζ.ne_one hp.one_lt)
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.exists_tate_operator_levelComplement l act χ ha hχ K s hs γ hγ ζ hζ
  obtain ⟨hv, hv2, -⟩ := hS w hw
  have hvO := T1c _ hv
  have hz : ∀ g ∈ Gj K s, act g (S w / (ζ - 1)) = act g (S w) / (ζ - 1) := fun g hg => by
    rw [map_div₀, map_sub, map_one, act_inC ha hg hζK]
  have hL0 := logC_ne_zero hs hγ
  have hβ : y / logC χ γ ∈ inC (Ks K s) := by
    rw [mem_inC_iff]
    exact Subfield.div_mem _ hy.1 (logC_mem χ _ γ)
  have key := vanish (Gj K s) (Hinf K) hle (fun g y => act g y) (fun g => by simp)
    (fun g => c1 g - logC χ g * (y / logC χ γ) - (act g (S w / (ζ - 1)) - S w / (ζ - 1)))
    ((hc1.1.sub ((continuous_logC hχ).mul continuous_const).continuousOn).sub
      ((GlobalTheory.Cyc.IsActC.continuous_orbit l act ha _).sub continuous_const).continuousOn)
    (fun g hg h hh => by
      have h1 := hc1.2.2 g hg h hh
      have h2 : act g (logC χ h) = logC χ h := act_algebraMap ha g _
      have h3 := act_inC ha hg hβ
      generalize S w / (ζ - 1) = z
      generalize y / logC χ γ = β at h3 ⊢
      clear_value c1
      simp only [h1, logC_mul hχ, map_sub, map_mul, h2, h3, RingAut.mul_apply]
      ring)
    γ hγ.1 (hgen γ hγ).2.2
    (fun h hh => by
      rw [hc1H h hh, logC_hinf hχ K hh, hz h (hle hh),
        (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K _ (ohat_norm K hvO)).2 hvO h hh]
      ring)
    (by
      rw [hz γ hγ.1, ← sub_div, hv2, hyw, mul_div_cancel₀ _ hL0, mul_div_cancel_left₀ _ hζ0]
      ring)
  refine ⟨y / logC χ γ / l, ?_, ?_, (x 0 + S w / (ζ - 1)) / l, fun σ hσ => ?_⟩
  · rw [mem_inC_iff]
    exact Subfield.div_mem _ hβ (natCast_mem _ l)
  · have h1 := norm_l_pow (l := l) 1
    rw [pow_one] at h1
    rw [norm_div, norm_div, norm_logC hs hγ, h1, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast,
      div_inv_eq_mul, div_inv_eq_mul, mul_assoc, ← pow_add, add_comm s 1]
    exact mul_le_of_le_one_left (by positivity) hy.2
  · have := key σ hσ
    simp only [hc1def] at this
    rw [map_div₀ (act σ) _ (l : PadicComplex l), map_natCast, map_add]
    generalize S w / (ζ - 1) = z at this ⊢
    generalize y / logC χ γ = β at this ⊢
    field_simp
    linear_combination this

theorem coeff_eq_zero {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
    (ha : IsActC act) (hχ : IsCyc χ) (K : FinExt l) (s : ℕ) (hs : Lev l s)
    (α : PadicComplex l) (hα : α ∈ inC (Ks K s)) (b : PadicComplex l)
    (hb : ∀ σ ∈ Gj K s, logC χ σ * α = act σ b - b) : α = 0 := by
  have hl0 : (l : PadicComplex l) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  obtain ⟨⟨γ, hγ⟩, -⟩ := GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties l act χ ha hχ K s hs
  obtain ⟨T1a, T1b, -, -, T1e, -⟩ := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ ha hχ K s hs.1
  obtain ⟨n, hn⟩ := exists_scale b
  have hO : (l : PadicComplex l) ^ n * b ∈ Ohat K := by
    refine (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K _ hn).1 fun h hh => ?_
    have := hb h (hinf_le_gj K s hh)
    rw [logC_hinf hχ K hh, zero_mul, eq_comm, sub_eq_zero] at this
    rw [map_mul, map_pow, map_natCast, this]
  obtain ⟨y, hy, x, hx, hyx⟩ := T1a _ hO
  have h1 := congrArg (act γ) hyx
  rw [map_mul, map_pow, map_natCast, map_add, act_inC ha hγ.1 hy.1] at h1
  have h2 : logC χ γ * α = 0 := by
    refine T1b _ ?_ _ ((Xj K s).sub_mem (T1e γ (gj_le K s hγ.1) x hx) hx) n ?_
    · rw [mem_inC_iff]
      exact Subfield.mul_mem _ (logC_mem χ _ γ) hα
    · rw [hb γ hγ.1]
      linear_combination h1 - hyx
  exact (mul_eq_zero.1 h2).resolve_left (logC_ne_zero hs hγ)

theorem image_H1_logChi : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ s : ℕ, Lev l s → (∀ c : GQ l → PadicComplex l, CocOn (Gj K s) (fun g y => act g y) {y | ‖y‖ ≤ 1} c → ∃ α ∈ inC (Ks K s), ‖α‖ ≤ (l : ℝ) ^ (1 + s) ∧ ∃ b : PadicComplex l, ∀ σ ∈ Gj K s, c σ = algebraMap ℚ_[l] (PadicComplex l) (logZl l (χ σ : ℚ_[l])) * α + (act σ b - b)) ∧ ∀ α ∈ inC (Ks K s), ∀ b : PadicComplex l, (∀ σ ∈ Gj K s, algebraMap ℚ_[l] (PadicComplex l) (logZl l (χ σ : ℚ_[l])) * α = act σ b - b) → α = 0 :=
  fun _ _ _ _ ha hχ K s hs =>
    ⟨fun c hc => exists_coeff ha hχ K s hs c hc, fun α hα b hb => coeff_eq_zero ha hχ K s hs α hα b hb⟩

end GlobalTheory.Cyc.LogClass

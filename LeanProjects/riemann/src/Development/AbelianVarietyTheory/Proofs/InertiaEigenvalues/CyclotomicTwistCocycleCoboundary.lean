import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicNormZpowSubOnePadicValIntStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerGeneratorMatrixPerturbationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTateMaximalIdealKillsFirstCohomologyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixedIffMemCompletedIntegersStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc.TwistKill

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

theorem norm_algebraMap (q : ℚ_[l]) : ‖algebraMap ℚ_[l] (PadicComplex l) q‖ = ‖q‖ := by
  rw [algebraMap_eq, PadicComplex.norm_extends, PadicAlgCl.norm_extends]

theorem continuous_algMap : Continuous (algebraMap ℚ_[l] (PadicComplex l)) :=
  (AddMonoidHomClass.isometry_of_norm _ norm_algebraMap).continuous

theorem chiC_mul (χ : GQ l →* ℚ_[l]ˣ) (j : ℤ) (g h : GQ l) :
    chiC χ j (g * h) = chiC χ j g * chiC χ j h := by
  simp only [chiC, map_mul, mul_zpow, Units.val_mul]

theorem norm_l_lt : ‖(l : PadicComplex l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicComplex l)), norm_algebraMap]
  exact Padic.norm_p_lt_one

theorem norm_l_pow (n : ℕ) : ‖(l : PadicComplex l) ^ n‖ = (l : ℝ) ^ (-(n : ℤ)) := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicComplex l)), ← map_pow, norm_algebraMap]
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
  rw [chiC, norm_algebraMap, Units.val_zpow_eq_zpow_val, norm_zpow, (GlobalTheory.Cyc.cyc_basic l χ hχ).1,
    one_zpow]

theorem continuous_chiC {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (j : ℤ) : Continuous (chiC χ j) := by
  unfold chiC
  refine continuous_algMap.comp ?_
  simp only [Units.val_zpow_eq_zpow_val]
  exact (GlobalTheory.Cyc.cyc_basic l χ hχ).2.1.zpow₀ j fun g => Or.inl (Units.ne_zero _)

theorem chi_hinf {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) {h : GQ l} (hh : h ∈ Hinf K) :
    χ h = 1 :=
  ((GlobalTheory.Cyc.cyc_basic l χ hχ).2.2 K h (gj_le K 0 (hinf_le_gj K 0 hh))).2.1 hh

theorem chiC_hinf {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) (j : ℤ) {h : GQ l}
    (hh : h ∈ Hinf K) : chiC χ j h = 1 := by
  simp [chiC, chi_hinf hχ K hh]

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

theorem solve {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
    (ha : IsActC act) (hχ : IsCyc χ) (K : FinExt l) (s : ℕ) (hs : Lev l s) (j : ℤ) (hj : j ≠ 0)
    (γ : GQ l) (hγ : IsGen χ K s γ) (w : PadicComplex l) (hw : w ∈ Ohat K) :
    ∃ z : PadicComplex l, ‖z‖ ≤ 1 ∧ (∀ h ∈ Hinf K, act h z = z) ∧
      chiC χ j γ * act γ z - z = (l : PadicComplex l) ^ (s + padicValInt l j) * w := by
  have hp : l.Prime := Fact.out
  obtain ⟨T1a, -, T1c, -⟩ := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ ha hχ K s hs.1
  obtain ⟨y, hy, x, hx, rfl⟩ := T1a w hw
  obtain ⟨ζ, hζ, hζK, hζn⟩ := exists_zeta K s hs.1
  have hrho : 0 < rho1 l := Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _
  obtain ⟨v, hv, hv2⟩ := (GlobalTheory.T.cyclotomic_tower_generator_matrix_perturbation l act χ ha hχ K s hs γ hγ 1 (fun _ => 1)
    (by
      intro a b
      rw [Subsingleton.elim a b, Matrix.one_apply_eq]
      exact ⟨⟨1, (Ks K s).one_mem, by simp⟩, by simp⟩)
    (by intro a b; simpa using hrho) j).2 ζ hζ (fun _ => x) (fun _ => hx)
  have hv3 : chiC χ j γ * act γ (v 0) - v 0 = (ζ - 1) * x := by
    simpa [twAct] using congrFun hv2 0
  have hvO := T1c _ (hv 0)
  set n := s + padicValInt l j with hn
  have hval : ‖chiC χ j γ - 1‖ = ‖(l : PadicComplex l) ^ n‖ := by
    have := GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt l s hs _ hγ.2 j hj
    rw [norm_l_pow, chiC, ← map_one (algebraMap ℚ_[l] (PadicComplex l)), ← map_sub,
      norm_algebraMap, Units.val_zpow_eq_zpow_val, this, hn]
    push_cast; rfl
  have hl0 : (l : PadicComplex l) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hu0 : chiC χ j γ - 1 ≠ 0 := by
    rw [← norm_ne_zero_iff, hval, norm_ne_zero_iff]; exact pow_ne_zero _ hl0
  have hζ0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (hζ.ne_one hp.one_lt)
  have hfix : ∀ g ∈ Gj K s, act g ((l : PadicComplex l) ^ n / (chiC χ j γ - 1) * y) =
      (l : PadicComplex l) ^ n / (chiC χ j γ - 1) * y := by
    intro g hg
    have h1 : act g (chiC χ j γ) = chiC χ j γ := act_algebraMap ha g _
    simp only [map_mul, map_div₀, map_pow, map_natCast, map_sub, map_one, h1,
      act_inC ha hg hy.1]
  have hfix2 : ∀ g ∈ Gj K s, act g ((l : PadicComplex l) ^ n / (ζ - 1)) =
      (l : PadicComplex l) ^ n / (ζ - 1) := by
    intro g hg
    simp only [map_div₀, map_pow, map_natCast, map_sub, map_one, act_inC ha hg hζK]
  refine ⟨(l : PadicComplex l) ^ n / (chiC χ j γ - 1) * y + (l : PadicComplex l) ^ n / (ζ - 1) * v 0,
    ?_, ?_, ?_⟩
  · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_div, hval, div_self (norm_ne_zero_iff.2 (pow_ne_zero _ hl0)), one_mul]
      exact hy.2
    · rw [norm_mul, norm_div]
      refine mul_le_one₀ ?_ (norm_nonneg _) (ohat_norm K hvO)
      rw [div_le_one (norm_pos_iff.2 hζ0), norm_pow]
      refine le_trans ?_ hζn
      have := hs.1
      exact pow_le_of_le_one (norm_nonneg _) norm_l_lt.le (by omega)
  · intro h hh
    rw [map_add, hfix h (hinf_le_gj K s hh), map_mul (act h) _ (v 0), hfix2 h (hinf_le_gj K s hh),
      (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K _ (ohat_norm K hvO)).2 hvO h hh]
  · rw [map_add, hfix γ hγ.1, map_mul (act γ) _ (v 0), hfix2 γ hγ.1]
    have e : chiC χ j γ * act γ (v 0) = v 0 + (ζ - 1) * x := by rw [← hv3]; ring
    have e1 : (l : PadicComplex l) ^ n / (chiC χ j γ - 1) * (chiC χ j γ - 1) = l ^ n :=
      div_mul_cancel₀ _ hu0
    have e2 : (l : PadicComplex l) ^ n / (ζ - 1) * (ζ - 1) = l ^ n := div_mul_cancel₀ _ hζ0
    linear_combination y * e1 + x * e2 + ((l : PadicComplex l) ^ n / (ζ - 1)) * e

theorem pow_kills_cyclotomic_H1 (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l))
    (χ : GQ l →* ℚ_[l]ˣ) (ha : IsActC act) (hχ : IsCyc χ) (K : FinExt l) (s : ℕ) (hs : Lev l s)
    (j : ℤ) (hj : j ≠ 0) (c : GQ l → PadicComplex l)
    (hc : CocOn (Gj K s) (fun g y => chiC χ j g * act g y) {y | ‖y‖ ≤ 1} c) :
    CobOn (Gj K s) (fun g y => chiC χ j g * act g y) {y | ‖y‖ ≤ 1}
      (fun g => (l : PadicComplex l) ^ (1 + s + padicValInt l j) * c g) := by
  have hle := hinf_le_gj K s
  obtain ⟨x, hx, hx2⟩ := GlobalTheory.T.cyclotomic_tate_maximalIdeal_kills_first_cohomology l act ha K 1 (l : PadicComplex l)
    ⟨l, natCast_mem (Kinf K) l, by simp⟩ norm_l_lt (fun g _ => c g)
    ⟨continuousOn_pi.2 fun _ => hc.1.mono hle, fun g hg _ => hc.2.1 g (hle hg),
      fun g hg h hh => by
        funext k
        have := hc.2.2 g (hle hg) h (hle hh)
        simpa [chiC_hinf hχ K j hg] using this⟩
  have hx3 : ∀ h ∈ Hinf K, (l : PadicComplex l) * c h = act h (x 0) - x 0 := fun h hh => by
    simpa using congrFun (hx2 h hh) 0
  have hc1 := modify ha hχ (Gj K s) j 1 c hc (x 0) (hx 0)
  set c1 : GQ l → PadicComplex l :=
    fun g => (l : PadicComplex l) ^ 1 * c g - (chiC χ j g * act g (x 0) - x 0) with hc1def
  have hc1H : ∀ h ∈ Hinf K, c1 h = 0 := fun h hh => by
    simp only [hc1def, pow_one, hx3 h hh, chiC_hinf hχ K j hh, one_mul, sub_self]
  obtain ⟨⟨γ, hγ⟩, hgen⟩ := GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties l act χ ha hχ K s hs
  have hO : c1 γ ∈ Ohat K := by
    refine (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K _ (hc1.2.1 γ hγ.1)).1 fun h hh => ?_
    have hconj := conj_hinf hχ K s hγ.1 hh
    have e1 := hc1.2.2 h (hle hh) γ hγ.1
    have e2 := hc1.2.2 γ hγ.1 _ (hle hconj)
    have e3 : γ * (γ⁻¹ * h * γ) = h * γ := by group
    rw [e3, e1, hc1H h hh, hc1H _ hconj] at e2
    simpa [chiC_hinf hχ K j hh] using e2
  obtain ⟨z, hz, hzH, hzγ⟩ := solve ha hχ K s hs j hj γ hγ _ hO
  have hc2 := modify ha hχ (Gj K s) j (s + padicValInt l j) c1 hc1 z hz
  have key := vanish (Gj K s) (Hinf K) hle (fun g y => chiC χ j g * act g y)
    (fun g => by simp) _ hc2.1 hc2.2.2 γ hγ.1
    (hgen γ hγ).2.2
    (fun h hh => by simp [hc1H h hh, hzH h hh, chiC_hinf hχ K j hh])
    (by simp only [hzγ, sub_self])
  refine ⟨(l : PadicComplex l) ^ (s + padicValInt l j) * x 0 + z, ?_, fun g hg => ?_⟩
  · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hz)
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) norm_l_lt.le) (norm_nonneg _) (hx 0)
  · have := key g hg
    simp only [hc1def] at this
    simp only [map_add, map_mul, map_pow, map_natCast]
    linear_combination this

end GlobalTheory.Cyc.TwistKill

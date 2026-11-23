import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTateMaximalIdealKillsFirstCohomologyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleVanishingOnFixingSubgroupDeterminedByGeneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionCoinvariantsTwistedCyclotomicGeneratorStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc.FrameTorsion

section Basic

variable {l : ℕ} [Fact l.Prime]

theorem ks_le_kinf (K : FinExt l) (s : ℕ) : Ks K s ≤ Kinf K := by
  unfold Ks Kinf
  refine sup_le_sup_left ?_ _
  exact IntermediateField.adjoin.mono _ _ _ (fun x hx => ⟨s, hx⟩)

theorem hinf_le_gj (K : FinExt l) (s : ℕ) : Hinf K ≤ Gj K s := by
  intro g hg
  rw [Hinf, IntermediateField.mem_fixingSubgroup_iff] at hg
  rw [Gj, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact hg x (ks_le_kinf K s hx)

theorem gj_le (K : FinExt l) (s : ℕ) : Gj K s ≤ (K0 K).fixingSubgroup := by
  intro g hg
  rw [Gj, IntermediateField.mem_fixingSubgroup_iff] at hg
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  apply hg x
  unfold Ks
  exact (le_sup_left : K0 K ≤ _) hx

theorem act_inC {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {g : GQ l} (hg : g ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ inC F) : act g y = y := by
  obtain ⟨x, hxF, rfl⟩ := hy
  rw [ha.1 g x]
  congr 1
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x hxF

theorem algebraMap_eq (q : ℚ_[l]) :
    algebraMap ℚ_[l] (PadicComplex l) q = ((algebraMap ℚ_[l] (Om l) q : Om l) : PadicComplex l) := IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l) q

theorem act_algebraMap {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    (g : GQ l) (q : ℚ_[l]) :
    act g (algebraMap ℚ_[l] (PadicComplex l) q) = algebraMap ℚ_[l] (PadicComplex l) q := by
  rw [algebraMap_eq, ha.1 g, AlgEquiv.commutes]

theorem norm_algebraMap (q : ℚ_[l]) : ‖algebraMap ℚ_[l] (PadicComplex l) q‖ = ‖q‖ := by
  rw [algebraMap_eq, PadicComplex.norm_extends, PadicAlgCl.norm_extends]

theorem continuous_algMap : Continuous (algebraMap ℚ_[l] (PadicComplex l)) := by
  have hiso : Isometry (algebraMap ℚ_[l] (PadicComplex l)) :=
    AddMonoidHomClass.isometry_of_norm (algebraMap ℚ_[l] (PadicComplex l)) norm_algebraMap
  exact hiso.continuous

theorem chiC_mul (χ : GQ l →* ℚ_[l]ˣ) (j : ℤ) (g h : GQ l) :
    chiC χ j (g * h) = chiC χ j g * chiC χ j h := by
  simp only [chiC, map_mul, mul_zpow, Units.val_mul]

theorem norm_l_lt : ‖(l : PadicComplex l)‖ < 1 := by
  have h1 : (l : PadicComplex l) = algebraMap ℚ_[l] (PadicComplex l) (l : ℚ_[l]) := (map_natCast _ l).symm
  rw [h1, norm_algebraMap]
  exact Padic.norm_p_lt_one

theorem ohat_norm (K : FinExt l) {y : PadicComplex l} (hy : y ∈ Ohat K) : ‖y‖ ≤ 1 := by
  have hcl : IsClosed {y : PadicComplex l | ‖y‖ ≤ 1} := isClosed_le continuous_norm continuous_const
  exact closure_minimal (fun z hz => hz.2) hcl hy

theorem norm_chiC {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (j : ℤ) (g : GQ l) : ‖chiC χ j g‖ = 1 := by
  rw [chiC, norm_algebraMap, Units.val_zpow_eq_zpow_val, norm_zpow, IsCyc.norm_eq_one hχ g, one_zpow]

theorem continuous_chiC {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (j : ℤ) : Continuous (chiC χ j) := by
  have h0 : Continuous (fun g : GQ l => ((χ g : ℚ_[l])) ^ j) :=
    (IsCyc.continuous hχ).zpow₀ j (fun g => Or.inl (χ g).ne_zero)
  have h1 : chiC χ j = fun g => algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ j) := by
    funext g
    rw [chiC, Units.val_zpow_eq_zpow_val]
  rw [h1]
  exact continuous_algMap.comp h0

theorem chi_hinf {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) {h : GQ l} (hh : h ∈ Hinf K) :
    χ h = 1 := by
  have hK0 : h ∈ (K0 K).fixingSubgroup := gj_le K 0 (hinf_le_gj K 0 hh)
  exact ((cyc_basic l χ hχ).2.2 K h hK0).2.1 hh

theorem chiC_hinf {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) (j : ℤ) {h : GQ l}
    (hh : h ∈ Hinf K) : chiC χ j h = 1 := by
  rw [chiC, chi_hinf hχ K hh, one_zpow, Units.val_one, map_one]

theorem conj_hinf {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) (s : ℕ) {g h : GQ l}
    (hg : g ∈ Gj K s) (hh : h ∈ Hinf K) : g⁻¹ * h * g ∈ Hinf K := by
  have hg0 : g ∈ (K0 K).fixingSubgroup := gj_le K s hg
  have hh0 : h ∈ (K0 K).fixingSubgroup := gj_le K 0 (hinf_le_gj K 0 hh)
  have hx0 : g⁻¹ * h * g ∈ (K0 K).fixingSubgroup :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg0) hh0) hg0
  rw [((cyc_basic l χ hχ).2.2 K _ hx0).2]
  rw [map_mul, map_mul, chi_hinf hχ K hh, mul_one, map_inv, inv_mul_cancel]

end Basic

variable {l : ℕ} [Fact l.Prime] {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
  {χ : GQ l →* ℚ_[l]ˣ} {r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {i : ℤ}

theorem tw_add (σ : GQ l) (x y : Fin r → PadicComplex l) :
    twAct act χ i U σ (x + y) = twAct act χ i U σ x + twAct act χ i U σ y := by
  have hv : (fun a => act σ ((x + y) a)) = (fun a => act σ (x a)) + (fun a => act σ (y a)) := by
    funext a
    simp only [Pi.add_apply, map_add]
  simp only [twAct, hv, Matrix.mulVec_add, smul_add]

theorem tw_sub (σ : GQ l) (x y : Fin r → PadicComplex l) :
    twAct act χ i U σ (x - y) = twAct act χ i U σ x - twAct act χ i U σ y := by
  have hv : (fun a => act σ ((x - y) a)) = (fun a => act σ (x a)) - (fun a => act σ (y a)) := by
    funext a
    simp only [Pi.sub_apply, map_sub]
  simp only [twAct, hv, Matrix.mulVec_sub, smul_sub]

theorem tw_zero (σ : GQ l) : twAct act χ i U σ 0 = 0 := by
  have hv : (fun a => act σ ((0 : Fin r → PadicComplex l) a)) = 0 := by
    funext a
    simp only [Pi.zero_apply, map_zero]
  simp only [twAct, hv, Matrix.mulVec_zero, smul_zero]

theorem tw_pow (σ : GQ l) (n : ℕ) (x : Fin r → PadicComplex l) :
    twAct act χ i U σ ((l : PadicComplex l) ^ n • x)
      = (l : PadicComplex l) ^ n • twAct act χ i U σ x := by
  have hl : ∀ z : PadicComplex l, act σ ((l : PadicComplex l) ^ n * z) = (l : PadicComplex l) ^ n * act σ z := by
    intro z
    rw [map_mul, map_pow, map_natCast]
  have hv : (fun a => act σ (((l : PadicComplex l) ^ n • x) a)) = (l : PadicComplex l) ^ n • (fun a => act σ (x a)) := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, hl]
  simp only [twAct, hv, Matrix.mulVec_smul, smul_comm (chiC χ i σ)]

theorem ball_add {x y : Fin r → PadicComplex l} (hx : x ∈ ball l r) (hy : y ∈ ball l r) :
    x + y ∈ ball l r := by
  intro a
  calc ‖(x + y) a‖ = ‖x a + y a‖ := rfl
    _ ≤ max ‖x a‖ ‖y a‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le (hx a) (hy a)

theorem ball_sub {x y : Fin r → PadicComplex l} (hx : x ∈ ball l r) (hy : y ∈ ball l r) :
    x - y ∈ ball l r := by
  intro a
  calc ‖(x - y) a‖ = ‖x a + -y a‖ := by rw [Pi.sub_apply, sub_eq_add_neg]
    _ ≤ max ‖x a‖ ‖-y a‖ := IsUltrametricDist.norm_add_le_max _ _
    _ = max ‖x a‖ ‖y a‖ := by rw [norm_neg]
    _ ≤ 1 := max_le (hx a) (hy a)

theorem ball_pow (n : ℕ) {x : Fin r → PadicComplex l} (hx : x ∈ ball l r) :
    (l : PadicComplex l) ^ n • x ∈ ball l r := by
  intro a
  have hl1 : ‖(l : PadicComplex l)‖ ≤ 1 := le_of_lt norm_l_lt
  calc ‖((l : PadicComplex l) ^ n • x) a‖ = ‖(l : PadicComplex l)‖ ^ n * ‖x a‖ := by
        rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (norm_nonneg _) hl1) (hx a) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

variable {K : FinExt l} {m : ℕ} {g : GQ l}

theorem tw_ball (ha : IsActC act) (hχ : IsCyc χ) (hU : Frame χ K m U g) {σ : GQ l}
    (hσ : σ ∈ Gj K m) {x : Fin r → PadicComplex l} (hx : x ∈ ball l r) :
    twAct act χ i U σ x ∈ ball l r := by
  intro a
  have hU1 : ∀ b, ‖U σ a b‖ ≤ 1 := fun b => (hU.2.2.1 σ hσ a b).2
  have hs : ‖∑ b, U σ a b * act σ (x b)‖ ≤ 1 := by
    refine Finset.sum_induction _ (fun z : PadicComplex l => ‖z‖ ≤ 1) ?_ ?_ ?_
    · intro u v hu hv
      exact (IsUltrametricDist.norm_add_le_max u v).trans (max_le hu hv)
    · rw [norm_zero]
      exact zero_le_one
    · intro b _
      rw [norm_mul, ha.2]
      exact mul_le_one₀ (hU1 b) (norm_nonneg _) (hx b)
  have e : twAct act χ i U σ x a = chiC χ i σ * ∑ b, U σ a b * act σ (x b) := by
    simp only [twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  rw [e, norm_mul, norm_chiC hχ, one_mul]
  exact hs

theorem tw_hinf (hχ : IsCyc χ) (hU : Frame χ K m U g) {h : GQ l} (hh : h ∈ Hinf K)
    (x : Fin r → PadicComplex l) : twAct act χ i U h x = fun a => act h (x a) := by
  have hU1 : U h = 1 := hU.2.2.2.2.1 h hh
  rw [twAct, hU1, Matrix.one_mulVec, chiC_hinf hχ K i hh, one_smul]

theorem tw_mul (ha : IsActC act) (hU : Frame χ K m U g) {σ τ : GQ l} (hσ : σ ∈ Gj K m)
    (hτ : τ ∈ Gj K m) (x : Fin r → PadicComplex l) :
    twAct act χ i U (σ * τ) x = twAct act χ i U σ (twAct act χ i U τ x) := by
  have hσF : σ ∈ (Ks K m).fixingSubgroup := hσ
  have hfix : ∀ a b, act σ (U τ a b) = U τ a b := fun a b => act_inC ha hσF (hU.2.2.1 τ hτ a b).1
  have hc : act σ (chiC χ i τ) = chiC χ i τ := act_algebraMap ha σ _
  have hv : (fun a => act σ (twAct act χ i U τ x a))
      = chiC χ i τ • (U τ).mulVec (fun b => act σ (act τ (x b))) := by
    funext a
    simp only [twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, map_mul, map_sum, hfix, hc]
  have hστ : (fun b => act (σ * τ) (x b)) = fun b => act σ (act τ (x b)) := by
    funext b
    rw [map_mul]
    rfl
  show chiC χ i (σ * τ) • (U (σ * τ)).mulVec (fun b => act (σ * τ) (x b))
    = chiC χ i σ • (U σ).mulVec (fun a => act σ (twAct act χ i U τ x a))
  rw [hv, hστ, chiC_mul, hU.2.2.2.1 σ hσ τ hτ, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, smul_smul]

theorem tw_cont (ha : IsActC act) (hχ : IsCyc χ) (hU : Frame χ K m U g)
    (x : Fin r → PadicComplex l) : ContinuousOn (fun σ => twAct act χ i U σ x) (Gj K m) := by
  apply continuousOn_pi.2
  intro a
  have h1 : ∀ b, ContinuousOn (fun σ => U σ a b * act σ (x b)) (Gj K m) :=
    fun b => (hU.2.1 a b).mul (IsActC.continuous_orbit l act ha (x b)).continuousOn
  have h2 : ContinuousOn (fun σ => ∑ b, U σ a b * act σ (x b)) (Gj K m) :=
    continuousOn_finsetSum _ (fun b _ => h1 b)
  have h3 : ContinuousOn (fun σ => chiC χ i σ * ∑ b, U σ a b * act σ (x b)) (Gj K m) :=
    (continuous_chiC hχ i).continuousOn.mul h2
  refine h3.congr ?_
  intro σ _
  simp only [twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]

theorem modify (ha : IsActC act) (hχ : IsCyc χ) (hU : Frame χ K m U g) (n : ℕ)
    {c : GQ l → Fin r → PadicComplex l} (hc : CocOn (Gj K m) (twAct act χ i U) (ball l r) c)
    {x : Fin r → PadicComplex l} (hx : x ∈ ball l r) :
    CocOn (Gj K m) (twAct act χ i U) (ball l r)
      (fun σ => (l : PadicComplex l) ^ n • c σ - (twAct act χ i U σ x - x)) := by
  obtain ⟨hcont, hmem, hcoc⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ContinuousOn (fun σ => ((l : PadicComplex l) ^ n) • c σ) (Gj K m) :=
      (continuousOn_const (c := (l : PadicComplex l) ^ n)).smul hcont
    exact h1.sub ((tw_cont ha hχ hU x).sub continuousOn_const)
  · intro σ hσ
    exact ball_sub (ball_pow n (hmem σ hσ)) (ball_sub (tw_ball ha hχ hU hσ hx) hx)
  · intro σ hσ τ hτ
    simp only
    rw [hcoc σ hσ τ hτ, tw_mul ha hU hσ hτ, tw_sub, tw_sub, tw_pow, smul_add]
    abel

theorem torsion_killed : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → ∀ (i : ℤ) (c : GQ l → Fin r → PadicComplex l) (k : ℕ), CocOn (Gj K m) (twAct act χ i U) (ball l r) c → CobOn (Gj K m) (twAct act χ i U) (ball l r) (fun σ => (l : PadicComplex l) ^ k • c σ) → CobOn (Gj K m) (twAct act χ i U) (ball l r) (fun σ => (l : PadicComplex l) ^ (1 + max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i)))) • c σ) := by
  intro l hl act χ ha hχ K m r hm U g hU J hJ i c k hc hk
  set N : ℕ := max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i))) with hN
  have hHG : ∀ h ∈ Hinf K, h ∈ Gj K m := fun h hh => hinf_le_gj K m hh
  have hgG : g ∈ Gj K m := hU.1.1

  have hHc : CocOn (Hinf K) (fun h y a => act h (y a)) (ball l r) c := by
    refine ⟨hc.1.mono (fun h hh => hHG h hh), fun h hh => hc.2.1 h (hHG h hh), ?_⟩
    intro h hh h' hh'
    rw [hc.2.2 h (hHG h hh) h' (hHG h' hh'), tw_hinf hχ hU hh]

  have hlC : (l : PadicComplex l) ∈ inC (Kinf K) :=
    ⟨algebraMap ℚ_[l] (Om l) (l : ℚ_[l]), IntermediateField.algebraMap_mem _ _,
      (algebraMap_eq (l := l) (l : ℚ_[l])).symm.trans (map_natCast _ l)⟩
  obtain ⟨x1, hx1, hx1e⟩ := GlobalTheory.T.cyclotomic_tate_maximalIdeal_kills_first_cohomology l act ha K r (l : PadicComplex l) hlC norm_l_lt c hHc

  obtain ⟨c1, hc1def⟩ : ∃ c1 : GQ l → Fin r → PadicComplex l,
      c1 = fun σ => (l : PadicComplex l) ^ 1 • c σ - (twAct act χ i U σ x1 - x1) := ⟨_, rfl⟩
  have hc1 : CocOn (Gj K m) (twAct act χ i U) (ball l r) c1 := by
    rw [hc1def]
    exact modify ha hχ hU 1 hc hx1
  have hc1H : ∀ h ∈ Hinf K, c1 h = 0 := by
    intro h hh
    have e := hx1e h hh
    simp only at e
    simp only [hc1def, pow_one, e, tw_hinf hχ hU hh]
    exact sub_self _

  have hw : ∀ a, c1 g a ∈ Ohat K := by
    intro a
    refine (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K (c1 g a) (hc1.2.1 g hgG a)).1 ?_
    intro h hh
    have hh' : g⁻¹ * h * g ∈ Hinf K := conj_hinf hχ K m hgG hh
    have e1 : c1 (g * (g⁻¹ * h * g)) = c1 g := by
      rw [hc1.2.2 g hgG _ (hHG _ hh'), hc1H _ hh', tw_zero, add_zero]
    have e2 : c1 (g * (g⁻¹ * h * g)) = fun a => act h (c1 g a) := by
      have e3 : g * (g⁻¹ * h * g) = h * g := by group
      rw [e3, hc1.2.2 h (hHG h hh) g hgG, hc1H h hh, zero_add, tw_hinf hχ hU hh]
    exact congrFun (e2.symm.trans e1) a

  obtain ⟨x0, hx0, hx0e⟩ := hk
  obtain ⟨x2, hx2def⟩ : ∃ x2 : Fin r → PadicComplex l,
      x2 = (l : PadicComplex l) ^ 1 • x0 - (l : PadicComplex l) ^ k • x1 := ⟨_, rfl⟩
  have hx2b : x2 ∈ ball l r := by
    rw [hx2def]
    exact ball_sub (ball_pow 1 hx0) (ball_pow k hx1)
  have hcob1 : ∀ σ ∈ Gj K m, (l : PadicComplex l) ^ k • c1 σ = twAct act χ i U σ x2 - x2 := by
    intro σ hσ
    have e := hx0e σ hσ
    simp only at e
    simp only [hc1def, hx2def]
    rw [tw_sub, tw_pow, tw_pow, smul_sub, smul_sub, smul_comm ((l : PadicComplex l) ^ k) ((l : PadicComplex l) ^ 1) (c σ), e, smul_sub]
    abel
  have hx2O : ∀ a, x2 a ∈ Ohat K := by
    intro a
    refine (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K (x2 a) (hx2b a)).1 ?_
    intro h hh
    have e := hcob1 h (hHG h hh)
    rw [hc1H h hh, smul_zero, tw_hinf hχ hU hh] at e
    have e' := congrFun e a
    simp only [Pi.zero_apply, Pi.sub_apply] at e'
    exact sub_eq_zero.1 e'.symm

  obtain ⟨y, hyO, hye⟩ := GlobalTheory.T.torsion_coinvariants_twistedCyclotomicGenerator l act χ ha hχ K m r hm U g hU J hJ i (c1 g) x2 k hw hx2O
    (hcob1 g hgG).symm
  rw [← hN] at hye
  have hyb : y ∈ ball l r := fun a => ohat_norm K (hyO a)
  have hyfix : ∀ h ∈ Hinf K, twAct act χ i U h y = y := by
    intro h hh
    rw [tw_hinf hχ hU hh]
    funext a
    exact (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K (y a) (hyb a)).2 (hyO a) h hh

  obtain ⟨d, hddef⟩ : ∃ d : GQ l → Fin r → PadicComplex l,
      d = fun σ => (l : PadicComplex l) ^ N • c1 σ - (twAct act χ i U σ y - y) := ⟨_, rfl⟩
  have hd : CocOn (Gj K m) (twAct act χ i U) (ball l r) d := by
    rw [hddef]
    exact modify ha hχ hU N hc1 hyb
  have hdU : CocOn (Gj K m) (twAct act χ i U) Set.univ d := ⟨hd.1, fun _ _ => Set.mem_univ _, hd.2.2⟩
  have hdH : ∀ h ∈ Hinf K, d h = 0 := by
    intro h hh
    simp only [hddef, hc1H h hh, hyfix h hh, smul_zero, sub_self]
  have hdg : d g = 0 := by
    simp only [hddef]
    rw [hye, sub_self]
  have hd0 := (GlobalTheory.T.cocycle_vanishing_on_fixingSubgroup_determined_by_generator l act χ ha hχ K m r hm U g hU i).1 d hdU hdH hdg

  refine ⟨y + (l : PadicComplex l) ^ N • x1, ball_add hyb (ball_pow N hx1), ?_⟩
  intro σ hσ
  have e1 := hd0 σ hσ
  simp only [hddef, hc1def] at e1
  rw [smul_sub, smul_sub] at e1
  have e2 := sub_eq_zero.1 e1
  have key : (l : PadicComplex l) ^ N • (l : PadicComplex l) ^ 1 • c σ
      = (twAct act χ i U σ y - y)
        + ((l : PadicComplex l) ^ N • twAct act χ i U σ x1 - (l : PadicComplex l) ^ N • x1) := by
    rw [← e2]
    abel
  simp only
  rw [tw_add, tw_pow, pow_add, mul_smul, smul_comm ((l : PadicComplex l) ^ 1) ((l : PadicComplex l) ^ N) (c σ), key]
  abel

end GlobalTheory.Cyc.FrameTorsion

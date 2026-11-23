import Mathlib
import GroundTheory.PAdicHodge.FieldOfNormsRam
import GroundTheory.PAdicHodge.FieldOfNormsLocal
import GroundTheory.LocalFields.ExamplesCharZero
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology IntermediateField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]

section GaloisAPF

variable {L : IntermediateField K Ω} [IsGalois K L]

theorem fixingSubgroup_normal_of_isGalois : L.fixingSubgroup.Normal :=
  (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance

instance upperSupFixing_normal (u : ℝ) : (upperSupFixing K Ω L u).Normal := by
  haveI := fixingSubgroup_normal_of_isGalois (L := L)
  exact Subgroup.sup_normal _ _

variable (hL : IsAPF K Ω L)
include hL

theorem finiteDimensional_upperField' (u : ℝ) : FiniteDimensional K (upperField K Ω L u) :=
  finiteDimensional_upperField hL u

theorem isGalois_upperField (u : ℝ) : IsGalois K (upperField K Ω L u) := by
  rw [← InfiniteGalois.normal_iff_isGalois, fixingSubgroup_upperField hL]
  infer_instance

def upperFieldFG (u : ℝ) : FiniteGaloisIntermediateField K Ω :=
  @FiniteGaloisIntermediateField.mk K Ω _ _ _ (upperField K Ω L u) (finiteDimensional_upperField hL u)
    (isGalois_upperField hL u)

theorem upperFieldFG_coe (u : ℝ) : (upperFieldFG hL u : IntermediateField K Ω) = upperField K Ω L u :=
  rfl

theorem ker_restrictNormalHom_upperField (u : ℝ) :
    (AlgEquiv.restrictNormalHom (upperFieldFG hL u : IntermediateField K Ω)).ker =
      upperSupFixing K Ω L u := by
  rw [IntermediateField.restrictNormalHom_ker, upperFieldFG_coe, fixingSubgroup_upperField hL]

theorem upperRamificationGroup_upperField_eq_bot (u' : ℝ) :
    upperRamificationGroup K (upperFieldFG hL u' : IntermediateField K Ω) u' = ⊥ := by
  rw [← map_absUpper (upperFieldFG hL u') u', Subgroup.map_eq_bot_iff,
    ker_restrictNormalHom_upperField hL]
  exact absUpper_le_upperSupFixing u'

theorem upperIndex_upperField {u' w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ u') :
    upperIndex K (upperFieldFG hL u' : IntermediateField K Ω) w = apfIndex K Ω L w := by
  haveI := fixingSubgroup_normal_of_isGalois (L := L)
  rw [upperIndex, ← upperRamificationGroup_zero, ← map_absUpper (upperFieldFG hL u') w,
    ← map_absUpper (upperFieldFG hL u') 0, Subgroup.relIndex_map_map,
    ker_restrictNormalHom_upperField hL, apfIndex]
  have h1 : absUpper K Ω w ⊔ upperSupFixing K Ω L u' = upperSupFixing K Ω L w := by
    rw [upperSupFixing, upperSupFixing, ← sup_assoc,
      sup_eq_left.mpr (absUpper_antitone K Ω hw)]
  have h2 : absUpper K Ω 0 ⊔ upperSupFixing K Ω L u' = absUpper K Ω 0 ⊔ upperSupFixing K Ω L w := by
    rw [upperSupFixing, upperSupFixing, ← sup_assoc, ← sup_assoc,
      sup_eq_left.mpr (absUpper_antitone K Ω (hw0.trans hw)),
      sup_eq_left.mpr (absUpper_antitone K Ω hw0)]
  rw [h1, h2, Subgroup.relIndex_sup_right]

theorem ramificationIndex_upperField {u' : ℝ} (hu' : 0 ≤ u') :
    ramificationIndex K (upperFieldFG hL u' : IntermediateField K Ω) = apfIndex K Ω L u' := by
  rw [← upperIndex_upperField hL hu' le_rfl, upperIndex, upperRamificationGroup_upperField_eq_bot,
    Subgroup.relIndex_bot_left, card_lowerRamificationGroup_zero]

theorem herbrandPsi_upperField {u u' : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ u') :
    herbrandPsi K (upperFieldFG hL u' : IntermediateField K Ω) u = apfPsi K Ω L u := by
  rw [herbrandPsi_eq_integral hu0, apfPsi]
  refine intervalIntegral.integral_congr fun w hw ↦ ?_
  rw [Set.uIcc_of_le hu0] at hw
  simp only [upperIndex_upperField hL hw.1 (hw.2.trans hu)]

theorem exists_mem_upperField {x : Ω} (hx : x ∈ L) : ∃ u : ℝ, x ∈ upperField K Ω L u := by
  let M := FiniteGaloisIntermediateField.adjoin K ({x} : Set Ω)
  have hxM : x ∈ (M : IntermediateField K Ω) :=
    FiniteGaloisIntermediateField.subset_adjoin K ({x} : Set Ω) rfl
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot K (M : IntermediateField K Ω)
  refine ⟨herbrandPhi K (M : IntermediateField K Ω) N, ?_⟩
  rw [upperField, IntermediateField.mem_fixedField_iff]
  intro σ hσ

  let S : Subgroup Gal(Ω/K) := (IntermediateField.adjoin K ({x} : Set Ω)).fixingSubgroup
  have hS : ∀ τ ∈ S, τ x = x := fun τ hτ ↦
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ x (IntermediateField.subset_adjoin K _ rfl)
  have hup : absUpper K Ω (herbrandPhi K (M : IntermediateField K Ω) N) ≤ S := by
    intro τ hτ
    have h1 := hτ M
    rw [upperRamificationGroup_herbrandPhi, lowerRamificationGroupReal_natCast, hN N le_rfl,
      Subgroup.mem_bot] at h1
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hyM : y ∈ (M : IntermediateField K Ω) :=
      (IntermediateField.le_normalClosure _) hy
    have := congrArg (fun f ↦ ((f ⟨y, hyM⟩ : M) : Ω)) h1
    simpa [AlgEquiv.restrictNormalHom_apply] using this
  have hfix : L.fixingSubgroup ≤ S := by
    intro τ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hyL : y ∈ L := IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hx) hy
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ y hyL
  exact hS σ (sup_le hup hfix hσ)

end GaloisAPF

section Tower

variable {L : IntermediateField K Ω} [IsGalois K L] (hL : IsAPF K Ω L)
include hL

theorem map_upperSupFixing {u u' : ℝ} :
    (upperSupFixing K Ω L u).map
        (AlgEquiv.restrictNormalHom (upperFieldFG hL u' : IntermediateField K Ω)) =
      upperRamificationGroup K (upperFieldFG hL u' : IntermediateField K Ω) u := by
  rw [upperSupFixing, Subgroup.map_sup, map_absUpper]
  have : L.fixingSubgroup.map
      (AlgEquiv.restrictNormalHom (upperFieldFG hL u' : IntermediateField K Ω)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, ker_restrictNormalHom_upperField hL]
    exact fixingSubgroup_le_upperSupFixing u'
  rw [this, sup_bot_eq]

theorem apfPsi_le_add {u u' : ℝ} (h : u ≤ u') :
    apfPsi K Ω L u' ≤ apfPsi K Ω L u + (u' - u) * apfIndex K Ω L u' := by
  rw [apfPsi, apfPsi, ← intervalIntegral.integral_add_adjacent_intervals (b := u)
    (intervalIntegrable_apfIndex hL _ _) (intervalIntegrable_apfIndex hL _ _)]
  gcongr
  calc ∫ w in u..u', (apfIndex K Ω L w : ℝ) ≤ ∫ _ in u..u', (apfIndex K Ω L u' : ℝ) :=
        intervalIntegral.integral_mono_on h (intervalIntegrable_apfIndex hL _ _)
          intervalIntegrable_const fun w hw ↦ by exact_mod_cast apfIndex_mono hL hw.2
    _ = (u' - u) * apfIndex K Ω L u' := by simp

end Tower

section Construction

variable {L : IntermediateField K Ω} [IsGalois K L]

structure APFData (L : IntermediateField K Ω) where
  apf : IsAPF K Ω L
  c : ℝ
  c_pos : 0 < c
  u₀ : ℝ
  one_le_u₀ : 1 ≤ u₀
  le_psi : ∀ u, u₀ ≤ u → c * apfIndex K Ω L u ≤ apfPsi K Ω L u

theorem IsStrictlyAPF.nonempty_apfData (h : IsStrictlyAPF K Ω L) : Nonempty (APFData L) := by
  obtain ⟨hapf, c, hc, hev⟩ := h
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.mp hev
  exact ⟨⟨hapf, c, hc, max U 1, le_max_right _ _, fun u hu ↦ hU u ((le_max_left _ _).trans hu)⟩⟩

namespace APFData

variable (d : APFData L)

def u (n : ℕ) : ℝ := d.u₀ + n * (d.c / 2)

theorem u_succ (n : ℕ) : d.u (n + 1) = d.u n + d.c / 2 := by
  simp only [u]; push_cast; ring

theorem one_le_u (n : ℕ) : 1 ≤ d.u n := by
  have := d.one_le_u₀
  have : 0 ≤ (n : ℝ) * (d.c / 2) := mul_nonneg n.cast_nonneg (by linarith [d.c_pos])
  simp only [u]; linarith

theorem u_nonneg (n : ℕ) : 0 ≤ d.u n := zero_le_one.trans (d.one_le_u n)

theorem u_mono : Monotone d.u := by
  intro m n h
  simp only [u]
  have : (m : ℝ) ≤ n := by exact_mod_cast h
  nlinarith [d.c_pos]

theorem exists_le_u (v : ℝ) : ∃ n, v ≤ d.u n := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((v - d.u₀) / (d.c / 2))
  refine ⟨n, ?_⟩
  have hc : 0 < d.c / 2 := by linarith [d.c_pos]
  rw [div_lt_iff₀ hc] at hn
  simp only [u]; linarith

def F (n : ℕ) : FiniteGaloisIntermediateField K Ω := upperFieldFG d.apf (d.u n)

def H (n : ℕ) : Subgroup Gal((d.F (n + 1) : IntermediateField K Ω)/K) :=
  upperRamificationGroup K (d.F (n + 1) : IntermediateField K Ω) (d.u n)

theorem exists_lift (n : ℕ) (g : d.H n) :
    ∃ σ ∈ absUpper K Ω (d.u n),
      AlgEquiv.restrictNormalHom (d.F (n + 1) : IntermediateField K Ω) σ = g := by
  have : (g : Gal((d.F (n + 1) : IntermediateField K Ω)/K)) ∈
      upperRamificationGroup K (d.F (n + 1) : IntermediateField K Ω) (d.u n) := g.2
  rw [← map_absUpper (d.F (n + 1)) (d.u n)] at this
  exact this

def lift (n : ℕ) (g : d.H n) : Gal(Ω/K) := (d.exists_lift n g).choose

theorem lift_mem (n : ℕ) (g : d.H n) : d.lift n g ∈ absUpper K Ω (d.u n) :=
  (d.exists_lift n g).choose_spec.1

theorem restrict_lift (n : ℕ) (g : d.H n) :
    AlgEquiv.restrictNormalHom (d.F (n + 1) : IntermediateField K Ω) (d.lift n g) = g :=
  (d.exists_lift n g).choose_spec.2

theorem lift_injective (n : ℕ) : Function.Injective (d.lift n) := by
  intro g g' h
  have := congrArg (AlgEquiv.restrictNormalHom (d.F (n + 1) : IntermediateField K Ω)) h
  rw [restrict_lift, restrict_lift] at this
  exact Subtype.ext this

instance (n : ℕ) : Fintype (d.H n) := Fintype.ofFinite _

open Classical in

def T (n : ℕ) : Finset Gal(Ω/K) := Finset.univ.image (d.lift n)

theorem card_alt (n : ℕ) : (d.T n).card = Nat.card (d.H n) := by
  classical
  rw [T, Finset.card_image_of_injective _ (d.lift_injective n), Finset.card_univ,
    Nat.card_eq_fintype_card]

theorem lift_apply (n : ℕ) (g : d.H n) {y : Ω} (hy : y ∈ (d.F (n + 1) : IntermediateField K Ω)) :
    d.lift n g y = ((g : Gal((d.F (n + 1) : IntermediateField K Ω)/K)) ⟨y, hy⟩ : Ω) := by
  rw [← d.restrict_lift n g, AlgEquiv.restrictNormalHom_apply]

theorem psi_ge (n : ℕ) : d.c / 2 * apfIndex K Ω L (d.u (n + 1)) ≤ apfPsi K Ω L (d.u n) := by
  have h1 := d.le_psi (d.u (n + 1)) (by simp only [u]; have := d.c_pos; push_cast; nlinarith)
  have h2 := apfPsi_le_add d.apf (d.u_mono (Nat.le_succ n))
  rw [d.u_succ] at h1 h2 ⊢
  have : d.u n + d.c / 2 - d.u n = d.c / 2 := by ring
  rw [this] at h2
  linarith

end APFData

end Construction

omit [IsGalois K Ω] in
theorem exists_nrm_eq_unifNrm_zpow (F : IntermediateField K Ω) [FiniteDimensional K F] {y : Ω}
    (hy : y ∈ F) (hy0 : y ≠ 0) : ∃ j : ℤ, nrm K y = unifNrm F ^ j := by
  obtain ⟨z, rfl⟩ : ∃ z : F, (z : Ω) = y := ⟨⟨y, hy⟩, rfl⟩
  have hz : z ≠ 0 := by
    rintro rfl; exact hy0 (ZeroMemClass.coe_zero _)
  exact ⟨_, nrm_eq_unifNrm_zpow F hz⟩

omit [IsGalois K Ω] in
theorem exists_nrm_eq_unifNrm (F : IntermediateField K Ω) [FiniteDimensional K F] :
    ∃ π ∈ F, nrm K π = unifNrm F :=
  ⟨_, SetLike.coe_mem ((unif F : 𝒪[F]) : F), rfl⟩

namespace APFData

variable {L : IntermediateField K Ω} [IsGalois K L] (d : APFData L)

theorem psi_pos (n : ℕ) : 0 < apfPsi K Ω L (d.u n) := by
  have h := d.psi_ge n
  have hI : (0 : ℝ) < apfIndex K Ω L (d.u (n + 1)) := by exact_mod_cast apfIndex_pos d.apf _
  have hc : 0 < d.c / 2 := by linarith [d.c_pos]
  nlinarith

theorem herbrandPsi_F (n : ℕ) :
    herbrandPsi K (d.F (n + 1) : IntermediateField K Ω) (d.u n) = apfPsi K Ω L (d.u n) :=
  herbrandPsi_upperField d.apf (d.u_nonneg n) (d.u_mono (Nat.le_succ n))

def i (n : ℕ) : ℕ := (⌈apfPsi K Ω L (d.u n)⌉).toNat

theorem i_cast (n : ℕ) : ((d.i n : ℕ) : ℤ) = ⌈apfPsi K Ω L (d.u n)⌉ :=
  Int.toNat_of_nonneg (Int.ceil_nonneg (d.psi_pos n).le)

theorem H_eq (n : ℕ) : d.H n = lowerRamificationGroup K (d.F (n + 1) : IntermediateField K Ω) (d.i n) := by
  rw [H, upperRamificationGroup, lowerRamificationGroupReal, d.herbrandPsi_F, d.i_cast]

theorem one_le_i (n : ℕ) : 1 ≤ d.i n := by
  have h := d.i_cast n
  have : (1 : ℤ) ≤ ⌈apfPsi K Ω L (d.u n)⌉ := Int.one_le_ceil_iff.mpr (d.psi_pos n)
  omega

theorem isPGroup_H (n : ℕ) : IsPGroup (ringChar 𝓀[K]) (d.H n) := by
  refine (isPGroup_lowerRamificationGroup_one K (d.F (n + 1) : IntermediateField K Ω)).to_le ?_
  rw [d.H_eq]
  exact lowerRamificationGroup_antitone K _ (by exact_mod_cast d.one_le_i n)

instance fact_prime : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.char_is_prime 𝓀[K] _⟩

theorem exists_card_H (n : ℕ) : ∃ k : ℕ, Nat.card (d.H n) = ringChar 𝓀[K] ^ k :=
  IsPGroup.iff_card.mp (d.isPGroup_H n)

def k (n : ℕ) : ℕ := (d.exists_card_H n).choose

theorem card_H (n : ℕ) : Nat.card (d.H n) = ringChar 𝓀[K] ^ d.k n :=
  (d.exists_card_H n).choose_spec

theorem restrict_mem_H (n : ℕ) {τ : Gal(Ω/K)} (hτ : τ ∈ upperSupFixing K Ω L (d.u n)) :
    AlgEquiv.restrictNormalHom (d.F (n + 1) : IntermediateField K Ω) τ ∈ d.H n := by
  show _ ∈ upperRamificationGroup K (upperFieldFG d.apf (d.u (n + 1)) : IntermediateField K Ω) (d.u n)
  rw [← map_upperSupFixing d.apf]
  exact Subgroup.mem_map_of_mem _ hτ

theorem prod_mem (n : ℕ) {y : Ω} (hy : y ∈ (d.F (n + 1) : IntermediateField K Ω)) :
    (∏ σ ∈ d.T n, σ y) ∈ (d.F n : IntermediateField K Ω) := by
  classical
  have e : (∏ σ ∈ d.T n, σ y) =
      ∏ g : d.H n, ((g : Gal((d.F (n + 1) : IntermediateField K Ω)/K)) ⟨y, hy⟩ : Ω) := by
    rw [T, Finset.prod_image (fun g _ g' _ h ↦ d.lift_injective n h)]
    exact Finset.prod_congr rfl fun g _ ↦ d.lift_apply n g hy
  rw [e]
  show _ ∈ upperField K Ω L (d.u n)
  rw [upperField, IntermediateField.mem_fixedField_iff]
  intro τ hτ
  rw [map_prod]
  let h : d.H n := ⟨_, d.restrict_mem_H n hτ⟩
  have hτg : ∀ g : d.H n, τ ((g : Gal((d.F (n + 1) : IntermediateField K Ω)/K)) ⟨y, hy⟩ : Ω) =
      (((h * g : d.H n) : Gal((d.F (n + 1) : IntermediateField K Ω)/K)) ⟨y, hy⟩ : Ω) := by
    intro g
    rw [Subgroup.coe_mul, AlgEquiv.mul_apply, ← AlgEquiv.restrictNormalHom_apply]
  simp_rw [hτg]
  exact Fintype.prod_equiv (Equiv.mulLeft h) _ _ fun g ↦ rfl

theorem step (n : ℕ) {σ : Gal(Ω/K)} (hσ : σ ∈ d.T n) {x : Ω}
    (hx : x ∈ (d.F (n + 1) : IntermediateField K Ω)) :
    nrm K (σ x - x) ≤ baseUnifNrm K Ω ^ (d.c / 2) * nrm K x := by
  classical
  simp only [T, Finset.mem_image, Finset.mem_univ, true_and] at hσ
  obtain ⟨g, rfl⟩ := hσ
  set F := (d.F (n + 1) : IntermediateField K Ω)
  have hg : AlgEquiv.restrictNormalHom F (d.lift n g) ∈ lowerRamificationGroup K F (d.i n) := by
    rw [d.restrict_lift, ← d.H_eq]; exact g.2
  have h1 := nrm_sub_le_of_mem_lowerRamificationGroup F hg ⟨x, hx⟩
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (nrm_nonneg _))

  set r := unifNrm F
  set e := ramificationIndex K F
  have hr0 := unifNrm_pos F
  have hr1 := unifNrm_lt_one F
  have hre : r ^ e = baseUnifNrm K Ω := unifNrm_pow_ramificationIndex F
  have he : (e : ℝ) = apfIndex K Ω L (d.u (n + 1)) := by
    exact_mod_cast ramificationIndex_upperField d.apf (d.u_nonneg (n + 1))
  have hi : d.c / 2 * e ≤ d.i n := by
    rw [he]
    refine (d.psi_ge n).trans ?_
    have := d.i_cast n
    have h2 : apfPsi K Ω L (d.u n) ≤ (⌈apfPsi K Ω L (d.u n)⌉ : ℝ) := Int.le_ceil _
    rw [← this] at h2
    exact_mod_cast h2
  rw [← hre, ← Real.rpow_natCast r e, ← Real.rpow_mul hr0.le, ← Real.rpow_natCast r (d.i n)]
  exact Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le (by linarith)

theorem value_succ (n : ℕ) :
    unifNrm (d.F (n + 1) : IntermediateField K Ω) ^ (ringChar 𝓀[K] ^ d.k n) =
      unifNrm (d.F n : IntermediateField K Ω) := by
  set F := (d.F (n + 1) : IntermediateField K Ω)
  have he1 : ramificationIndex K F = apfIndex K Ω L (d.u (n + 1)) :=
    ramificationIndex_upperField d.apf (d.u_nonneg (n + 1))
  have he0 : ramificationIndex K (d.F n : IntermediateField K Ω) = apfIndex K Ω L (d.u n) :=
    ramificationIndex_upperField d.apf (d.u_nonneg n)
  have hidx : upperIndex K F (d.u n) = apfIndex K Ω L (d.u n) :=
    upperIndex_upperField d.apf (d.u_nonneg n) (d.u_mono (Nat.le_succ n))

  have hmul : ramificationIndex K F = ramificationIndex K (d.F n : IntermediateField K Ω) *
      Nat.card (d.H n) := by
    rw [he0, ← hidx, ← card_lowerRamificationGroup_zero, upperIndex]
    have hle : d.H n ≤ lowerRamificationGroup K F 0 := by
      rw [← upperRamificationGroup_zero]
      exact upperRamificationGroup_antitone K F (d.u_nonneg n)
    have := relIndex_mul_card_inf (d.H n) (lowerRamificationGroup K F 0)
    rw [inf_eq_left.mpr hle] at this
    exact this.symm
  have h1 := unifNrm_pow_ramificationIndex F
  have h0 := unifNrm_pow_ramificationIndex (d.F n : IntermediateField K Ω)
  rw [hmul, mul_comm, pow_mul, ← h0, d.card_H] at h1
  have hpos : ramificationIndex K (d.F n : IntermediateField K Ω) ≠ 0 :=
    (ramificationIndex_pos K _).ne'
  exact (pow_left_inj₀ (pow_nonneg (unifNrm_pos F).le _) (unifNrm_pos _).le hpos).mp h1

theorem F_succ_le_of_k_eq_zero {m : ℕ} (hk : d.k m = 0) :
    (d.F (m + 1) : IntermediateField K Ω) ≤ d.F m := by
  have hH : d.H m = ⊥ := by
    rw [← Subgroup.card_eq_one, d.card_H, hk, pow_zero]
  intro x hx
  show x ∈ upperField K Ω L (d.u m)
  rw [upperField, IntermediateField.mem_fixedField_iff]
  intro τ hτ
  have h := d.restrict_mem_H m hτ
  rw [hH, Subgroup.mem_bot] at h
  have := congrArg (fun f ↦ ((f ⟨x, hx⟩ : (d.F (m + 1) : IntermediateField K Ω)) : Ω)) h
  simpa [AlgEquiv.restrictNormalHom_apply] using this

theorem le_F_of_mem (n : ℕ) : (d.F n : IntermediateField K Ω) ≤ L := upperField_le _

theorem frequently_ne_zero (hinf : ¬ FiniteDimensional K L) (n : ℕ) : ∃ m, n ≤ m ∧ d.k m ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hstab : ∀ j, (d.F (n + j) : IntermediateField K Ω) ≤ d.F n := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact (d.F_succ_le_of_k_eq_zero (hcon (n + j) (by omega))).trans ih
  have hL : L ≤ d.F n := by
    intro x hx
    obtain ⟨v, hv⟩ := exists_mem_upperField d.apf hx
    obtain ⟨m, hm⟩ := d.exists_le_u v
    have : x ∈ (d.F (n + m) : IntermediateField K Ω) :=
      upperField_mono (hm.trans (d.u_mono (by omega))) hv
    exact hstab m this
  exact hinf (FiniteDimensional.of_injective (IntermediateField.inclusion hL).toLinearMap
    (IntermediateField.inclusion_injective hL))

omit [IsGalois K Ω] in
theorem nrm_ringChar_lt_one : nrm K ((ringChar 𝓀[K] : ℕ) : Ω) < 1 := by
  have h := CharZero.valuation_p_lt_one K (ringChar 𝓀[K])
  rw [nrm_lt_one_iff, ← map_natCast (algebraMap K Ω)]
  exact (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation Ω) _).mpr h

theorem value_zpow (n : ℕ) {y : Ω} (hy : y ∈ (d.F n : IntermediateField K Ω)) (hy0 : y ≠ 0) :
    ∃ j : ℤ, nrm K y = unifNrm (d.F n : IntermediateField K Ω) ^ j :=
  exists_nrm_eq_unifNrm_zpow _ hy hy0

theorem exists_value (n : ℕ) : ∃ π ∈ (d.F n : IntermediateField K Ω),
    nrm K π = unifNrm (d.F n : IntermediateField K Ω) :=
  exists_nrm_eq_unifNrm _

def tower (hinf : ¬ FiniteDimensional K L) : NormTower K Ω (ringChar 𝓀[K]) where
  E n := (d.F n : IntermediateField K Ω)
  mono _ _ h := upperField_mono (d.u_mono h)
  finiteDimensional _ := inferInstance
  T := d.T
  fix n σ hσ x hx := by
    classical
    simp only [T, Finset.mem_image, Finset.mem_univ, true_and] at hσ
    obtain ⟨g, rfl⟩ := hσ
    have h1 : d.lift n g ∈ (upperField K Ω L (d.u n)).fixingSubgroup := by
      rw [fixingSubgroup_upperField d.apf]
      exact absUpper_le_upperSupFixing _ (d.lift_mem n g)
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp h1 x hx
  prod_mem n y hy := d.prod_mem n hy
  k := d.k
  card_alt n := (d.card_alt n).trans (d.card_H n)
  frequently_ne_zero := d.frequently_ne_zero hinf
  c := baseUnifNrm K Ω ^ (d.c / 2)
  c_nonneg := Real.rpow_nonneg baseUnifNrm_pos.le _
  c_lt_one := by
    refine Real.rpow_lt_one baseUnifNrm_pos.le ?_ (by linarith [d.c_pos])
    rw [← unifNrm_pow_ramificationIndex (d.F 0 : IntermediateField K Ω)]
    exact pow_lt_one₀ (unifNrm_pos _).le (unifNrm_lt_one _) (ramificationIndex_pos K _).ne'
  step n σ hσ x hx := d.step n hσ hx
  prime := Fact.out
  nrm_p_lt_one := nrm_ringChar_lt_one
  value n := unifNrm (d.F n : IntermediateField K Ω)
  value_pos n := unifNrm_pos _
  value_lt_one n := unifNrm_lt_one _
  exists_value n := d.exists_value n
  value_zpow n y hy hy0 := d.value_zpow n hy hy0
  value_succ n := d.value_succ n

end APFData

end GroundTheory.PAdicHodge

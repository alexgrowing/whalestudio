import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
import GroundTheory.LocalFields.LocalZetaGauss
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GaussLam.TestFn

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def coset (V : Set Fˣ) (a : Fˣ) : Set Fˣ := (fun u => a⁻¹ * u) ⁻¹' V

def ind (V : Set Fˣ) (a : Fˣ) : F → ℂ := (Units.val '' coset V a).indicator fun _ => 1

theorem isOpen_coset {V : Set Fˣ} (hV : IsOpen V) (a : Fˣ) : IsOpen (coset V a) :=
  hV.preimage (continuous_const.mul continuous_id)

theorem isCompact_coset {V : Set Fˣ} (hV : IsCompact V) (a : Fˣ) : IsCompact (coset V a) := by
  have : coset V a = (fun u => a * u) '' V := by
    ext u
    constructor
    · intro h
      exact ⟨a⁻¹ * u, h, by simp⟩
    · rintro ⟨v, hv, rfl⟩
      simpa [coset] using hv
  rw [this]
  exact hV.image (continuous_const.mul continuous_id)

theorem ind_mem {V : Set Fˣ} (ho : IsOpen V) (hc : IsCompact V) (a : Fˣ) :
    ind V a ∈ schwartzBruhat F := by
  have hO : IsOpen (Units.val '' coset V a) :=
    isOpenEmbedding_units_val.isOpenMap _ (isOpen_coset ho a)
  have hK : IsCompact (Units.val '' coset V a) :=
    (isCompact_coset hc a).image Units.continuous_val
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, ?_⟩
  · by_cases hx : x ∈ Units.val '' coset V a
    · exact ⟨_, hO, hx, fun y hy => by
        simp only [ind, Set.indicator_of_mem hx, Set.indicator_of_mem hy]⟩
    · exact ⟨_, hK.isClosed.isOpen_compl, hx, fun y hy => by
        simp only [ind, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]⟩
  exact HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _

theorem ind_zero (V : Set Fˣ) (a : Fˣ) : ind V a 0 = 0 := by
  refine Set.indicator_of_notMem ?_ _
  rintro ⟨u, -, hu⟩
  exact u.ne_zero hu

theorem ind_unit_of_mem {V : Set Fˣ} {a u : Fˣ} (hu : u ∈ coset V a) : ind V a (u : F) = 1 :=
  Set.indicator_of_mem (Set.mem_image_of_mem _ hu) _

theorem ind_unit_of_notMem {V : Set Fˣ} {a u : Fˣ} (hu : u ∉ coset V a) : ind V a (u : F) = 0 := by
  refine Set.indicator_of_notMem ?_ _
  rintro ⟨v, hv, hvu⟩
  exact hu (Units.ext hvu ▸ hv)

theorem integrand_ind {V : Subgroup Fˣ} (hV0 : V ≤ unitFiltrationUnits F 0) {χ : Fˣ →* ℂˣ}
    (hVχ : V ≤ χ.ker) (a : Fˣ) (s : ℂ) (u : Fˣ) :
    ind (V : Set Fˣ) a u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : F) : ℝ) : ℂ) ^ s =
      (coset (V : Set Fˣ) a).indicator
        (fun _ => ((χ a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ s) u := by
  by_cases hu : u ∈ coset (V : Set Fˣ) a
  · rw [ind_unit_of_mem hu, Set.indicator_of_mem hu, one_mul]
    have hw : a⁻¹ * u ∈ V := hu
    have e : u = a * (a⁻¹ * u) := by simp
    have hχ : χ u = χ a := by
      conv_lhs => rw [e]
      rw [map_mul, MonoidHom.mem_ker.mp (hVχ hw), mul_one]
    have hm1 : modulus (((a⁻¹ * u : Fˣ)) : F) = 1 :=
      modulus_eq_one_iff.2 ⟨Units.ne_zero _, mem_unitFiltrationUnits_zero_iff_ord.1 (hV0 hw)⟩
    have hm : modulus (u : F) = modulus (a : F) := by
      conv_lhs => rw [e, Units.val_mul, modulus_mul, hm1, mul_one]
    rw [hχ, hm]
  · rw [ind_unit_of_notMem hu, Set.indicator_of_notMem hu, zero_mul, zero_mul]

variable [MeasurableSpace F] [BorelSpace F]

theorem measure_coset (V : Set Fˣ) (a : Fˣ) : multHaar F (coset V a) = multHaar F V :=
  measure_preimage_mul (multHaar F) a⁻¹ V

theorem integrable_coset {V : Subgroup Fˣ} (ho : IsOpen (V : Set Fˣ)) (hc : IsCompact (V : Set Fˣ))
    (a : Fˣ) (c : ℂ) :
    Integrable ((coset (V : Set Fˣ) a).indicator fun _ => c) (multHaar F) := by
  refine (integrable_indicator_iff (isOpen_coset ho a).measurableSet).2 ?_
  exact integrableOn_const (isCompact_coset hc a).measure_lt_top.ne

theorem integral_coset {V : Subgroup Fˣ} (ho : IsOpen (V : Set Fˣ)) (a : Fˣ) (c : ℂ) :
    ∫ u, (coset (V : Set Fˣ) a).indicator (fun _ => c) u ∂multHaar F =
      ((multHaar F).real (V : Set Fˣ) : ℂ) * c := by
  rw [integral_indicator_const c (isOpen_coset ho a).measurableSet, measureReal_def,
    measureReal_def, measure_coset]
  simp

theorem zeta_test {V : Subgroup Fˣ} (ho : IsOpen (V : Set Fˣ)) (hc : IsCompact (V : Set Fˣ))
    (hV0 : V ≤ unitFiltrationUnits F 0) {χ : Fˣ →* ℂˣ} (hVχ : V ≤ χ.ker) (t : Fˣ) :
    localZeta (fun x => ind (V : Set Fˣ) 1 x -
        ((modulus (t : F) : ℝ) : ℂ) ^ (-(1 / 2) : ℂ) * ind (V : Set Fˣ) t x) χ (1 / 2) =
      ((multHaar F).real (V : Set Fˣ) : ℂ) * (1 - ((χ t : ℂˣ) : ℂ)) := by
  have hm0 : ((modulus (t : F) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (modulus_ne_zero t.ne_zero)
  have hcc : ((modulus (t : F) : ℝ) : ℂ) ^ (-(1 / 2) : ℂ) * ((modulus (t : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ)
      = 1 := by
    rw [← Complex.cpow_add _ _ hm0, neg_add_cancel, Complex.cpow_zero]
  set c := ((modulus (t : F) : ℝ) : ℂ) ^ (-(1 / 2) : ℂ) with hc_def
  have e : ∀ u : Fˣ, (ind (V : Set Fˣ) 1 u - c * ind (V : Set Fˣ) t u) * ((χ u : ℂˣ) : ℂ) *
        ((modulus (u : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      (coset (V : Set Fˣ) 1).indicator (fun _ => (1 : ℂ)) u -
        (coset (V : Set Fˣ) t).indicator (fun _ => ((χ t : ℂˣ) : ℂ)) u := by
    intro u
    have h1 := integrand_ind hV0 hVχ 1 (1 / 2) u
    have h2 := integrand_ind hV0 hVχ t (1 / 2) u
    have e1 : (fun _ : Fˣ => (((χ 1 : ℂˣ) : ℂ)) * ((modulus ((1 : Fˣ) : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ))
        = fun _ => (1 : ℂ) := by
      funext _
      simp
    rw [e1] at h1
    have e2 : c * (coset (V : Set Fˣ) t).indicator
        (fun _ => ((χ t : ℂˣ) : ℂ) * ((modulus (t : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) u =
        (coset (V : Set Fˣ) t).indicator (fun _ => ((χ t : ℂˣ) : ℂ)) u := by
      by_cases hu : u ∈ coset (V : Set Fˣ) t
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, mul_left_comm, hcc, mul_one]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, mul_zero]
    rw [← e2, ← h1, ← h2]
    ring
  rw [localZeta]
  simp only [e]
  rw [integral_sub (integrable_coset ho hc 1 1) (integrable_coset ho hc t _),
    integral_coset ho 1, integral_coset ho t]
  ring

end GlobalTheory.CompanionTheory.GaussLam.TestFn

open GlobalTheory.CompanionTheory.GaussLam.TestFn in

theorem GlobalTheory.CompanionTheory.GaussLam.TestFn.exists_test : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (η : Fˣ →* ℂˣ), Continuous η → ∀ t : Fˣ, η t = -1 → ∃ g : F → ℂ, g ∈ schwartzBruhat F ∧ g 0 = 0 ∧ localZeta g 1 (1 / 2) = 0 ∧ localZeta g η (1 / 2) ≠ 0 := by
  intro F _ _ _ _ _ _ η hη t ht
  obtain ⟨n, hn⟩ := exists_unitFiltrationUnits_le_ker hη
  have ho := isOpen_unitFiltrationUnits (K := F) n
  have hc := isCompact_unitFiltrationUnits (K := F) n
  have hV0 : unitFiltrationUnits F n ≤ unitFiltrationUnits F 0 :=
    unitFiltrationUnits_antitone (Nat.zero_le n)
  have hvol : (multHaar F).real (unitFiltrationUnits F n : Set Fˣ) ≠ 0 := by
    rw [measureReal_def]
    refine ENNReal.toReal_ne_zero.mpr ⟨?_, hc.measure_lt_top.ne⟩
    exact (ho.measure_pos _ ⟨1, one_mem _⟩).ne'
  refine ⟨_, ?_, ?_, (zeta_test ho hc hV0 (χ := 1) (fun _ _ => rfl) t).trans ?_,
    (zeta_test ho hc hV0 hn t).trans_ne ?_⟩
  · exact Submodule.sub_mem _ (ind_mem ho hc 1)
      (Submodule.smul_mem _ (((modulus (t : F) : ℝ) : ℂ) ^ (-(1 / 2) : ℂ)) (ind_mem ho hc t))
  · simp [ind_zero]
  · simp
  · rw [ht]
    have : ((multHaar F).real (unitFiltrationUnits F n : Set Fˣ) : ℂ) ≠ 0 := by
      exact_mod_cast hvol
    simp only [Units.val_neg, Units.val_one, sub_neg_eq_add]
    exact mul_ne_zero this (by norm_num)

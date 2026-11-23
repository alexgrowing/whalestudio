import Mathlib
import GroundTheory.LocalFields.CompleteTrivial
import GroundTheory.LocalFields.NormalLattice

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Finset

section Action

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [ValuativeRel L]

abbrev unitVal (u : 𝒪[L]ˣ) : L := ((u : 𝒪[L]) : L)

theorem unitVal_injective : Function.Injective (unitVal (L := L)) :=
  fun _ _ h => Units.ext (Subtype.ext h)

variable (V : Subgroup 𝒪[L]ˣ)
  (hV : ∀ σ : Gal(L/K), ∀ u ∈ V, ∃ w ∈ V, unitVal w = σ (unitVal u))

def stableSMul (σ : Gal(L/K)) (u : V) : V :=
  ⟨(hV σ u u.2).choose, (hV σ u u.2).choose_spec.1⟩

theorem unitVal_stableSMul (σ : Gal(L/K)) (u : V) :
    unitVal (stableSMul V hV σ u : 𝒪[L]ˣ) = σ (unitVal u) :=
  (hV σ u u.2).choose_spec.2

@[instance_reducible]
def stableUnitsAction : MulDistribMulAction Gal(L/K) V where
  smul := stableSMul V hV
  one_smul u := Subtype.ext (unitVal_injective (by
    show unitVal (stableSMul V hV 1 u : 𝒪[L]ˣ) = unitVal u
    rw [unitVal_stableSMul, AlgEquiv.one_apply]))
  mul_smul σ τ u := Subtype.ext (unitVal_injective (by
    show unitVal (stableSMul V hV (σ * τ) u : 𝒪[L]ˣ) =
      unitVal (stableSMul V hV σ (stableSMul V hV τ u) : 𝒪[L]ˣ)
    rw [unitVal_stableSMul, unitVal_stableSMul, unitVal_stableSMul, AlgEquiv.mul_apply]))
  smul_mul σ u w := Subtype.ext (unitVal_injective (by
    show unitVal (stableSMul V hV σ (u * w) : 𝒪[L]ˣ) =
      unitVal ((stableSMul V hV σ u * stableSMul V hV σ w : V) : 𝒪[L]ˣ)
    rw [unitVal_stableSMul]
    simp only [unitVal, Subgroup.coe_mul, Units.val_mul, Subring.coe_mul] at *
    rw [map_mul]
    exact congrArg₂ (· * ·) ((hV σ u u.2).choose_spec.2).symm ((hV σ w w.2).choose_spec.2).symm))
  smul_one σ := Subtype.ext (unitVal_injective (by
    show unitVal (stableSMul V hV σ 1 : 𝒪[L]ˣ) = unitVal ((1 : V) : 𝒪[L]ˣ)
    rw [unitVal_stableSMul]
    simp [unitVal]))

theorem unitVal_smul (σ : Gal(L/K)) (u : V) :
    letI := stableUnitsAction V hV
    unitVal ((σ • u : V) : 𝒪[L]ˣ) = σ (unitVal u) :=
  (hV σ u u.2).choose_spec.2

end Action

section Data

variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
  [FiniteDimensional K L]

structure NormalLatticeData where

  π : 𝒪[K]
  irreducible : Irreducible π

  θ : L
  linearIndependent : LinearIndependent K fun σ : Gal(L/K) => σ θ
  integer : ∀ σ : Gal(L/K), σ θ ∈ 𝒪[L]

  r : ℕ
  mul_mem : ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0

namespace NormalLatticeData

variable {K L} (D : NormalLatticeData K L)

abbrev lat (s : ℕ) : Submodule 𝒪[K] L := normalLattice D.π D.θ s

abbrev k : ℕ := D.r + 1

omit [FiniteDimensional K L] in
theorem lat_antitone {s t : ℕ} (h : s ≤ t) : D.lat t ≤ D.lat s := normalLattice_antitone _ _ h

theorem mul_mem_lat {s t : ℕ} (hs : D.k ≤ s) {x y : L} (hx : x ∈ D.lat s) (hy : y ∈ D.lat t) :
    x * y ∈ D.lat (t + 1) :=
  mul_mem_normalLattice_succ D.π D.θ D.mul_mem (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hs) hx hy

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension K L]

theorem exists_unit {s : ℕ} (hs : D.k ≤ s) {x : L} (hx : x ∈ D.lat s) :
    ∃ u : 𝒪[L]ˣ, unitVal u = 1 + x ∧ unitVal u⁻¹ - 1 ∈ D.lat s :=
  exists_unit_one_add D.irreducible D.linearIndependent D.integer D.mul_mem
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hs) hx

def units (j : ℕ) : Subgroup 𝒪[L]ˣ where
  carrier := {u | unitVal u - 1 ∈ D.lat (D.k + j)}
  one_mem' := by
    show unitVal (1 : 𝒪[L]ˣ) - 1 ∈ D.lat (D.k + j)
    simp [unitVal]
  mul_mem' {u w} hu hw := by
    have e : unitVal (u * w) - 1 = (unitVal u - 1) + (unitVal w - 1) +
        (unitVal u - 1) * (unitVal w - 1) := by
      simp only [unitVal, Units.val_mul, Subring.coe_mul]
      ring
    show unitVal (u * w) - 1 ∈ D.lat (D.k + j)
    rw [e]
    exact add_mem (add_mem hu hw)
      (D.lat_antitone (Nat.le_succ _) (D.mul_mem_lat (Nat.le_add_right _ _) hu hw))
  inv_mem' {u} hu := by
    obtain ⟨v, hv, hvi⟩ := D.exists_unit (Nat.le_add_right _ j) hu
    have : v = u := unitVal_injective (by rw [hv]; ring)
    rw [← this]
    exact hvi

theorem mem_units {j : ℕ} {u : 𝒪[L]ˣ} : u ∈ D.units j ↔ unitVal u - 1 ∈ D.lat (D.k + j) := Iff.rfl

theorem units_antitone : Antitone D.units := fun _ _ h _ hu =>
  D.lat_antitone (by omega) hu

theorem exists_mem_units_eq (j : ℕ) (σ : Gal(L/K)) {u : 𝒪[L]ˣ} (hu : u ∈ D.units j) :
    ∃ w ∈ D.units j, unitVal w = σ (unitVal u) := by
  have hx : σ (unitVal u - 1) ∈ D.lat (D.k + j) := algEquiv_mem_normalLattice _ _ σ hu
  obtain ⟨w, hw, -⟩ := D.exists_unit (Nat.le_add_right _ j) hx
  refine ⟨w, ?_, ?_⟩
  · rw [mem_units, hw, add_sub_cancel_left]
    exact hx
  · rw [hw, map_sub, map_one]
    ring

end NormalLatticeData

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L]

theorem NormalLatticeData.nonempty : Nonempty (NormalLatticeData K L) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨θ, hθ, hθO⟩ := exists_normalBasis_integer (L := L) hπ
  obtain ⟨r, hr⟩ := exists_pow_smul_mul_mem_normalLattice π θ hπ hθ
  exact ⟨⟨π, hπ, θ, hθ, hθO, r, hr⟩⟩

end Data

section Units

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

namespace NormalLatticeData

variable (D : NormalLatticeData K L)

theorem units_zero_stable :
    ∀ σ : Gal(L/K), ∀ u ∈ D.units 0, ∃ w ∈ D.units 0, unitVal w = σ (unitVal u) :=
  fun σ _ hu => D.exists_mem_units_eq 0 σ hu

@[instance_reducible]
def action : MulDistribMulAction Gal(L/K) (D.units 0) :=
  stableUnitsAction (D.units 0) D.units_zero_stable

attribute [local instance] action

abbrev val (x : D.units 0) : L := unitVal (x : 𝒪[L]ˣ)

theorem val_injective : Function.Injective D.val :=
  fun _ _ h => Subtype.ext (unitVal_injective h)

theorem val_one : D.val 1 = 1 := by simp [val, unitVal]

theorem val_mul (x y : D.units 0) : D.val (x * y) = D.val x * D.val y := by
  simp [val, unitVal]

theorem val_mul_val_inv (x : D.units 0) : D.val x * D.val x⁻¹ = 1 := by
  rw [← val_mul, mul_inv_cancel, val_one]

theorem val_smul (σ : Gal(L/K)) (x : D.units 0) : D.val (σ • x) = σ (D.val x) :=
  unitVal_smul (D.units 0) D.units_zero_stable σ x

theorem val_sub_one_mem (x : D.units 0) : D.val x - 1 ∈ D.lat D.k := x.2

theorem val_mul_mem (x : D.units 0) {t : ℕ} {z : L} (hz : z ∈ D.lat t) : D.val x * z ∈ D.lat t := by
  have e : D.val x * z = z + (D.val x - 1) * z := by ring
  rw [e]
  exact add_mem hz (D.lat_antitone (Nat.le_succ t) (D.mul_mem_lat le_rfl (D.val_sub_one_mem x) hz))

def filt : StableFiltration Gal(L/K) (D.units 0) where
  F j := (D.units j).subgroupOf (D.units 0)
  antitone := fun _ _ h _ hx => D.units_antitone h hx
  smul_mem j σ {x} hx := by
    show D.val (σ • x) - 1 ∈ D.lat (D.k + j)
    rw [val_smul, ← map_one σ, ← map_sub]
    exact algEquiv_mem_normalLattice _ _ σ hx

theorem mem_filt {j : ℕ} {x : D.units 0} : x ∈ D.filt.F j ↔ D.val x - 1 ∈ D.lat (D.k + j) :=
  Iff.rfl

theorem filt_zero : D.filt.F 0 = ⊤ := Subgroup.subgroupOf_self _

theorem div_mem_filt_iff {j : ℕ} {x y : D.units 0} :
    x / y ∈ D.filt.F j ↔ D.val x - D.val y ∈ D.lat (D.k + j) := by
  rw [mem_filt]
  have e1 : D.val (x / y) - 1 = D.val y⁻¹ * (D.val x - D.val y) := by
    rw [div_eq_mul_inv, val_mul]
    linear_combination D.val_mul_val_inv y
  have e2 : D.val x - D.val y = D.val y * (D.val (x / y) - 1) := by
    rw [div_eq_mul_inv, val_mul]
    linear_combination (-D.val x) * D.val_mul_val_inv y
  constructor
  · intro h
    rw [e2]
    exact D.val_mul_mem y h
  · intro h
    rw [e1]
    exact D.val_mul_mem y⁻¹ h

theorem filt_complete : FiltrationComplete D.filt.F := by
  intro x hx
  obtain ⟨z, hz, hlim⟩ := exists_limit_normalLattice D.π D.θ D.irreducible D.linearIndependent
    (s := D.k) (fun n => D.val (x n) - 1) (fun n => D.val_sub_one_mem (x n)) (fun N => by
      obtain ⟨M, hM⟩ := hx N
      refine ⟨M, fun m hm n hn => ?_⟩
      have := D.div_mem_filt_iff.mp (hM m hm n hn)
      rwa [sub_sub_sub_cancel_right])
  obtain ⟨w, hw, -⟩ := D.exists_unit le_rfl hz
  have hw0 : w ∈ D.units 0 := by
    rw [mem_units, hw, add_sub_cancel_left]
    exact hz
  refine ⟨⟨w, hw0⟩, fun N => ?_⟩
  obtain ⟨M, hM⟩ := hlim N
  refine ⟨M, fun n hn => D.div_mem_filt_iff.mpr ?_⟩
  have e : D.val (x n) - D.val ⟨w, hw0⟩ = (D.val (x n) - 1) - z := by
    simp only [val, hw]
    ring
  rw [e]
  exact hM n hn

theorem filt_separated : FiltrationSeparated D.filt.F := by
  intro x hx
  have h0 : D.val x - 1 = 0 := eq_zero_of_forall_mem_normalLattice D.π D.θ D.irreducible
    D.linearIndependent (s := D.k) fun N => hx N
  exact D.val_injective (by rw [val_one]; exact sub_eq_zero.mp h0)

end NormalLatticeData

end Units

section Graded

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L] [ValuativeExtension K L]
  [FiniteDimensional K L] in
theorem algEquiv_algebraMap_integer (τ : Gal(L/K)) (c : 𝒪[K]) :
    τ (algebraMap 𝒪[K] L c) = algebraMap 𝒪[K] L c := by
  rw [IsScalarTower.algebraMap_apply 𝒪[K] K L, AlgEquiv.commutes]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L] [ValuativeExtension K L]
  [FiniteDimensional K L] in
theorem quotient_mk_sum {N : AddSubgroup L} {ι : Type*} [Fintype ι] (g : ι → L) :
    ∑ i, (g i : L ⧸ N) = ((∑ i, g i : L) : L ⧸ N) :=
  (map_sum (QuotientAddGroup.mk' N) g univ).symm

namespace NormalLatticeData

variable (D : NormalLatticeData K L)

attribute [local instance] action

abbrev Q (j : ℕ) : AddSubgroup L := (D.lat (D.k + j + 1)).toAddSubgroup

def grHom (j : ℕ) : D.filt.F j →* Multiplicative (L ⧸ D.Q j) where
  toFun x := Multiplicative.ofAdd ((D.val x - 1 : L) : L ⧸ D.Q j)
  map_one' := by simp [val_one]
  map_mul' x y := by
    rw [← ofAdd_add, ← QuotientAddGroup.mk_add]
    congr 1
    rw [QuotientAddGroup.eq_iff_sub_mem, Submodule.mem_toAddSubgroup]
    have e : D.val ((x * y : D.filt.F j) : D.units 0) - 1 - ((D.val x - 1) + (D.val y - 1)) =
        (D.val x - 1) * (D.val y - 1) := by
      rw [Subgroup.coe_mul, val_mul]
      ring
    rw [e]
    exact D.mul_mem_lat (Nat.le_add_right _ _) (D.mem_filt.mp x.2) (D.mem_filt.mp y.2)

theorem grHom_toAdd {j : ℕ} (x : D.filt.F j) :
    (D.grHom j x).toAdd = ((D.val x - 1 : L) : L ⧸ D.Q j) := rfl

theorem grHom_eq_one_iff {j : ℕ} (x : D.filt.F j) :
    D.grHom j x = 1 ↔ (x : D.units 0) ∈ D.filt.F (j + 1) := by
  rw [← toAdd_eq_zero, grHom_toAdd, QuotientAddGroup.eq_zero_iff, Submodule.mem_toAddSubgroup,
    mem_filt]
  rfl

theorem val_coe_smul_F {j : ℕ} (σ : Gal(L/K)) (y : D.filt.F j) :
    D.val ((σ • y : D.filt.F j) : D.units 0) = σ (D.val y) := by
  rw [StableFiltration.coe_smul_F, val_smul]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension K L]
  [FiniteDimensional K L] in

theorem smul_theta_mem (j : ℕ) (c : 𝒪[K]) : c • D.π ^ (D.k + j) • D.θ ∈ D.lat (D.k + j) := by
  have : D.π ^ (D.k + j) • (1 : Gal(L/K)) D.θ ∈ D.lat (D.k + j) := Submodule.subset_span ⟨1, rfl⟩
  simpa using Submodule.smul_mem _ c this

theorem exists_mem_filt (j : ℕ) (c : 𝒪[K]) :
    ∃ y : D.units 0, y ∈ D.filt.F j ∧ D.val y = 1 + c • D.π ^ (D.k + j) • D.θ := by
  obtain ⟨w, hw, -⟩ := D.exists_unit (Nat.le_add_right _ _) (D.smul_theta_mem j c)
  have hw0 : w ∈ D.units 0 := by
    rw [mem_units, hw, add_sub_cancel_left]
    exact D.lat_antitone (Nat.le_add_right _ _) (D.smul_theta_mem j c)
  refine ⟨⟨w, hw0⟩, ?_, hw⟩
  rw [mem_filt]
  show unitVal w - 1 ∈ _
  rw [hw, add_sub_cancel_left]
  exact D.smul_theta_mem j c

theorem subsingleton_tateZero_gr (j : ℕ) : Subsingleton (TateZero Gal(L/K) (D.filt.gr j)) := by
  rw [D.filt.subsingleton_tateZero_gr_iff]
  intro x hx hinv
  obtain ⟨c, hc⟩ := (mem_normalLattice_iff D.π D.θ).mp (D.mem_filt.mp hx)
  have hdiv : ∀ σ : Gal(L/K), D.π ^ 1 ∣ c σ - c 1 := by
    intro σ
    have h1 := D.div_mem_filt_iff.mp (hinv σ)
    rw [← add_assoc] at h1
    have e : D.val (σ • x) - D.val x = D.π ^ (D.k + j) • ∑ τ, (c (σ⁻¹ * τ) - c τ) • τ D.θ := by
      rw [← smul_sum_sub_smul_sum, ← algEquiv_smul_sum, hc, val_smul, map_sub, map_one]
      ring
    rw [e] at h1
    have h2 := (smul_sum_mem_normalLattice_add_iff D.π D.θ D.irreducible.ne_zero
      D.linearIndependent (D.k + j) 1 _).mp h1 σ
    rw [inv_mul_cancel] at h2
    have := dvd_neg.mpr h2
    rwa [neg_sub] at this
  obtain ⟨y, hy, hyv⟩ := D.exists_mem_filt j (c 1)
  refine ⟨y, hy, ?_⟩
  let x' : D.filt.F j := ⟨x, hx⟩
  let y' : D.filt.F j := ⟨y, hy⟩
  have e1 : x / tateNorm Gal(L/K) (D.units 0) y =
      ((x' / tateNorm Gal(L/K) (D.filt.F j) y' : D.filt.F j) : D.units 0) := by
    rw [Subgroup.coe_div, D.filt.coe_tateNorm_F]
  rw [e1, ← grHom_eq_one_iff, map_div, div_eq_one]
  apply Multiplicative.toAdd.injective
  rw [grHom_toAdd, tateNorm_apply, map_prod, toAdd_prod]
  simp_rw [grHom_toAdd, val_coe_smul_F]
  rw [quotient_mk_sum, QuotientAddGroup.eq_iff_sub_mem, Submodule.mem_toAddSubgroup]
  have e2 : D.val x' - 1 - ∑ σ : Gal(L/K), (σ (D.val y') - 1) =
      D.π ^ (D.k + j) • ∑ σ, (c σ - c 1) • σ D.θ := by
    show D.val x - 1 - ∑ σ : Gal(L/K), (σ (D.val y) - 1) = _
    rw [← hc, hyv]
    simp only [Algebra.smul_def, map_add, map_one, map_mul, map_pow, map_sub,
      algEquiv_algebraMap_integer, add_sub_cancel_left, Finset.mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun σ _ => ?_
    ring
  rw [e2]
  exact (smul_sum_mem_normalLattice_add_iff D.π D.θ D.irreducible.ne_zero D.linearIndependent
    (D.k + j) 1 _).mpr hdiv

theorem subsingleton_tateNegOne_gr (j : ℕ) : Subsingleton (TateNegOne Gal(L/K) (D.filt.gr j)) := by
  rw [D.filt.subsingleton_tateNegOne_gr_iff]
  intro x hx hN
  obtain ⟨c, hc⟩ := (mem_normalLattice_iff D.π D.θ).mp (D.mem_filt.mp hx)
  let x' : D.filt.F j := ⟨x, hx⟩
  have hN' : ((tateNorm Gal(L/K) (D.filt.F j) x' : D.filt.F j) : D.units 0) ∈ D.filt.F (j + 1) := by
    rwa [D.filt.coe_tateNorm_F]
  rw [← grHom_eq_one_iff, ← toAdd_eq_zero, tateNorm_apply, map_prod, toAdd_prod] at hN'
  simp_rw [grHom_toAdd, val_coe_smul_F] at hN'
  rw [quotient_mk_sum, QuotientAddGroup.eq_zero_iff, Submodule.mem_toAddSubgroup] at hN'
  have e : ∑ σ : Gal(L/K), (σ (D.val x') - 1) =
      D.π ^ (D.k + j) • ∑ τ, (∑ σ : Gal(L/K), c (σ⁻¹ * τ)) • τ D.θ := by
    have h1 : ∀ σ : Gal(L/K), σ (D.val x') - 1 = σ (D.val x' - 1) := fun σ => by
      rw [map_sub, map_one]
    simp_rw [h1]
    show ∑ σ : Gal(L/K), σ (D.val x - 1) = _
    simp_rw [← hc, algEquiv_smul_sum, ← smul_sum]
    rw [sum_comm]
    simp_rw [sum_smul]
  rw [e] at hN'
  have hdiv := (smul_sum_mem_normalLattice_add_iff D.π D.θ D.irreducible.ne_zero
    D.linearIndependent (D.k + j) 1 _).mp hN' 1
  have hsumc : ∑ σ : Gal(L/K), c (σ⁻¹ * 1) = ∑ σ, c σ := by
    simp_rw [mul_one]
    exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun _ => rfl)
  rw [hsumc, pow_one] at hdiv
  obtain ⟨e0, he0⟩ := hdiv
  choose m hm hmv using fun τ => D.exists_mem_filt j (c τ)
  refine ⟨m, hm, ?_⟩
  let m' : Gal(L/K) → D.filt.F j := fun τ => ⟨m τ, hm τ⟩
  have e1 : x / augMap Gal(L/K) (D.units 0) m =
      ((x' / augMap Gal(L/K) (D.filt.F j) m' : D.filt.F j) : D.units 0) := by
    rw [Subgroup.coe_div, D.filt.coe_augMap_F]
  rw [e1, ← grHom_eq_one_iff, map_div, div_eq_one]
  apply Multiplicative.toAdd.injective
  rw [grHom_toAdd, augMap_apply, map_prod, toAdd_prod]
  simp_rw [map_div, toAdd_div, grHom_toAdd, val_coe_smul_F, ← QuotientAddGroup.mk_sub]
  rw [quotient_mk_sum, QuotientAddGroup.eq_iff_sub_mem, Submodule.mem_toAddSubgroup]
  have e2 : D.val x' - 1 - ∑ τ : Gal(L/K), (τ (D.val (m' τ)) - 1 - (D.val (m' τ) - 1)) =
      e0 • D.π ^ (D.k + j + 1) • D.θ := by
    show D.val x - 1 - ∑ τ : Gal(L/K), (τ (D.val (m τ)) - 1 - (D.val (m τ) - 1)) = _
    rw [← hc]
    simp_rw [hmv]
    have he0' : ∑ τ, algebraMap 𝒪[K] L (c τ) = algebraMap 𝒪[K] L D.π * algebraMap 𝒪[K] L e0 := by
      rw [← map_sum, he0, map_mul]
    simp only [Algebra.smul_def, map_add, map_one, map_mul, map_pow,
      algEquiv_algebraMap_integer, add_sub_cancel_left, Finset.mul_sum, sum_sub_distrib]
    have h3 : ∑ τ : Gal(L/K), algebraMap 𝒪[K] L (c τ) * (algebraMap 𝒪[K] L D.π ^ (D.k + j) * D.θ) =
        (∑ τ, algebraMap 𝒪[K] L (c τ)) * (algebraMap 𝒪[K] L D.π ^ (D.k + j) * D.θ) := by
      rw [Finset.sum_mul]
    rw [h3, he0']
    ring_nf
  rw [e2]
  have : D.π ^ (D.k + j + 1) • (1 : Gal(L/K)) D.θ ∈ D.lat (D.k + j + 1) :=
    Submodule.subset_span ⟨1, rfl⟩
  simpa using Submodule.smul_mem _ e0 this

end NormalLatticeData

end Graded

section Main

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] in
open scoped Pointwise in

theorem normalLattice_eq_smul_span (π : 𝒪[K]) (θ : L) (s : ℕ) :
    normalLattice π θ s = π ^ s • Submodule.span 𝒪[K] (Set.range fun σ : Gal(L/K) => σ θ) := by
  rw [normalLattice, ← Set.smul_set_range, Submodule.span_smul]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] in

theorem span_conjugates_eq_top {θ : L} (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) :
    Submodule.span K (Set.range fun σ : Gal(L/K) => σ θ) = ⊤ := by
  have := (basisOfLinearIndependentOfCardEqFinrank hθ
    (Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank K L))).span_eq
  simpa [coe_basisOfLinearIndependentOfCardEqFinrank] using this

namespace NormalLatticeData

variable (D : NormalLatticeData K L)

theorem isOpen_units (j : ℕ) : IsOpen (D.units j : Set 𝒪[L]ˣ) := by
  have h : (D.units j : Set 𝒪[L]ˣ) =
      (fun u : 𝒪[L]ˣ => unitVal u - 1) ⁻¹' (D.lat (D.k + j) : Set L) := rfl
  rw [h]
  exact (isOpen_normalLattice D.π D.θ D.irreducible D.linearIndependent _).preimage
    ((continuous_subtype_val.comp Units.continuous_val).sub continuous_const)

attribute [local instance] action

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] [IsGalois K L] in

theorem subsingleton_tate :
    Subsingleton (TateZero Gal(L/K) (D.units 0)) ∧ Subsingleton (TateNegOne Gal(L/K) (D.units 0)) :=
  subsingleton_tate_of_complete D.filt D.filt_zero D.filt_complete D.filt_separated
    D.subsingleton_tateZero_gr D.subsingleton_tateNegOne_gr

end NormalLatticeData

open scoped Pointwise in

theorem exists_openSubgroup_units_tateTrivial :
    ∃ (π : 𝒪[K]) (θ : L) (k : ℕ), Irreducible π ∧ (LinearIndependent K fun σ : Gal(L/K) => σ θ) ∧
      Submodule.span K (Set.range fun σ : Gal(L/K) => σ θ) = ⊤ ∧
      (∀ σ : Gal(L/K), σ θ ∈ 𝒪[L]) ∧
      ∃ (V : Subgroup 𝒪[L]ˣ)
        (hV : ∀ σ : Gal(L/K), ∀ u ∈ V, ∃ w ∈ V, ((w : 𝒪[L]) : L) = σ ((u : 𝒪[L]) : L)),
        (∀ u : 𝒪[L]ˣ, u ∈ V ↔
          ((u : 𝒪[L]) : L) - 1 ∈ π ^ k • Submodule.span 𝒪[K] (Set.range fun σ : Gal(L/K) => σ θ)) ∧
        IsOpen (V : Set 𝒪[L]ˣ) ∧
        (letI := stableUnitsAction V hV;
          Subsingleton (TateZero Gal(L/K) V) ∧ Subsingleton (TateNegOne Gal(L/K) V)) := by
  obtain ⟨D⟩ := NormalLatticeData.nonempty K L
  refine ⟨D.π, D.θ, D.k, D.irreducible, D.linearIndependent,
    span_conjugates_eq_top D.linearIndependent, D.integer, D.units 0, D.units_zero_stable,
    fun u => ?_, D.isOpen_units 0, D.subsingleton_tate⟩
  rw [← normalLattice_eq_smul_span]
  exact Iff.rfl

end Main

end GroundTheory.LocalField

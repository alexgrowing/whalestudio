import Mathlib
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups

namespace GroundTheory.Global

open Topology Filter IsDedekindDomain WithZero

noncomputable section

theorem exists_le_ker_of_noSmallSubgroups {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] {P : Subgroup G → Prop}
    (hP : ∀ W ∈ 𝓝 (1 : G), ∃ L : Subgroup G, P L ∧ (L : Set G) ⊆ W) (hH : NoSmallSubgroups H)
    (χ : G →* H) (hχ : Continuous χ) : ∃ L : Subgroup G, P L ∧ L ≤ χ.ker := by
  obtain ⟨U, hU, hsmall⟩ := hH
  have hW : χ ⁻¹' U ∈ 𝓝 (1 : G) := hχ.continuousAt.preimage_mem_nhds (by rwa [map_one])
  obtain ⟨L, hL, hLW⟩ := hP _ hW
  refine ⟨L, hL, ?_⟩
  rw [← Subgroup.map_eq_bot_iff]
  refine hsmall _ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hLW hx

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

def unitsLevel (n : ℕ) : Subgroup (v.adicCompletion K)ˣ where
  carrier := {x | Valued.v (x : v.adicCompletion K) = 1 ∧
    Valued.v ((x : v.adicCompletion K) - 1) ≤ exp (-(n : ℤ))}
  one_mem' := by simp
  mul_mem' {x y} hx hy := by
    refine ⟨by simp [hx.1, hy.1], ?_⟩
    have : ((x * y : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
        (x : v.adicCompletion K) * ((y : v.adicCompletion K) - 1) +
          ((x : v.adicCompletion K) - 1) := by
      push_cast; ring
    rw [this]
    refine Valuation.map_add_le _ ?_ hx.2
    rw [map_mul, hx.1, one_mul]
    exact hy.2
  inv_mem' {x} hx := by
    have hx0 : (x : v.adicCompletion K) ≠ 0 := x.ne_zero
    refine ⟨by simp [hx.1], ?_⟩
    have : ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
        (x : v.adicCompletion K)⁻¹ * (1 - (x : v.adicCompletion K)) := by
      rw [Units.val_inv_eq_inv_val, mul_sub, mul_one, inv_mul_cancel₀ hx0]
    rw [this, map_mul, map_inv₀, hx.1, inv_one, one_mul, Valuation.map_sub_swap]
    exact hx.2

variable {v} in
theorem mem_unitsLevel {n : ℕ} {x : (v.adicCompletion K)ˣ} :
    x ∈ unitsLevel v n ↔ Valued.v (x : v.adicCompletion K) = 1 ∧
      Valued.v ((x : v.adicCompletion K) - 1) ≤ exp (-(n : ℤ)) :=
  Iff.rfl

variable {v} in

theorem mem_unitsLevel_of_one_le {n : ℕ} (hn : 1 ≤ n) {x : (v.adicCompletion K)ˣ} :
    x ∈ unitsLevel v n ↔ Valued.v ((x : v.adicCompletion K) - 1) ≤ exp (-(n : ℤ)) := by
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  have hlt : Valued.v ((x : v.adicCompletion K) - 1) < Valued.v (1 : v.adicCompletion K) := by
    rw [map_one]
    refine h.trans_lt ?_
    rw [← exp_zero, exp_lt_exp]
    omega
  simpa using Valuation.map_eq_of_sub_lt _ hlt

theorem unitsLevel_zero :
    unitsLevel (K := K) v 0 = (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  ext x
  rw [Submonoid.mem_units_iff, mem_unitsLevel]
  change _ ↔ (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
    ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · rintro ⟨h1, -⟩
    simp [h1]
  · rintro ⟨h1, h2⟩
    have hx0 : Valued.v (x : v.adicCompletion K) ≠ 0 := by simp
    have h3 : 1 ≤ Valued.v (x : v.adicCompletion K) := by
      exact (inv_le_one₀ (zero_lt_iff.2 hx0)).1 h2
    refine ⟨le_antisymm h1 h3, ?_⟩
    rw [Nat.cast_zero, neg_zero, exp_zero]
    exact Valuation.map_sub_le _ h1 (by simp)

theorem unitsLevel_antitone : Antitone (unitsLevel (K := K) v) := by
  intro m n hmn x hx
  refine ⟨hx.1, hx.2.trans ?_⟩
  rw [exp_le_exp]
  omega

theorem isOpen_unitsLevel (n : ℕ) : IsOpen (unitsLevel (K := K) v n : Set (v.adicCompletion K)ˣ) := by
  refine Subgroup.isOpen_of_mem_nhds (g := 1) _ ?_
  obtain ⟨a, ha⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective (K := K) (v := v)
    (exp (-(n : ℤ)))
  have ha0 : Valued.v a ≠ 0 := by simp [ha]
  have h1 : {y : v.adicCompletion K | Valued.v y = 1} ∈ 𝓝 (1 : v.adicCompletion K) := by
    simpa using Valued.locally_const (x := (1 : v.adicCompletion K)) (by simp)
  have h2 : {y : v.adicCompletion K | Valued.v (y - 1) ≤ exp (-(n : ℤ))} ∈
      𝓝 (1 : v.adicCompletion K) := by
    have hc : Continuous fun y : v.adicCompletion K ↦ y - 1 + a :=
      (continuous_id.sub continuous_const).add continuous_const
    have h := hc.continuousAt.preimage_mem_nhds (x := (1 : v.adicCompletion K))
      (by simpa using Valued.locally_const (x := a) ha0)
    refine Filter.mem_of_superset h fun y hy ↦ ?_
    have hy' : Valued.v (y - 1 + a) = exp (-(n : ℤ)) := by rw [← ha]; exact hy
    have : y - 1 = (y - 1 + a) - a := by ring
    change Valued.v (y - 1) ≤ exp (-(n : ℤ))
    rw [this]
    exact Valuation.map_sub_le _ hy'.le ha.le
  have h3 := Units.continuous_val.continuousAt.preimage_mem_nhds (x := (1 : (v.adicCompletion K)ˣ))
    (by rw [Units.val_one]; exact Filter.inter_mem h1 h2)
  exact Filter.mem_of_superset h3 fun x hx ↦ hx

theorem exists_unitsLevel_subset {t : Set (v.adicCompletion K)ˣ} (ht : t ∈ 𝓝 1) :
    ∃ n : ℕ, 1 ≤ n ∧ (unitsLevel (K := K) v n : Set (v.adicCompletion K)ˣ) ⊆ t := by
  rw [Units.isEmbedding_val₀.nhds_eq_comap, Units.val_one, mem_comap] at ht
  obtain ⟨t', ht', hsub⟩ := ht
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 ht'
  set c := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc
  have hc0 : c ≠ 0 := fun h ↦ γ.ne_zero
    (MonoidWithZeroHom.ValueGroup₀.embedding_injective (h.trans (map_zero _).symm))
  refine ⟨(-(log c)).toNat + 1, by omega, fun x hx ↦ hsub (hγ ?_)⟩
  change Valued.v.restrict ((x : v.adicCompletion K) - 1) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hc]
  refine hx.2.trans_lt (lt_of_lt_of_eq ?_ (exp_log hc0))
  rw [exp_lt_exp]
  omega

section Character

variable {H : Type*} [Group H] [TopologicalSpace H]

theorem exists_unitsLevel_le_ker (hH : NoSmallSubgroups H) (χ : (v.adicCompletion K)ˣ →* H)
    (hχ : Continuous χ) : ∃ n : ℕ, 1 ≤ n ∧ unitsLevel v n ≤ χ.ker := by
  obtain ⟨L, ⟨n, hn, rfl⟩, hL⟩ := exists_le_ker_of_noSmallSubgroups
    (P := fun L ↦ ∃ n : ℕ, 1 ≤ n ∧ L = unitsLevel v n)
    (fun W hW ↦ by
      obtain ⟨n, hn, h⟩ := exists_unitsLevel_subset v hW
      exact ⟨_, ⟨n, hn, rfl⟩, h⟩) hH χ hχ
  exact ⟨n, hn, hL⟩

theorem isOpen_ker_of_continuous (hH : NoSmallSubgroups H) (χ : (v.adicCompletion K)ˣ →* H)
    (hχ : Continuous χ) : IsOpen (χ.ker : Set (v.adicCompletion K)ˣ) := by
  obtain ⟨n, -, hn⟩ := exists_unitsLevel_le_ker v hH χ hχ
  exact Subgroup.isOpen_mono hn (isOpen_unitsLevel v n)

def conductorExponent (χ : (v.adicCompletion K)ˣ →* H) : ℕ :=
  sInf {n : ℕ | unitsLevel v n ≤ χ.ker}

theorem unitsLevel_le_ker_iff (hH : NoSmallSubgroups H) (χ : (v.adicCompletion K)ˣ →* H)
    (hχ : Continuous χ) {n : ℕ} : unitsLevel v n ≤ χ.ker ↔ conductorExponent v χ ≤ n := by
  have hne : {n : ℕ | unitsLevel v n ≤ χ.ker}.Nonempty :=
    (exists_unitsLevel_le_ker v hH χ hχ).imp fun _ h ↦ h.2
  refine ⟨fun h ↦ Nat.sInf_le h, fun h ↦ (unitsLevel_antitone v h).trans (Nat.sInf_mem hne)⟩

theorem conductorExponent_eq_zero_iff (hH : NoSmallSubgroups H) (χ : (v.adicCompletion K)ˣ →* H)
    (hχ : Continuous χ) :
    conductorExponent v χ = 0 ↔ (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ χ.ker := by
  rw [← unitsLevel_zero, unitsLevel_le_ker_iff v hH χ hχ, Nat.le_zero]

end Character

end

end GroundTheory.Global

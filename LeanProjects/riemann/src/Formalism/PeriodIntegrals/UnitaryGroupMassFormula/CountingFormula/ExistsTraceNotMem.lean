import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.PairUnitLoc

open NumberField Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.UG

variable {K : Type} [Field K] [NumberField K] [StarRing K]

private lemma not_mem_of_mem_hcompl {p : Ideal (𝓞 K)} (hp : p.IsPrime) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) : s ∉ p ∧ conjO K s ∉ p := by
  rw [hcompl_eq_closure] at hs
  let M : Submonoid (𝓞 K) :=
    { carrier := {s | s ∉ p ∧ conjO K s ∉ p}
      mul_mem' := by
        intro x y hx hy
        obtain ⟨hx1, hx2⟩ := hx
        obtain ⟨hy1, hy2⟩ := hy
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rcases hp.mem_or_mem h with h | h
          exacts [hx1 h, hy1 h]
        · rw [map_mul] at h
          rcases hp.mem_or_mem h with h | h
          exacts [hx2 h, hy2 h]
      one_mem' := by
        refine ⟨fun h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr h), fun h => ?_⟩
        rw [map_one] at h
        exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr h) }
  have hle : Submonoid.closure {s : 𝓞 K | s ∉ p ∧ conjO K s ∉ p} ≤ M :=
    Submonoid.closure_le.mpr (fun x hx => hx)
  exact hle hs

theorem num_mem_both {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p) (hst : star a = a)
    (hna : ¬ IsUnitIn (locRing p) a) :
    ∃ a₁ : 𝓞 K, ∃ s₁ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
      a = algebraMap (𝓞 K) K a₁ / algebraMap (𝓞 K) K s₁ ∧ a₁ ∈ p ∧ a₁ ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p := by
  have hinj := IsFractionRing.injective (𝓞 K) K
  have hloc : a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := ha
  obtain ⟨s, hs, hsa⟩ := (Formalism.HermitianLatticesTheory.locDual_mem_locR (K := K) p a).mp hloc
  obtain ⟨a₀, ha₀⟩ := Submodule.mem_one.mp hsa
  obtain ⟨hs1, hs2⟩ := not_mem_of_mem_hcompl hp hs
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
    intro h
    apply hs1
    have : s = 0 := hinj (by rw [h, map_zero])
    rw [this]
    exact p.zero_mem
  have hcs0 : star (algebraMap (𝓞 K) K s) ≠ 0 := by
    rw [← algebraMap_conjO]
    intro h
    apply hs2
    have : conjO K s = 0 := hinj (by rw [h, map_zero])
    rw [this]
    exact p.zero_mem
  obtain ⟨a₁, ha₁d⟩ : ∃ x : 𝓞 K, x = a₀ * conjO K s := ⟨_, rfl⟩
  obtain ⟨s₁, hs₁d⟩ : ∃ x : 𝓞 K, x = s * conjO K s := ⟨_, rfl⟩
  have hs₁ : s₁ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
    rw [hs₁d]
    exact mul_mem hs (conjO_mem_hcompl hs)
  have hA : algebraMap (𝓞 K) K a₁ = algebraMap (𝓞 K) K s₁ * a := by
    rw [ha₁d, hs₁d, map_mul, map_mul, algebraMap_conjO, ha₀]
    ring
  have hAs : star (algebraMap (𝓞 K) K s₁) = algebraMap (𝓞 K) K s₁ := by
    rw [hs₁d, map_mul, algebraMap_conjO, star_mul, star_star]
  have hc : conjO K a₁ = a₁ := hinj (by rw [algebraMap_conjO, hA, star_mul, hst, hAs, mul_comm])
  have hs₁0 : algebraMap (𝓞 K) K s₁ ≠ 0 := by
    rw [hs₁d, map_mul, algebraMap_conjO]
    exact mul_ne_zero hs0 hcs0
  have hp1 : a₁ ∈ p := by
    by_contra hn
    have hmem : a₁ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
      rw [hcompl_eq_closure]
      exact Submonoid.subset_closure ⟨hn, by rw [hc]; exact hn⟩
    have ha0 : a ≠ 0 := by
      intro h0
      apply hn
      have : a₁ = 0 := hinj (by rw [hA, h0, mul_zero, map_zero])
      rw [this]
      exact p.zero_mem
    apply hna
    refine ⟨ha0, ha, ?_⟩
    change a⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    refine ⟨a₁, hmem, Submodule.mem_one.mpr ⟨s₁, ?_⟩⟩
    rw [hA, mul_assoc, mul_inv_cancel₀ ha0, mul_one]
  refine ⟨a₁, s₁, hs₁, ?_, hp1, ?_⟩
  · rw [hA, eq_div_iff hs₁0, mul_comm]
  · rw [mem_conjIdeal_iff, hc]
    exact hp1

theorem exists_trace_notMem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    ∃ l : 𝓞 K, l + conjO K l ∉ p := by
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hp
  by_cases h2 : (2 : 𝓞 K) ∈ p
  · refine ⟨θ, fun h => hθ ?_⟩
    have e : θ - conjO K θ = (θ + conjO K θ) - 2 * conjO K θ := by ring
    rw [e]
    exact p.sub_mem h (p.mul_mem_right _ h2)
  · refine ⟨1, ?_⟩
    rw [map_one, one_add_one_eq_two]
    exact h2

theorem pair_unit_local : PairUnitLoc := by
  intro K _ _ _ hK p hp V _ _ h hh w y hyw ha hb
  have hpp : p.IsPrime := hp.isPrime
  have hinj := IsFractionRing.injective (𝓞 K) K
  by_cases hua : IsUnitIn (locRing p) (h w w)
  · exact ⟨1, (locRing p).one_mem, 0, (locRing p).zero_mem, by simpa using hua⟩
  by_cases hub : IsUnitIn (locRing p) (h y y)
  · exact ⟨0, (locRing p).zero_mem, 1, (locRing p).one_mem, by simpa using hub⟩
  obtain ⟨l, hl⟩ := exists_trace_notMem hK hp
  have hwy : h w y = 1 := by rw [← hh.eq y w, hyw, map_one]
  have hsa : star (h w w) = h w w := by
    have := hh.eq w w
    rwa [starRingEnd_apply] at this
  have hsb : star (h y y) = h y y := by
    have := hh.eq y y
    rwa [starRingEnd_apply] at this
  obtain ⟨a₁, s₁, hs₁, hae, ha₁, -⟩ := num_mem_both hpp ha hsa hua
  obtain ⟨b₁, s₂, hs₂, hbe, hb₁, -⟩ := num_mem_both hpp hb hsb hub
  have hAmem : ∀ r : 𝓞 K, algebraMap (𝓞 K) K r ∈ locRing p := by
    intro r
    change algebraMap (𝓞 K) K r ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    exact ⟨1, one_mem _, Submodule.mem_one.mpr ⟨r, by rw [map_one, one_mul]⟩⟩
  refine ⟨1, (locRing p).one_mem, algebraMap (𝓞 K) K l, hAmem l, ?_⟩
  have hv : h ((1 : K) • w + algebraMap (𝓞 K) K l • y) ((1 : K) • w + algebraMap (𝓞 K) K l • y) =
      h w w + algebraMap (𝓞 K) K (l + conjO K l) + algebraMap (𝓞 K) K (conjO K l * l) * h y y := by
    simp only [one_smul, map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply, RingHom.id_apply, map_smul, hyw, hwy, map_mul,
      algebraMap_conjO, star_one]
    ring
  rw [hv]
  by_contra hnu
  have hvmem : h w w + algebraMap (𝓞 K) K (l + conjO K l) + algebraMap (𝓞 K) K (conjO K l * l) * h y y ∈ locRing p :=
    add_mem (add_mem ha (hAmem _)) (mul_mem (hAmem _) hb)
  have hvs : star (h w w + algebraMap (𝓞 K) K (l + conjO K l) + algebraMap (𝓞 K) K (conjO K l * l) * h y y) =
      h w w + algebraMap (𝓞 K) K (l + conjO K l) + algebraMap (𝓞 K) K (conjO K l * l) * h y y := by
    rw [star_add, star_add, star_mul, hsa, hsb, ← algebraMap_conjO, ← algebraMap_conjO,
      map_add, map_mul, Formalism.HermitianLattices.Ext.L3.conjO_conjO]
    ring
  obtain ⟨n, t, ht, hve, hn, -⟩ := num_mem_both hpp hvmem hvs hnu
  have hnz : ∀ {u : 𝓞 K}, u ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p → algebraMap (𝓞 K) K u ≠ 0 := by
    intro u hu h0
    apply (not_mem_of_mem_hcompl hpp hu).1
    have : u = 0 := hinj (by rw [h0, map_zero])
    rw [this]
    exact p.zero_mem
  have ht0 := hnz ht
  have h10 := hnz hs₁
  have h20 := hnz hs₂
  have key : n * (s₁ * s₂) = (a₁ * s₂ + (l + conjO K l) * (s₁ * s₂) + conjO K l * l * b₁ * s₁) * t := by
    apply hinj
    have e1 : algebraMap (𝓞 K) K n = (h w w + algebraMap (𝓞 K) K (l + conjO K l) + algebraMap (𝓞 K) K (conjO K l * l) * h y y) * algebraMap (𝓞 K) K t := by
      rw [hve, div_mul_cancel₀ _ ht0]
    simp only [map_mul, map_add]
    rw [e1, hae, hbe]
    simp only [map_mul, map_add]
    field_simp
  have hN : a₁ * s₂ + (l + conjO K l) * (s₁ * s₂) + conjO K l * l * b₁ * s₁ ∈ p := by
    have hmem : (a₁ * s₂ + (l + conjO K l) * (s₁ * s₂) + conjO K l * l * b₁ * s₁) * t ∈ p := by
      rw [← key]
      exact p.mul_mem_right _ hn
    rcases hpp.mem_or_mem hmem with h1 | h1
    · exact h1
    · exact absurd h1 (not_mem_of_mem_hcompl hpp ht).1
  have hT : (l + conjO K l) * (s₁ * s₂) ∈ p := by
    have e : (l + conjO K l) * (s₁ * s₂) =
        (a₁ * s₂ + (l + conjO K l) * (s₁ * s₂) + conjO K l * l * b₁ * s₁) - a₁ * s₂ -
          conjO K l * l * b₁ * s₁ := by ring
    rw [e]
    refine p.sub_mem (p.sub_mem hN (p.mul_mem_right _ ha₁)) ?_
    have e2 : conjO K l * l * b₁ * s₁ = (conjO K l * l) * (b₁ * s₁) := by ring
    rw [e2]
    exact p.mul_mem_left _ (p.mul_mem_right _ hb₁)
  rcases hpp.mem_or_mem hT with h1 | h1
  · exact hl h1
  · rcases hpp.mem_or_mem h1 with h2 | h2
    · exact (not_mem_of_mem_hcompl hpp hs₁).1 h2
    · exact (not_mem_of_mem_hcompl hpp hs₂).1 h2

end PI.UnitaryGroupMassFormula.CntFormula.UG

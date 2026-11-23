import Mathlib
import GroundTheory.GlobalFields.CyclotomicCharacters.ProfinitePadic

open Filter Topology
open scoped GroundTheory.LocalField.Abstract

namespace GroundTheory.Global

namespace Cyclotomic

open GroundTheory.LocalField.Abstract

section Padic

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem mul_mem_of_isClosed (H : AddSubgroup ℤ_[ℓ]) (hH : IsClosed (H : Set ℤ_[ℓ])) {x : ℤ_[ℓ]}
    (hx : x ∈ H) (t : ℤ_[ℓ]) : x * t ∈ H :=
  PadicInt.denseRange_natCast.induction_on t (hH.preimage (continuous_const.mul continuous_id))
    fun k => by
      show x * (k : ℤ_[ℓ]) ∈ H
      rw [mul_comm, ← nsmul_eq_mul]
      exact H.nsmul_mem hx k

theorem isOpen_of_isClosed_of_ne_zero (H : AddSubgroup ℤ_[ℓ]) (hH : IsClosed (H : Set ℤ_[ℓ]))
    {x : ℤ_[ℓ]} (hx : x ∈ H) (hx0 : x ≠ 0) : IsOpen (H : Set ℤ_[ℓ]) := by
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[ℓ]ˣ, x = u * (ℓ : ℤ_[ℓ]) ^ x.valuation :=
    ⟨_, PadicInt.unitCoeff_spec hx0⟩
  set v := x.valuation
  rw [Metric.isOpen_iff]
  intro y hy
  refine ⟨(ℓ : ℝ) ^ (-(v : ℤ)), zpow_pos (by exact_mod_cast hℓ.out.pos) _, fun w hw => ?_⟩
  have h1 : w - y ∈ Ideal.span {(ℓ : ℤ_[ℓ]) ^ v} :=
    (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 (by
      rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hw).le)
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h1
  have h2 : x * (↑u⁻¹ * t) = w - y := by
    rw [← ht, hu, show (u : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ v * (↑u⁻¹ * t) =
      ((u : ℤ_[ℓ]) * ↑u⁻¹) * t * (ℓ : ℤ_[ℓ]) ^ v by ring, Units.mul_inv, one_mul]
  have h3 : w - y ∈ H := h2 ▸ mul_mem_of_isClosed H hH hx _
  have := H.add_mem h3 hy
  rwa [sub_add_cancel] at this

theorem infinite_of_ne_zero (H : AddSubgroup ℤ_[ℓ]) {x : ℤ_[ℓ]} (hx : x ∈ H) (hx0 : x ≠ 0) :
    (H : Set ℤ_[ℓ]).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun k : ℕ => k • x)
    (fun a b hab => by
      simp only [nsmul_eq_mul] at hab
      exact Nat.cast_injective (mul_right_cancel₀ hx0 hab))
    fun k => H.nsmul_mem hx k

end Padic

section ProfiniteInteger

def factorialPNat (n : ℕ) : ℕ+ := ⟨(n + 1).factorial, Nat.factorial_pos _⟩

theorem tendsto_natCast (a : ℤ̂) :
    Tendsto (fun n : ℕ => (((ProfiniteInteger.proj (factorialPNat n) a).val : ℕ) : ℤ̂)) atTop
      (𝓝 a) := by
  rw [tendsto_subtype_rng, tendsto_pi_nhds]
  intro m
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [eventually_ge_atTop (m : ℕ)] with n hn
  have hdvd : (m : ℕ) ∣ (factorialPNat n : ℕ) := Nat.dvd_factorial m.pos (by omega)
  have h := ProfiniteInteger.castHom_proj hdvd a
  rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
  simp only [ProfiniteInteger.proj_apply] at h
  rw [← h]
  rfl

theorem denseRange_natCast : DenseRange (Nat.cast : ℕ → ℤ̂) := fun a =>
  mem_closure_of_tendsto (tendsto_natCast a) (Eventually.of_forall fun _ => Set.mem_range_self _)

theorem mul_mem_of_isClosed' (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂)) {x : ℤ̂}
    (hx : x ∈ H) (a : ℤ̂) : a * x ∈ H :=
  denseRange_natCast.induction_on a (hH.preimage (continuous_id.mul continuous_const))
    fun k => by
      show (k : ℤ̂) * x ∈ H
      rw [← nsmul_eq_mul]
      exact H.nsmul_mem hx k

def idealOfIsClosed (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂)) : Ideal ℤ̂ where
  carrier := H
  add_mem' := H.add_mem
  zero_mem' := H.zero_mem
  smul_mem' a _ hx := mul_mem_of_isClosed' H hH hx a

noncomputable def primeIdempotent (q : Nat.Primes) : ℤ̂ :=
  ofPadics (Pi.single q 1)

theorem toPadicInt_primeIdempotent (q q' : Nat.Primes) :
    toPadicInt q' (primeIdempotent q) = Pi.single (M := fun q : Nat.Primes => ℤ_[q]) q 1 q' :=
  congrFun (toPadics_ofPadics _) q'

theorem toPadicInt_surjective (q : Nat.Primes) : Function.Surjective (toPadicInt q) := fun z =>
  ⟨ofPadics (Pi.single q z), by
    rw [← toPadics_apply, toPadics_ofPadics, Pi.single_eq_same]⟩

theorem mem_of_forall_toPadicInt (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂)) {y : ℤ̂}
    (hy : ∀ q : Nat.Primes, ∃ h ∈ H, toPadicInt q h = toPadicInt q y) : y ∈ H := by
  choose h hh hhy using hy
  let s : Finset Nat.Primes → ℤ̂ := fun F => ∑ q ∈ F, primeIdempotent q * h q
  have hs : ∀ F, s F ∈ H := fun F =>
    H.sum_mem fun q _ => mul_mem_of_isClosed' H hH (hh q) _
  have hcomp : ∀ (F : Finset Nat.Primes) (q' : Nat.Primes), toPadicInt q' (s F) = if q' ∈ F then toPadicInt q' y else 0 := by
    intro F q'
    simp only [s, map_sum, map_mul, toPadicInt_primeIdempotent]
    split_ifs with hq'
    · rw [Finset.sum_eq_single q', Pi.single_eq_same, one_mul, hhy]
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb.symm, zero_mul]
      · intro h'; exact absurd hq' h'
    · refine Finset.sum_eq_zero fun b hb => ?_
      rw [Pi.single_eq_of_ne (by rintro rfl; exact hq' hb), zero_mul]
  have ht : Tendsto (fun F => toPadics (s F)) atTop (𝓝 (toPadics y)) := by
    rw [tendsto_pi_nhds]
    intro q'
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [eventually_ge_atTop {q'}] with F hF
    rw [toPadics_apply, hcomp, if_pos (Finset.singleton_subset_iff.1 hF), toPadics_apply]
  have ht' := (continuous_ofPadics.tendsto _).comp ht
  simp only [Function.comp_def, ofPadics_toPadics] at ht'
  exact hH.mem_of_tendsto ht' (Eventually.of_forall hs)

theorem exists_eq_mul_of_isClosed (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂))
    (hne : ∀ q : Nat.Primes, ∃ h ∈ H, toPadicInt q h ≠ 0) :
    ∃ g : ℤ̂, (∀ q : Nat.Primes, toPadicInt q g ≠ 0) ∧ ∀ y, y ∈ H ↔ ∃ a, y = g * a := by
  let I : Ideal ℤ̂ := idealOfIsClosed H hH
  have hI : ∀ q : Nat.Primes, I.map (toPadicInt q) ≠ ⊥ := by
    intro q hbot
    obtain ⟨h, hh, hh0⟩ := hne q
    apply hh0
    have : toPadicInt q h ∈ I.map (toPadicInt q) := Ideal.mem_map_of_mem _ hh
    rwa [hbot, Ideal.mem_bot] at this
  choose v hv using fun q => PadicInt.ideal_eq_span_pow_p (hI q)
  have hmem : ∀ (q : Nat.Primes) (z : ℤ_[q]), (∃ h ∈ H, toPadicInt q h = z) ↔ (q : ℤ_[q]) ^ v q ∣ z := by
    intro q z
    rw [← Ideal.mem_span_singleton, ← hv q, Ideal.mem_map_iff_of_surjective _
      (toPadicInt_surjective q)]
    rfl
  let g : ℤ̂ := ofPadics fun q => (q : ℤ_[q]) ^ v q
  have hg : ∀ q : Nat.Primes, toPadicInt q g = (q : ℤ_[q]) ^ v q := fun q =>
    congrFun (toPadics_ofPadics _) q
  refine ⟨g, fun q => by rw [hg]; exact pow_ne_zero _ (Nat.cast_ne_zero.2 q.2.ne_zero), ?_⟩
  intro y
  constructor
  · intro hy
    choose t ht using fun q => (hmem q (toPadicInt q y)).1 ⟨y, hy, rfl⟩
    refine ⟨ofPadics t, ext_toPadicInt fun q => ?_⟩
    rw [map_mul, hg, ht q]
    congr 1
    exact (congrFun (toPadics_ofPadics t) q).symm
  · rintro ⟨a, rfl⟩
    have hgH : g ∈ H := mem_of_forall_toPadicInt H hH fun q =>
      (hmem q _).2 (by rw [hg])
    rw [mul_comm]
    exact mul_mem_of_isClosed' H hH hgH a

theorem nonempty_addEquiv_of_isClosed (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂))
    (hne : ∀ q : Nat.Primes, ∃ h ∈ H, toPadicInt q h ≠ 0) : Nonempty (H ≃+ ℤ̂) := by
  obtain ⟨g, hg0, hgH⟩ := exists_eq_mul_of_isClosed H hH hne
  let f : ℤ̂ →+ H :=
    { toFun := fun a => ⟨g * a, (hgH _).2 ⟨a, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp [mul_add] }
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ext_toPadicInt fun q => ?_, fun y => ?_⟩
    · have := congrArg (fun z : H => toPadicInt q (z : ℤ̂)) hab
      simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul] at this
      exact mul_left_cancel₀ (hg0 q) this
    · obtain ⟨a, ha⟩ := (hgH y).1 y.2
      exact ⟨a, Subtype.ext ha.symm⟩
  exact ⟨(AddEquiv.ofBijective f hf).symm⟩

end ProfiniteInteger

end Cyclotomic

end GroundTheory.Global

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

noncomputable section

open IsDedekindDomain
namespace GlobalTheory.CompatLim

theorem norm_sub_le_of_dvd (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) (x y : ℤ) (h : ((ℓ ^ k : ℕ) : ℤ) ∣ x - y) :
    ‖((x : ℤ_[ℓ]) - (y : ℤ_[ℓ]))‖ ≤ (ℓ : ℝ) ^ (-(k : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
  obtain ⟨c, hc⟩ := h
  refine ⟨(c : ℤ_[ℓ]), ?_⟩
  have := congrArg (fun z : ℤ => (z : ℤ_[ℓ])) hc
  push_cast at this
  rw [← this]

theorem exists_padicInt_lim (p ℓ : ℕ) [Fact ℓ.Prime] (hp : p.Prime) (hne : ℓ ≠ p) (a : ℕ → ℤ)
    (ha : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ a (n * m) - a n) :
    ∃ L : ℤ_[ℓ], ∀ n : ℕ, 0 < n → n.Coprime p → ∃ b : ℤ_[ℓ], L = (a n : ℤ_[ℓ]) + (n : ℤ_[ℓ]) * b := by
  have hℓ : ℓ.Prime := Fact.out
  have hcop : ∀ k, (ℓ ^ k).Coprime p := fun k => Nat.Coprime.pow_left k ((Nat.coprime_primes hℓ hp).2 hne)
  have hpos : ∀ k, 0 < ℓ ^ k := fun k => pow_pos hℓ.pos k

  have key : ∀ k m, k ≤ m → ((ℓ ^ k : ℕ) : ℤ) ∣ a (ℓ ^ m) - a (ℓ ^ k) := by
    intro k m hkm
    have h := ha (ℓ ^ k) (ℓ ^ (m - k)) (hpos k) (hpos _) (by rw [← pow_add, Nat.add_sub_cancel' hkm]; exact hcop m)
    rwa [← pow_add, Nat.add_sub_cancel' hkm] at h
  set s : ℕ → ℤ_[ℓ] := fun k => (a (ℓ ^ k) : ℤ_[ℓ]) with hs
  have hdist : ∀ k m, k ≤ m → dist (s m) (s k) ≤ (ℓ : ℝ) ^ (-(k : ℤ)) := by
    intro k m hkm
    rw [dist_eq_norm]
    exact norm_sub_le_of_dvd ℓ k _ _ (key k m hkm)
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.one_lt
  have hcs : CauchySeq s := by
    refine cauchySeq_of_le_geometric ((ℓ : ℝ)⁻¹) 1 (inv_lt_one_of_one_lt₀ hℓ1) fun k => ?_
    rw [dist_comm, _root_.one_mul, inv_pow, ← zpow_natCast, ← zpow_neg]
    exact hdist k (k + 1) (Nat.le_succ k)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  have hLk : ∀ k, ‖L - s k‖ ≤ (ℓ : ℝ) ^ (-(k : ℤ)) := by
    intro k
    have hmem : L ∈ Metric.closedBall (s k) ((ℓ : ℝ) ^ (-(k : ℤ))) :=
      Metric.isClosed_closedBall.mem_of_tendsto hL
        (Filter.eventually_atTop.2 ⟨k, fun m hm => Metric.mem_closedBall.2 (hdist k m hm)⟩)
    rwa [Metric.mem_closedBall, dist_eq_norm] at hmem
  refine ⟨L, fun n hn hnp => ?_⟩
  set e := n.factorization ℓ
  set m := n / ℓ ^ e
  have hnm : ℓ ^ e * m = n := Nat.ordProj_mul_ordCompl_eq_self n ℓ
  have hm : ℓ.Coprime m := Nat.coprime_ordCompl hℓ hn.ne'
  have hmpos : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hnm; omega

  have h1 : L - s e ∈ Ideal.span {(ℓ : ℤ_[ℓ]) ^ e} := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 (hLk e)

  have h2 := ha (ℓ ^ e) m (hpos e) hmpos (by rw [hnm]; exact hnp)
  rw [hnm] at h2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 h1
  obtain ⟨d, hd⟩ := h2
  have hu : IsUnit (m : ℤ_[ℓ]) := PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hm)
  obtain ⟨u, hu⟩ := hu
  refine ⟨(u⁻¹ : ℤ_[ℓ]ˣ) * (c - (d : ℤ_[ℓ])), ?_⟩
  have hd' : (a n : ℤ_[ℓ]) - s e = (ℓ : ℤ_[ℓ]) ^ e * d := by
    have := congrArg (fun z : ℤ => (z : ℤ_[ℓ])) hd
    push_cast at this
    simpa [hs] using this
  have hn' : (n : ℤ_[ℓ]) = (ℓ : ℤ_[ℓ]) ^ e * u := by
    rw [hu, ← hnm]; push_cast; ring
  rw [hn']
  have : (ℓ : ℤ_[ℓ]) ^ e * (u : ℤ_[ℓ]) * ((u⁻¹ : ℤ_[ℓ]ˣ) * (c - d)) = (ℓ : ℤ_[ℓ]) ^ e * (c - d) := by
    rw [_root_.mul_assoc, ← _root_.mul_assoc (u : ℤ_[ℓ]), Units.mul_inv, _root_.one_mul]
  rw [this]
  linear_combination hc - hd'

open Rat.HeightOneSpectrum in
theorem natGenerator_ne (p : ℕ) (v : AwayP p) : (primesEquiv v.1 : ℕ) ≠ p := by
  obtain ⟨w, hw⟩ := v
  intro h
  apply hw
  have hs := span_natGenerator (R := ℤ) w
  change natGenerator w = p at h
  rw [h] at hs
  rw [hs]
  ext x
  rw [Ideal.mem_map_of_equiv]
  simp [eq_intCast]

open Rat.HeightOneSpectrum in

theorem exists_integer_lim (p : ℕ) [hp : Fact p.Prime] (a : ℕ → ℤ)
    (ha : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ a (n * m) - a n) (v : AwayP p) :
    ∃ x : v.1.adicCompletionIntegers ℚ, ∀ n : ℕ, 0 < n → n.Coprime p →
      ∃ b : v.1.adicCompletionIntegers ℚ, x = (a n : v.1.adicCompletionIntegers ℚ) + (n : v.1.adicCompletionIntegers ℚ) * b := by
  haveI : Fact (primesEquiv v.1 : ℕ).Prime := ⟨(primesEquiv v.1).2⟩
  obtain ⟨L, hL⟩ := exists_padicInt_lim p (primesEquiv v.1 : ℕ) hp.out (natGenerator_ne p v) a ha
  let e := (RingEquivClass.toRingEquiv (adicCompletionIntegers.padicIntEquiv (R := ℤ) v.1)).symm
  refine ⟨e L, fun n hn hnp => ?_⟩
  obtain ⟨b, hb⟩ := hL n hn hnp
  refine ⟨e b, ?_⟩
  rw [hb, map_add, map_mul, map_intCast, map_natCast]

theorem exists_lim : ∀ (p : ℕ) [Fact p.Prime] (a : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ a (n * m) - a n) → ∃ α : AfP p, IsIntAf α ∧ ∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ α = (a n : AfP p) + n • β := by
  intro p _ a ha
  choose x hx using exists_integer_lim p a ha
  let α : AfP p := RestrictedProduct.mk (fun v => (x v : v.1.adicCompletion ℚ)) (Filter.Eventually.of_forall fun v => (x v).2)
  refine ⟨α, fun v => (x v).2, fun n hn hnp => ?_⟩
  choose b hb using fun v => hx v n hn hnp
  let β : AfP p := RestrictedProduct.mk (fun v => (b v : v.1.adicCompletion ℚ)) (Filter.Eventually.of_forall fun v => (b v).2)
  refine ⟨β, fun v => (b v).2, ?_⟩
  apply RestrictedProduct.ext
  intro v
  have h1 : AfP.eval v α = x v := rfl
  have h2 : AfP.eval v β = b v := rfl
  have h3 : AfP.eval v ((a n : AfP p) + n • β) = (a n : v.1.adicCompletion ℚ) + (n : v.1.adicCompletion ℚ) * b v := by
    rw [map_add, map_intCast, map_nsmul, h2, nsmul_eq_mul]
  change AfP.eval v α = AfP.eval v ((a n : AfP p) + n • β)
  rw [h3, h1, hb v]
  push_cast
  rfl

end GlobalTheory.CompatLim

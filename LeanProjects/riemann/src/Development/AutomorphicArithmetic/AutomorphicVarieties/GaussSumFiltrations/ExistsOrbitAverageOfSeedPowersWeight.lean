import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.SlashAddSmulPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertHolomorphicUnnormalizedSlashOfPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertModerateGrowthUnnormalizedSlash
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashRationalMatrixProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSeedOrbitFiniteAndCongruence
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertQExpPadicCongruencePowPrimePow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertQExpPadicBoundAlgebraProperties
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.OrbitAvg

section Gen

variable {F : Type} [Field F] [NumberField F]

theorem sl_sum (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) {α : Type} (T : Finset α) (u : α → Hn F → ℂ) :
    sl k h (∑ a ∈ T, u a) = ∑ a ∈ T, sl k h (u a) := by
  funext z; simp only [sl, sl0, Finset.sum_apply, Finset.mul_sum]

theorem det_free_slash_finset_sum (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) {α : Type} (T : Finset α) (u : α → Hn F → ℂ) :
    sl0 k h (∑ a ∈ T, u a) = ∑ a ∈ T, sl0 k h (u a) := by
  funext z; simp only [sl0, Finset.sum_apply, Finset.mul_sum]

theorem hol_pow {f : Hn F → ℂ} (hf : Hol f) (M : ℕ) : Hol (f ^ M) := by
  induction M with
  | zero => rw [pow_zero]; exact differentiableOn_const _
  | succ n ih => rw [pow_succ]; exact (HolKeep.main F 0 _ _ 0 ih hf).2.2.1

theorem hol_sum {α : Type} (T : Finset α) (u : α → Hn F → ℂ) (hu : ∀ a ∈ T, Hol (u a)) :
    Hol (∑ a ∈ T, u a) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact differentiableOn_const _
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    exact (HolKeep.main F 0 _ _ 0 (hu a (Finset.mem_insert_self a T))
      (ih fun b hb => hu b (Finset.mem_insert_of_mem hb))).1

theorem gr_pow {f : Hn F → ℂ} (hf : Gr f) (M : ℕ) : Gr (f ^ M) := by
  induction M with
  | zero => rw [pow_zero]; exact Growth.gr_const 1
  | succ n ih => rw [pow_succ]; exact Growth.gr_mul ih hf

theorem gr_sum {α : Type} (T : Finset α) (u : α → Hn F → ℂ) (hu : ∀ a ∈ T, Gr (u a)) :
    Gr (∑ a ∈ T, u a) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Growth.gr_const 0
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    exact Growth.gr_add (hu a (Finset.mem_insert_self a T)) (ih fun b hb => hu b (Finset.mem_insert_of_mem hb))

end Gen

section Small

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ)

theorem small_zero {s : ℝ} (hs : 0 ≤ s) : Small ι s (0 : Hn F → ℂ) := by
  refine ⟨0, ⟨⟨1, one_pos, fun ξ h => absurd rfl h⟩, fun z => ?_⟩, fun ξ => ?_⟩
  · simpa using (hasSum_zero : HasSum (fun _ : F => (0 : ℂ)) 0)
  · simpa using hs

theorem small_sum' {α : Type} (T : Finset α) (u : α → Hn F → ℂ) {r : ℝ} (hz : Small ι r (0 : Hn F → ℂ))
    (hu : ∀ a ∈ T, Small ι r (u a)) : Small ι r (∑ a ∈ T, u a) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact hz
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := hu a (Finset.mem_insert_self a T)
    have h2 := ih fun b hb => hu b (Finset.mem_insert_of_mem hb)
    simpa using (GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι r r _ _ 0 h1 h2).1

theorem small_sum {α : Type} (T : Finset α) (u : α → Hn F → ℂ) {r : ℝ} (hT : T.Nonempty)
    (hu : ∀ a ∈ T, Small ι r (u a)) : Small ι r (∑ a ∈ T, u a) := by
  obtain ⟨a0, ha0⟩ := hT
  have hr : 0 ≤ r := (GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι r r _ _ 0 (hu a0 ha0) (hu a0 ha0)).2.2.2.2.1
  exact small_sum' ι T u (small_zero ι hr) hu

end Small

theorem norm_natCast_inv_le (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : n ≠ 0) :
    ‖((n : Qbar p))⁻¹‖ ≤ (p : ℝ) ^ (n.factorization p) := by
  have e : ((n : ℕ) : Qbar p) = algebraMap ℚ_[p] (PadicAlgCl p) (n : ℚ_[p]) := (map_natCast _ n).symm
  have h1 := Nat.ordProj_mul_ordCompl_eq_self n p
  have hc : ‖((ordCompl[p] n : ℕ) : ℚ_[p])‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff).2 (Nat.coprime_ordCompl hp.out hn)
  have h2 : ‖(n : ℚ_[p])‖ = (p : ℝ) ^ (-(n.factorization p : ℤ)) := by
    conv_lhs => rw [← h1]
    rw [Nat.cast_mul, norm_mul, hc, mul_one, Nat.cast_pow, Padic.norm_p_pow]
  rw [norm_inv, e, PadicAlgCl.norm_extends, h2, zpow_neg, inv_inv, zpow_natCast]

end GlobalTheory.HilbertThetaSeries.OrbitAvg

namespace GlobalTheory.HilbertThetaSeries.OrbitAvg

theorem sl_cancel {F : Type} [Field F] [NumberField F] (k : ℕ) (h h' : GL (Fin 2) (InfinitePlace F → ℝ))
    (hh : Pos h) (hh' : Pos h') (e : h * h' = 1) (f : Hn F → ℂ) : sl k h' (sl k h f) = f := by
  have H := SlashCocycle.slash_cocycle F k h h' f hh hh'
  rw [← H.2.2.2.1, e, H.2.2.2.2.2]

theorem avg_pow : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ θ : Hn F → ℂ, Seed ι δ θ → ∀ y : (Af F)ˣ, AtP p δ y → ∃ N : ℕ, ∀ M : ℕ, p ^ N ∣ M → ∃ f : Hn F → ℂ, Comp ι δ ((p - 1) * M) (aff y 0) f := by
  intro F _ _ _ p _ ι hp2 δ hδ θ hθ y hy
  classical
  obtain ⟨hfin, hone, h1, hgrp⟩ := GlobalTheory.T.hilbert_seed_orbit_finite_and_congruence F p ι hp2 δ hδ θ hθ y hy
  set g0 := aff y (0 : Af F) with hg0
  set T := hfin.toFinset with hT
  have hmem : ∀ g, g ∈ T ↔ ∃ γ, Stab g0 γ ∧ g = sl (p - 1) (toInf γ) θ := fun g => by
    rw [hT, Set.Finite.mem_toFinset]; rfl
  have hpos : ∀ γ, Stab g0 γ → Pos (toInf γ) := fun γ hγ => ((GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash F 0 θ).2.1 γ).1.2 hγ.1
  have hθT : sl (p - 1) (toInf 1) θ ∈ T := (hmem _).2 ⟨1, h1, rfl⟩
  have hTne : T.Nonempty := ⟨_, hθT⟩
  have hcard : (T.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hTne)

  have hmap : ∀ γ, Stab g0 γ → ∀ g ∈ T, sl (p - 1) (toInf γ) g ∈ T := by
    intro γ hγ g hg
    obtain ⟨γ', hγ', rfl⟩ := (hmem g).1 hg
    refine (hmem _).2 ⟨γ' * γ, (hgrp γ' γ hγ' hγ).1, ?_⟩
    rw [map_mul, (SlashCocycle.slash_cocycle F (p - 1) _ _ θ (hpos γ' hγ') (hpos γ hγ)).2.2.2.1]
  have hperm : ∀ γ, Stab g0 γ → ∀ M : ℕ, ∑ g ∈ T, (sl (p - 1) (toInf γ) g) ^ M = ∑ g ∈ T, g ^ M := by
    intro γ hγ M
    have hγi := (hgrp γ γ hγ hγ).2
    refine Finset.sum_nbij' (fun g => sl (p - 1) (toInf γ) g) (fun g => sl (p - 1) (toInf γ⁻¹) g)
      (fun g hg => hmap γ hγ g hg) (fun g hg => hmap γ⁻¹ hγi g hg) (fun g _ => ?_) (fun g _ => ?_) (fun g _ => rfl)
    · exact sl_cancel _ _ _ (hpos γ hγ) (hpos _ hγi) (by rw [← map_mul, mul_inv_cancel, map_one]) g
    · exact sl_cancel _ _ _ (hpos _ hγi) (hpos γ hγ) (by rw [← map_mul, inv_mul_cancel, map_one]) g
  have hholT : ∀ g ∈ T, Hol g := by
    intro g hg
    obtain ⟨γ, hγ, rfl⟩ := (hmem g).1 hg
    exact (HolKeep.main F (p - 1) θ θ 0 hθ.hol hθ.hol).2.2.2.2.2 _ (hpos γ hγ) |>.2
  have hgrT : ∀ g ∈ T, Gr g := by
    intro g hg
    obtain ⟨γ, hγ, rfl⟩ := (hmem g).1 hg
    exact Growth.gr_sl _ _ hθ.gr
  refine ⟨T.card.factorization p, ?_⟩
  rintro M ⟨m, rfl⟩
  set c : ℂ := (T.card : ℂ)⁻¹ with hc
  refine ⟨c • ∑ g ∈ T, g ^ (p ^ T.card.factorization p * m), ?_, ?_, ?_, ?_⟩
  · exact (HolKeep.main F 0 _ θ c
      (hol_sum T (fun g => g ^ (p ^ T.card.factorization p * m)) fun g hg => hol_pow (hholT g hg) _) hθ.hol).2.1
  · exact Growth.gr_smul c (gr_sum T (fun g => g ^ (p ^ T.card.factorization p * m)) fun g hg => gr_pow (hgrT g hg) _)
  · intro γ hγ
    have L := fun (f : Hn F → ℂ) => GlobalTheory.HilbertThetaSeries.slash_add_smul_pow F (p - 1) (p ^ T.card.factorization p * m) (toInf γ) f f c
    rw [(GlobalTheory.HilbertThetaSeries.slash_add_smul_pow F _ 0 (toInf γ) _ θ c).2.2.2.2.1, sl_sum]
    congr 1
    rw [← hperm γ hγ]
    exact Finset.sum_congr rfl fun g _ => (L g).2.2.2.2.2
  · intro γ hγ
    set N := T.card.factorization p
    have L := fun (f : Hn F → ℂ) => GlobalTheory.HilbertThetaSeries.slash_add_smul_pow F (p - 1) (p ^ N * m) (toInf γ) f f c
    have e : sl0 ((p - 1) * (p ^ N * m)) (toInf γ) (c • ∑ g ∈ T, g ^ (p ^ N * m)) - 1 =
        c • ∑ g ∈ T, ((sl0 (p - 1) (toInf γ) g) ^ (p ^ N * m) - 1) := by
      rw [(GlobalTheory.HilbertThetaSeries.slash_add_smul_pow F _ 0 (toInf γ) _ θ c).2.1, det_free_slash_finset_sum, Finset.sum_congr rfl fun g _ => (L g).2.2.1, Finset.sum_sub_distrib, smul_sub,
        Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc, inv_mul_cancel₀ hcard, one_smul]
    rw [e]
    have hS : Small ι ((p : ℝ)⁻¹ ^ (N + 1)) (∑ g ∈ T, ((sl0 (p - 1) (toInf γ) g) ^ (p ^ N * m) - 1)) := by
      refine small_sum ι T _ hTne fun g hg => ?_
      obtain ⟨γ', hγ', rfl⟩ := (hmem g).1 hg
      exact GlobalTheory.T.hilbertQExp_padicCongruence_pow_prime_pow F p ι _ (hone γ' hγ' γ hγ) N m
    have H := (GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι _ _ _ _ c hS hS).2.2.1
    have hθ1 := hone 1 h1 γ hγ
    refine (GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι _ _ _ _ c H hθ1).2.2.2.1 ?_
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    have hn : ‖ι.symm c‖ ≤ (p : ℝ) ^ N := by
      rw [hc, map_inv₀, map_natCast]
      exact norm_natCast_inv_le p T.card (Finset.card_ne_zero.2 hTne)
    calc ‖ι.symm c‖ * (p : ℝ)⁻¹ ^ (N + 1) ≤ (p : ℝ) ^ N * (p : ℝ)⁻¹ ^ (N + 1) :=
          mul_le_mul_of_nonneg_right hn (by positivity)
      _ = (p : ℝ)⁻¹ := by rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hp0.ne', one_pow, one_mul]

end GlobalTheory.HilbertThetaSeries.OrbitAvg

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orbit_average_of_seed_powers_weight : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ θ : Hn F → ℂ, Seed ι δ θ → ∀ y : (Af F)ˣ, AtP p δ y → ∃ N : ℕ, ∀ M : ℕ, p ^ N ∣ M → ∃ f : Hn F → ℂ, Comp ι δ ((p - 1) * M) (aff y 0) f := by
  first | exact @GlobalTheory.HilbertThetaSeries.OrbitAvg.avg_pow | exact GlobalTheory.HilbertThetaSeries.OrbitAvg.avg_pow | (intros; apply GlobalTheory.HilbertThetaSeries.OrbitAvg.avg_pow <;> assumption)

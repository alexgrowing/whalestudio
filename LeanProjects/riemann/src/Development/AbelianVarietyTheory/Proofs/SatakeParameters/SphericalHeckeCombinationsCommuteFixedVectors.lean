import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiInvolutionOfChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphLabelComm

section Abstract

variable {G : Type} [Group G]

theorem isDC_of_reps {K : Subgroup G} {x : G} {A : Finset G} (h : GlobalTheory.SphLabelOps.Reps K x A) :
    Formalism.IndefR.Bridge.IsDC K x A := by
  refine ⟨fun a ha => ?_, fun g hg => h.2 g ?_⟩
  · obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h.1 a ha
    exact ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩, rfl⟩
  · obtain ⟨k₁, k₂, rfl⟩ := hg
    exact ⟨k₁, k₁.2, k₂, k₂.2, rfl⟩

theorem sum_comm_of_antiInv (K L : Subgroup G) (hKL : K ≤ L) (θ : G → G)
    (t1 : ∀ g ∈ L, θ g ∈ L) (t2 : ∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) (t3 : ∀ x ∈ L, θ (θ x) = x)
    (t4 : ∀ k ∈ K, θ k ∈ K) (t5 : ∀ g ∈ L, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b)
    {x y : G} (hx : x ∈ L) (hy : y ∈ L) {A B A' : Finset G}
    (hA : GlobalTheory.SphLabelOps.Reps K x A) (hB : GlobalTheory.SphLabelOps.Reps K y B) (hA' : GlobalTheory.SphLabelOps.Reps K x⁻¹ A')
    {M : Type} [AddCommGroup M] [Module ℂ M] (π : G →* Module.End ℂ M) (u : M) (hu : ∀ k ∈ K, π k u = u) :
    ∑ a ∈ A, π a (∑ b ∈ B, π b u) = ∑ b ∈ B, π b (∑ a ∈ A, π a u) := by
  have memL : ∀ {z : G} {R : Finset G}, GlobalTheory.SphLabelOps.Reps K z R → z ∈ L → ∀ a ∈ R, a ∈ L := by
    intro z R hR hz a ha
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hR.1 a ha
    exact mul_mem (mul_mem (hKL h₁) hz) (hKL h₂)
  have hθ : ∃ θ : G → G, (∀ g ∈ L, θ g ∈ L) ∧ (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧
      (∀ x ∈ L, θ (θ x) = x) ∧ (∀ k ∈ K ⊓ L, θ k ∈ K) ∧ ∀ g ∈ L, ∃ a ∈ K ⊓ L, ∃ b ∈ K ⊓ L, θ g = a * g * b := by
    refine ⟨θ, t1, t2, t3, fun k hk => t4 k hk.1, fun g hg => ?_⟩
    obtain ⟨a, ha, b, hb, e⟩ := t5 g hg
    exact ⟨a, ⟨ha, hKL ha⟩, b, ⟨hb, hKL hb⟩, e⟩
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have hF : ∀ (k : K) (h : G), (fun g => φ (π g u)) (h * k) = ((1 : K →* ℂˣ) k : ℂ) • (fun g => φ (π g u)) h := by
    intro k h
    simp [map_mul, Module.End.mul_apply, hu k k.2]
  have key := (GlobalTheory.DoubleCosetComm.dcOp_comm_and_card (W := ℂ) K L 1 x y A B A' (fun g => φ (π g u))
    (fun k hk => ⟨k, hk, 1, one_mem _, hKL hk, (mul_one k).symm, fun l _ => Commute.one_left l⟩)
    (fun k _ => rfl) hθ (memL hA hx) (memL hB hy) (memL hA' (inv_mem hx)) (isDC_of_reps hA) (isDC_of_reps hB)
    (isDC_of_reps hA') hF).1
  have e := congrFun key 1
  simp only [Formalism.IndefR.Bridge.dcOp, one_mul, map_mul, Module.End.mul_apply] at e
  simp only [map_sub, map_sum, LinearMap.zero_apply]
  rw [sub_eq_zero]
  exact e

theorem comb_comm {ι M : Type} [AddCommGroup M] [Module ℂ M] (S : ι → Module.End ℂ M) (u : M)
    (h : ∀ i j, S i (S j u) = S j (S i u)) (c c' : ι →₀ ℂ) :
    (c.sum fun i z => z • S i) ((c'.sum fun i z => z • S i) u) =
      (c'.sum fun i z => z • S i) ((c.sum fun i z => z • S i) u) := by
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [h i j, smul_comm]

end Abstract

open GlobalTheory.IdemSupport in

theorem label_ops_comm : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ c c', ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P c (opOf π P c' u) = opOf π P c' (opOf π P c u) := by
  intro D V P c c' M _ _ π u hu
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  obtain ⟨e, f, h⟩ := (supported_group_and_prime_idempotents V).2.1 P
  have h0 := (supported_group_and_prime_idempotents V).2.2.1 P e f h
  obtain ⟨L, hL⟩ := ((supported_group_and_prime_idempotents V).1 f h0.1 h0.2.1).1
  have memK : ∀ k, k ∈ K ↔ k ∈ KsphC V ∅ ∧ SuppF V f k := fun k => by
    rw [← SetLike.mem_coe, ← hK, GlobalTheory.SphLabelOps.hyp_eq h]
    rfl
  have hKL : K ≤ L := fun k hk => (hL k).2 ((memK k).1 hk).2
  obtain ⟨θ, t1, t2, t3, t4, t5⟩ : ∃ θ : GA D V → GA D V, (∀ g ∈ L, θ g ∈ L) ∧
      (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧ (∀ x ∈ L, θ (θ x) = x) ∧ (∀ k ∈ K, θ k ∈ K) ∧
      ∀ g ∈ L, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b := by
    rcases id h with ⟨hs, rfl⟩ | ⟨rfl, -⟩
    · obtain ⟨θ, s1, s2, s3, s4, s5⟩ := (GlobalTheory.SplitPlace.split_local V P e hs).1
      refine ⟨θ, fun g hg => (hL _).2 (s1 g ((hL g).1 hg)), fun x hx y hy => s2 x y ((hL x).1 hx) ((hL y).1 hy),
        fun x hx => s3 x ((hL x).1 hx), fun k hk => ?_, fun g hg => ?_⟩
      · have hk' := (memK k).1 hk
        exact (memK _).2 ⟨s4 k hk', s1 k hk'.2⟩
      · obtain ⟨a, ha, b, hb, eq⟩ := s5 g ((hL g).1 hg)
        exact ⟨a, (memK a).2 ha, b, (memK b).2 hb, eq⟩
    · refine ⟨fun g => g⁻¹, fun g hg => inv_mem hg, fun x _ y _ => mul_inv_rev x y, fun x _ => inv_inv x,
        fun k hk => inv_mem hk, fun g hg => ?_⟩
      obtain ⟨a, b, ha, ha', hb, hb', eq⟩ := (GlobalTheory.InertDoubleCoset.inert_double_cosets V P _ h
        (GlobalTheory.SphLabelOps.exists_real_unif D P) g ((hL g).1 hg)).1
      exact ⟨a, (memK a).2 ⟨ha, ha'⟩, b, (memK b).2 ⟨hb, hb'⟩, eq⟩
  have reps : ∀ d, IsLab V P d → ∃ x ∈ L, GlobalTheory.SphLabelOps.Reps K x (rep V P d) ∧
      ∃ A', GlobalTheory.SphLabelOps.Reps K x⁻¹ A' := by
    intro d hd
    have hR := GlobalTheory.SphLabelOps.sphOp_rep hd
    obtain ⟨e', f', ϖ, α, -, h', h1, h2, -, -, -, hα, hD, -⟩ := id hR
    obtain ⟨rfl, rfl⟩ := h0.2.2.2.1 e' f' h'
    have hαL : α ∈ L := (hL α).2 hα
    refine ⟨α, hαL, GlobalTheory.SphLabelOps.reps_of_sphOp hK h' h1 h2 hα hD hR, ?_⟩
    obtain ⟨R', hR', -⟩ := GlobalTheory.SphLabelOps.exists_dual hR
    have he := (GlobalTheory.HeckeDual.idem_of_isPrimeIdem h').1
    exact ⟨R', GlobalTheory.SphLabelOps.reps_of_sphOp hK h' h1 h2 ((hL _).1 (inv_mem hαL))
      (GlobalTheory.DivDual.divAt_inv_and_mul V _ _ d α he (GlobalTheory.SphLabelOps.unif_ne_zero h2) hD).1 hR'⟩
  have key : ∀ d d', (∑ γ ∈ rep V P d, π γ) ((∑ δ ∈ rep V P d', π δ) u) =
      (∑ δ ∈ rep V P d', π δ) ((∑ γ ∈ rep V P d, π γ) u) := by
    intro d d'
    by_cases hd : IsLab V P d
    swap
    · simp [Hk3.rep, dif_neg hd]
    by_cases hd' : IsLab V P d'
    swap
    · simp [Hk3.rep, dif_neg hd']
    obtain ⟨x, hx, rA, A', rA'⟩ := reps d hd
    obtain ⟨y, hy, rB, -⟩ := reps d' hd'
    simp only [LinearMap.sum_apply]
    exact sum_comm_of_antiInv K L hKL θ t1 t2 t3 t4 t5 hx hy rA rB rA' π u
      (fun k hk => hu k (by rw [hK]; exact hk))
  exact comb_comm (fun d => ∑ γ ∈ rep V P d, π γ) u key c c'

end GlobalTheory.SphLabelComm

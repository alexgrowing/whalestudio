import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

namespace HeckeTraceForms

variable {Γ H V : Type} [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V]

def forms (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) : Submodule ℂ (H → V) where
  carrier := {φ | (∀ γ g, φ (ι γ * g) = ξ γ (φ g)) ∧ ∀ k ∈ K, ∀ g, φ (g * k) = φ g}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun γ g => by simp [ha1, hb1], fun k hk g => by simp [ha2 k hk, hb2 k hk]⟩
  zero_mem' := ⟨fun γ g => by simp, fun k hk g => by simp⟩
  smul_mem' := by
    rintro c a ⟨h1, h2⟩
    exact ⟨fun γ g => by simp [h1], fun k hk g => by simp [h2 k hk]⟩

def IsHecke (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (F : H → ℂ)
    (T : forms ι K ξ →ₗ[ℂ] forms ι K ξ) : Prop :=
  ∀ φ g, (T φ : H → V) g = ∑ᶠ h : H ⧸ K, F h.out • (φ : H → V) (g * h.out)

def heckeTrace (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (F : H → ℂ) : ℂ :=
  if h : ∃ T, IsHecke ι K ξ F T then LinearMap.trace ℂ (forms ι K ξ) h.choose else 0

theorem heckeTrace_zero (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) :
    heckeTrace ι K ξ (fun _ => 0) = 0 := by
  have h0 : IsHecke ι K ξ (fun _ => 0) 0 := fun φ g => by simp
  have h : ∃ T, IsHecke ι K ξ (fun _ => 0) T := ⟨0, h0⟩
  have hT : h.choose = 0 := by
    apply LinearMap.ext; intro φ; apply Subtype.ext; funext g
    rw [h.choose_spec φ g]; simp
  rw [heckeTrace, dif_pos h, hT, map_zero]

end HeckeTraceForms

variable {p : ℕ} [Fact p.Prime]

structure DForm (G : HTGroup p) where

  β : G.Cˣ
  sym : sh G β = β
  trivAf : ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ), Triv G (AfP p) β x t

  posR : ∀ v : InfinitePlace G.F, ∀ x : Fin G.n → ℂ, x ≠ 0 →
    (sigPosH (G.gram_herm v) = 1 → 0 < (star x ⬝ᵥ ((G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re) ∧
    (sigPosH (G.gram_herm v) ≠ 1 → (star x ⬝ᵥ ((G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re < 0)

namespace DForm

variable {G : HTGroup p}

def Rel (P Q : DForm G) : Prop :=
  ∃ (y : G.Cˣ) (s : ℚ), 0 < s ∧ (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y)

def ofDPair (P : DPair G) : DForm G := ⟨P.β, P.sym, P.trivAf, P.posR⟩

def embAt (B : DForm G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) B.β x t) :
    GlobalTheory.LKCx.grp G B.β →* G.GAf × Gr G 1 :=
  (GlobalTheory.LKCx.toAfF G B.β x t hx).prod (GlobalTheory.LKCx.toP1 G B.β)

def emb (B : DForm G) : GlobalTheory.LKCx.grp G B.β →* G.GAf × Gr G 1 :=
  B.embAt B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec

def trace (B : DForm G) {V : Type} [AddCommGroup V] [Module ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V)
    (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  HeckeTraceForms.heckeTrace B.emb (Kf.prod K') (ξ.comp (GlobalTheory.LKCx.grp G B.β).subtype) (fun h => f h.1 * f' h.2)

end DForm

def DFCls (G : HTGroup p) : Type := Quot (DForm.Rel (G := G))

def dTrace (G : HTGroup p) {V : Type} [AddCommGroup V] [Module ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V)
    (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  ∑ᶠ q : DFCls G, (Quot.out q).trace ξ Kf f K' f'

def RegIrr (G : HTGroup p) (x : G.C) : Prop :=
  (minpoly G.F x).natDegree = G.n ∧ (minpoly G.F x).Separable ∧ Irreducible (minpoly G.F x)

def TraceDefinitePairsEqAutomorphicTrace : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V)
      (wt : Polynomial G.F → ℂ),
      (∀ (B : DForm G) (y : GlobalTheory.LKCx.grp G B.β), (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).natDegree = G.n →
        (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).Separable →
        LinearMap.trace ℂ V (ξ y.1) = wt (minpoly G.F ((y.1.1 : G.Cˣ) : G.C))) →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      (∀ (B : DForm G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) B.β x t)
          (y : GlobalTheory.LKCx.grp G B.β), ¬ RegIrr G ((y.1.1 : G.Cˣ) : G.C) →
        GlobalTheory.LKCount.orbK (MonoidHom.id _) (L.K.toSubgroup.prod K') (B.embAt x t hx y)
          (fun h => f h.1 * f' h.2) = 0) →
      dSumIrr G wt L.K.toSubgroup f 1 K' f' = dTrace G ξ L.K.toSubgroup f K' f'

namespace HeckeTraceExample

open GlobalTheory.LKTrip.Example GlobalTheory.LKMid.Example GlobalTheory.LKDef.Example

theorem regIrr_of_n_one (G : HTGroup p) (hn : G.n = 1) (x : G.C) : RegIrr G x := by
  have hr : Module.finrank G.F G.C = 1 := by rw [G.rankC, hn]; rfl
  have htop : (⊥ : Subalgebra G.F G.C) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one hr
  have hx : x ∈ (⊥ : Subalgebra G.F G.C) := by rw [htop]; exact Algebra.mem_top
  obtain ⟨a, rfl⟩ := Algebra.mem_bot.1 hx
  rw [RegIrr, minpoly.eq_X_sub_C, hn]
  exact ⟨Polynomial.natDegree_X_sub_C _, Polynomial.separable_X_sub_C, Polynomial.irreducible_X_sub_C _⟩

def exDF : DForm (ex 1 one_ne_zero) := DForm.ofDPair exD

theorem dFCls_nonempty : Nonempty (DFCls (ex 1 one_ne_zero)) := ⟨Quot.mk _ exDF⟩

theorem indicator_bi {H : Type} [Group H] (K : Subgroup H) :
    ∀ k ∈ K, ∀ k' ∈ K, ∀ g, Set.indicator (K : Set H) (1 : H → ℂ) (k * g * k') = Set.indicator (K : Set H) 1 g := by
  intro k hk k' hk' g
  have : k * g * k' ∈ K ↔ g ∈ K := by
    rw [K.mul_mem_cancel_right hk', K.mul_mem_cancel_left hk]
  by_cases hg : g ∈ K
  · simp [Set.indicator_apply, hg, this.2 hg]
  · have h2 : k * g * k' ∉ K := fun h => hg (this.1 h)
    simp [Set.indicator_apply, hg, h2]

theorem hyps_ex :
    (ex 1 one_ne_zero).a = 1 ∧
    (∀ (B : DForm (ex 1 one_ne_zero)) (y : GlobalTheory.LKCx.grp (ex 1 one_ne_zero) B.β),
      (minpoly (ex 1 one_ne_zero).F ((y.1.1 : (ex 1 one_ne_zero).Cˣ) : (ex 1 one_ne_zero).C)).natDegree =
        (ex 1 one_ne_zero).n →
      (minpoly (ex 1 one_ne_zero).F ((y.1.1 : (ex 1 one_ne_zero).Cˣ) : (ex 1 one_ne_zero).C)).Separable →
      LinearMap.trace ℂ ℂ (Representation.trivial ℂ ((ex 1 one_ne_zero).Cˣ × ℚˣ) ℂ y.1) =
        (fun _ => (1 : ℂ)) (minpoly (ex 1 one_ne_zero).F ((y.1.1 : (ex 1 one_ne_zero).Cˣ) : (ex 1 one_ne_zero).C))) ∧
    ∃ (L : (ex 1 one_ne_zero).Level) (f : (ex 1 one_ne_zero).GAf → ℂ) (K' : Subgroup (Gr (ex 1 one_ne_zero) 1))
      (f' : Gr (ex 1 one_ne_zero) 1 → ℂ), f 1 = 1 ∧ f' 1 = 1 ∧
      IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f ∧
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) ∧
      IsTest (sigG (ex 1 one_ne_zero) 1) (KHT 5 (ex 1 one_ne_zero).m (ex 1 one_ne_zero).n 1 (ex 1 one_ne_zero).Fw) K' f' ∧
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) ∧
      (∀ (B : DForm (ex 1 one_ne_zero)) (x : (AfP 5 ⊗[ℚ] (ex 1 one_ne_zero).C)ˣ) (t : (AfP 5)ˣ)
          (hx : Triv (ex 1 one_ne_zero) (AfP 5) B.β x t) (y : GlobalTheory.LKCx.grp (ex 1 one_ne_zero) B.β),
          ¬ RegIrr (ex 1 one_ne_zero) ((y.1.1 : (ex 1 one_ne_zero).Cˣ) : (ex 1 one_ne_zero).C) →
        GlobalTheory.LKCount.orbK (MonoidHom.id _) (L.K.toSubgroup.prod K') (B.embAt x t hx y)
          (fun h => f h.1 * f' h.2) = 0) ∧
      Nonempty (DFCls (ex 1 one_ne_zero)) := by
  obtain ⟨L⟩ := GlobalTheory.LKTrip.LevelExists.level_exists 5 (ex 1 one_ne_zero)
  refine ⟨a_ex_one, fun B y _ _ => ?_, L, _, _, _, Set.indicator_of_mem (Subgroup.one_mem _) _,
    Set.indicator_of_mem (Subgroup.one_mem _) _, isTest_indicator _ _ (by simp), indicator_bi _,
    isTest_indicator _ _ ?_, indicator_bi _, fun B x t hx y hy => absurd (regIrr_of_n_one _ rfl _) hy,
    dFCls_nonempty⟩
  · simp [Representation.trivial]
  · rintro _ ⟨k, hk, rfl⟩
    rw [GlobalTheory.LKCx.sigG_one]; exact hk

example (G : HTGroup p) {V : Type} [AddCommGroup V] [Module ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V)
    (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) :
    dSumIrr G wt Kf (fun _ => 0) 1 K' f' = dTrace G ξ Kf (fun _ => 0) K' f' := by
  have h1 : dSumIrr G wt Kf (fun _ => 0) 1 K' f' = 0 := by
    simp [dSumIrr, DPair.term, DPair.termAt, GlobalTheory.LKCount.pointSum]
  have h2 : dTrace G ξ Kf (fun _ => 0) K' f' = 0 := by
    simp only [dTrace, DForm.trace, zero_mul]
    simp [HeckeTraceForms.heckeTrace_zero]
  rw [h1, h2]

end HeckeTraceExample

end GlobalTheory.LKDef

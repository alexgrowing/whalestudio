import Formalism.SatakeDualWeyl.Statement

namespace Formalism.L2.G.Cmp

open Formalism.UG

structure Fib {G Gp : Type} [Group G] [Group Gp] (K K' : Subgroup G) (Kp : Subgroup Gp) where
  j : Gp →* G
  pr : G →* Gp
  pr_j : ∀ g, pr (j g) = g
  j_mem : ∀ g, j g ∈ K'
  K_iff : ∀ x, x ∈ K ↔ x ∈ K' ∧ pr x ∈ Kp

namespace Fib

variable {G Gp : Type} [Group G] [Group Gp] {K K' : Subgroup G} {Kp : Subgroup Gp} (X : Fib K K' Kp) (H : Subgroup G)

def mkC (S : Subgroup G) (a : G) : ClassSet H S := DoubleCoset.mk H S a

theorem mk_eq_iff (S : Subgroup G) (a b : G) :
    (mkC H S a = mkC H S b) ↔ ∃ h ∈ H, ∃ κ ∈ S, b = h * a * κ := by
  unfold mkC
  exact DoubleCoset.eq _ _ a b

theorem K'_split (x : G) (hx : x ∈ K') : (X.j (X.pr x))⁻¹ * x ∈ K := by
  rw [X.K_iff]
  refine ⟨K'.mul_mem (K'.inv_mem (X.j_mem _)) hx, ?_⟩
  rw [map_mul, map_inv, X.pr_j, inv_mul_cancel]
  exact Kp.one_mem

variable (y : ClassSet H K' → G) (hy : ∀ i, mkC H K' (y i) = i) (hp : ∀ i, X.pr (y i) = 1)

include hy hp in

theorem cls_iff (i i' : ClassSet H K') (g g' : Gp) :
    mkC H K (y i * X.j g) = mkC H K (y i' * X.j g') ↔
      i = i' ∧ ∃ γ ∈ H, (y i)⁻¹ * γ * y i ∈ K' ∧ g'⁻¹ * (X.pr γ * g) ∈ Kp := by
  rw [mk_eq_iff]
  constructor
  · rintro ⟨h, hh, κ, hκ, he⟩
    have hκ' := (X.K_iff κ).1 hκ
    have hi : i = i' := by
      rw [← hy i, ← hy i', mk_eq_iff]
      refine ⟨h, hh, X.j g * κ * (X.j g')⁻¹,
        K'.mul_mem (K'.mul_mem (X.j_mem g) hκ'.1) (K'.inv_mem (X.j_mem g')), ?_⟩
      calc y i' = (y i' * X.j g') * (X.j g')⁻¹ := by group
        _ = h * (y i * X.j g) * κ * (X.j g')⁻¹ := by rw [he]
        _ = h * y i * (X.j g * κ * (X.j g')⁻¹) := by group
    subst hi
    have hh' : h = (y i * X.j g') * κ⁻¹ * (y i * X.j g)⁻¹ := by rw [he]; group
    have hz : (y i)⁻¹ * h * y i = X.j g' * κ⁻¹ * (X.j g)⁻¹ := by rw [hh']; group
    refine ⟨rfl, h, hh, ?_, ?_⟩
    · rw [hz]
      exact K'.mul_mem (K'.mul_mem (X.j_mem _) (K'.inv_mem hκ'.1)) (K'.inv_mem (X.j_mem _))
    · rw [hh']
      simp only [map_mul, map_inv, X.pr_j, hp]
      convert Kp.inv_mem hκ'.2 using 1
      group
  · rintro ⟨rfl, γ, hγ, hz, hg⟩
    refine ⟨γ, hγ, (y i * X.j g)⁻¹ * γ⁻¹ * (y i * X.j g'), ?_, by group⟩
    rw [X.K_iff]
    have e : (y i * X.j g)⁻¹ * γ⁻¹ * (y i * X.j g') =
        (X.j g)⁻¹ * ((y i)⁻¹ * γ * y i)⁻¹ * X.j g' := by group
    rw [e]
    refine ⟨K'.mul_mem (K'.mul_mem (K'.inv_mem (X.j_mem _)) (K'.inv_mem hz)) (X.j_mem _), ?_⟩
    simp only [map_mul, map_inv, X.pr_j, hp]
    convert Kp.inv_mem hg using 1
    group

include hy in

theorem cls_surj (x : G) : ∃ i g, mkC H K (y i * X.j g) = mkC H K x := by
  obtain ⟨h, hh, κ, hκ, he⟩ := (mk_eq_iff H K' (y (mkC H K' x)) x).1 (hy _)
  refine ⟨mkC H K' x, X.pr κ, (mk_eq_iff H K _ _).2
    ⟨h, hh, (X.j (X.pr κ))⁻¹ * κ, X.K'_split κ hκ, ?_⟩⟩
  conv_lhs => rw [he]
  group

include hp in

theorem stab_iff (i : ClassSet H K') (g : Gp) (γ : G) :
    (y i * X.j g)⁻¹ * γ * (y i * X.j g) ∈ K ↔ (y i)⁻¹ * γ * y i ∈ K' ∧ g⁻¹ * (X.pr γ * g) ∈ Kp := by
  have hz : (y i * X.j g)⁻¹ * γ * (y i * X.j g) = (X.j g)⁻¹ * ((y i)⁻¹ * γ * y i) * X.j g := by
    group
  rw [hz, X.K_iff]
  have hjg := X.j_mem g
  have h1 : (X.j g)⁻¹ * ((y i)⁻¹ * γ * y i) * X.j g ∈ K' ↔ (y i)⁻¹ * γ * y i ∈ K' := by
    constructor
    · intro h
      have h2 := K'.mul_mem (K'.mul_mem hjg h) (K'.inv_mem hjg)
      have e : X.j g * ((X.j g)⁻¹ * ((y i)⁻¹ * γ * y i) * X.j g) * (X.j g)⁻¹ =
          (y i)⁻¹ * γ * y i := by group
      rwa [e] at h2
    · intro h
      exact K'.mul_mem (K'.mul_mem (K'.inv_mem hjg) h) hjg
  rw [h1]
  simp only [map_mul, map_inv, X.pr_j, hp, inv_one, one_mul, mul_one, mul_assoc]

end Fib

end Formalism.L2.G.Cmp

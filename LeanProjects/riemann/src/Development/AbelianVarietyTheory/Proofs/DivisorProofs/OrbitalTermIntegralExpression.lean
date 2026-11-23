import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelesSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalTermPointSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumCompMulEquiv
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.Regroup

variable {p : ℕ} [Fact p.Prime]

noncomputable def centEquiv (G : HTGroup p) (P : Pair G) (hpos : ∀ y ∈ P.cent, 0 < ((y.2 : ℚˣ) : ℚ))
    (r : grp G P.β) (hr : (r : G.Cˣ × ℚˣ) = (P.γ, P.c)) :
    Subgroup.centralizer ({r} : Set (grp G P.β)) ≃* P.cent where
  toFun y := ⟨y.1.1, by
    have h := congrArg (fun a : grp G P.β => (a : G.Cˣ × ℚˣ).1)
      (Subgroup.mem_centralizer_singleton_iff.1 y.2)
    simp only [Subgroup.coe_mul, hr, Prod.fst_mul] at h
    exact h, y.1.2.1⟩
  invFun y := ⟨⟨y.1, y.2.2, hpos y.1 y.2⟩, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hr]
    exact Prod.ext y.2.1 (mul_comm _ _)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem fix_iff_mark (G : HTGroup p) (hG : G.a = 1) (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1)
    (P : Pair G) (r : grp G P.β) (hr : (r : G.Cˣ × ℚˣ) = (P.γ, P.c)) :
    (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v P.β *ᵥ z)).re ∧ FixL G v P.β r z) ↔ ∃ μ, P.Mark μ := by
  have hV : (toV G v P.β r : Matrix (Fin G.n) (Fin G.n) ℂ) = G.psi v (P.γ : G.C) := by
    show G.psi v (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = _
    rw [hr]
  constructor
  · rintro ⟨z, hz, c, hc⟩
    rw [hV] at hc
    exact ⟨c, v, hv, z, hc, hz⟩
  · rintro ⟨μ, w, hw, z, hz, hpos⟩
    have h1 : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1 := hG.le
    have hvv : w = v := congrArg Subtype.val (Fintype.card_le_one_iff.1 h1 ⟨w, hw⟩ ⟨v, hv⟩)
    subst hvv
    exact ⟨z, hpos, μ, by rw [hV]; exact hz⟩

end GlobalTheory.LKCx.Regroup

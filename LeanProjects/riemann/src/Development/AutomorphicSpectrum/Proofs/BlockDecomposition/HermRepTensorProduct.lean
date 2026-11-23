import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.TensRep

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem res_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W W' : (MP ℤ m n).Opens} (h : W' ≤ W)
    (h' : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) :
    Semi.res h (blockUnit i j h') = blockUnit i j (h.trans h') :=
  DVR.res_res' _ _ _

def mulUnit {P Q C : (MP ℤ m n).Opens} (u : Γ(MP ℤ m n, P ⊓ C)ˣ) (v : Γ(MP ℤ m n, Q ⊓ C)ˣ) :
    Γ(MP ℤ m n, P ⊓ Q ⊓ C)ˣ :=
  Semi.res (inf_le_inf_right _ inf_le_left) u * Semi.res (inf_le_inf_right _ inf_le_right) v

theorem ev_mulUnit {P Q C : (MP ℤ m n).Opens} (u : Γ(MP ℤ m n, P ⊓ C)ˣ) (v : Γ(MP ℤ m n, Q ⊓ C)ˣ)
    {y : CxPts (mpStr ℤ m n) σ₀} (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (P ⊓ Q ⊓ C)) :
    CxPts.ev (mpStr ℤ m n) σ₀ (P ⊓ Q ⊓ C) (mulUnit u v : Γ(MP ℤ m n, P ⊓ Q ⊓ C)ˣ) y =
      CxPts.ev (mpStr ℤ m n) σ₀ (P ⊓ C) (u : Γ(MP ℤ m n, P ⊓ C)) y *
        CxPts.ev (mpStr ℤ m n) σ₀ (Q ⊓ C) (v : Γ(MP ℤ m n, Q ⊓ C)) y := by
  rw [mulUnit, Units.val_mul, CxPts.ev_mul]
  exact congrArg₂ (· * ·) (CxPts.ev_res _ hy _) (CxPts.ev_res _ hy _)

theorem frame_mulUnit {P P' Q Q' C : (MP ℤ m n).Opens} (g : Γ(MP ℤ m n, P ⊓ P')ˣ) (g' : Γ(MP ℤ m n, Q ⊓ Q')ˣ)
    (u : Γ(MP ℤ m n, P ⊓ C)ˣ) (u' : Γ(MP ℤ m n, P' ⊓ C)ˣ) (v : Γ(MP ℤ m n, Q ⊓ C)ˣ) (v' : Γ(MP ℤ m n, Q' ⊓ C)ˣ)
    (a₁ : P ⊓ P' ⊓ C ≤ P' ⊓ C) (a₂ : P ⊓ P' ⊓ C ≤ P ⊓ P') (a₃ : P ⊓ P' ⊓ C ≤ P ⊓ C)
    (b₁ : Q ⊓ Q' ⊓ C ≤ Q' ⊓ C) (b₂ : Q ⊓ Q' ⊓ C ≤ Q ⊓ Q') (b₃ : Q ⊓ Q' ⊓ C ≤ Q ⊓ C)
    (hu : Semi.res a₁ u' = Semi.res a₂ g * Semi.res a₃ u) (hv : Semi.res b₁ v' = Semi.res b₂ g' * Semi.res b₃ v)
    (d₁ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P' ⊓ Q' ⊓ C) (d₂ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P ⊓ Q ⊓ (P' ⊓ Q'))
    (d₃ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P ⊓ Q ⊓ C) (f₁ : P ⊓ Q ⊓ (P' ⊓ Q') ≤ P ⊓ P') (f₂ : P ⊓ Q ⊓ (P' ⊓ Q') ≤ Q ⊓ Q') :
    Semi.res d₁ (mulUnit u' v') = Semi.res d₂ (Semi.res f₁ g * Semi.res f₂ g') * Semi.res d₃ (mulUnit u v) := by
  have l₁ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P ⊓ P' ⊓ C := inf_le_inf_right _ (inf_le_inf inf_le_left inf_le_left)
  have l₂ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ Q ⊓ Q' ⊓ C := inf_le_inf_right _ (inf_le_inf inf_le_right inf_le_right)
  have e₁ := congrArg (Semi.res l₁) hu
  have e₂ := congrArg (Semi.res l₂) hv
  simp only [map_mul, DVR.res_res'] at e₁ e₂
  simp only [mulUnit, map_mul, DVR.res_res']
  exact (congrArg₂ (· * ·) e₁ e₂).trans (mul_mul_mul_comm _ _ _ _)

theorem mono_mulUnit {P Q : (MP ℤ m n).Opens} {c c' : ∀ k, Bk n k} (a b : Fin (m + 1) → ℤ)
    (u : Γ(MP ℤ m n, P ⊓ mchart c)ˣ) (u' : Γ(MP ℤ m n, P ⊓ mchart c')ˣ)
    (v : Γ(MP ℤ m n, Q ⊓ mchart c)ˣ) (v' : Γ(MP ℤ m n, Q ⊓ mchart c')ˣ)
    (a₁ : P ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ mchart c) (a₂ : P ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ mchart c')
    (b₁ : Q ⊓ (mchart c ⊓ mchart c') ≤ Q ⊓ mchart c) (b₂ : Q ⊓ (mchart c ⊓ mchart c') ≤ Q ⊓ mchart c')
    (ta : ∀ k, P ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)))
    (tb : ∀ k, Q ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)))
    (hu : Semi.res a₁ u = Semi.res a₂ u' * ∏ k, blockUnit (c k) (c' k) (ta k) ^ a k)
    (hv : Semi.res b₁ v = Semi.res b₂ v' * ∏ k, blockUnit (c k) (c' k) (tb k) ^ b k)
    (d₁ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ Q ⊓ mchart c) (d₂ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ Q ⊓ mchart c')
    (td : ∀ k, P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) :
    Semi.res d₁ (mulUnit u v) = Semi.res d₂ (mulUnit u' v') * ∏ k, blockUnit (c k) (c' k) (td k) ^ (a k + b k) := by
  have l₁ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ (mchart c ⊓ mchart c') := inf_le_inf_right _ inf_le_left
  have l₂ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ Q ⊓ (mchart c ⊓ mchart c') := inf_le_inf_right _ inf_le_right
  have e₁ := congrArg (Semi.res l₁) hu
  have e₂ := congrArg (Semi.res l₂) hv
  simp only [map_mul, map_prod, map_zpow, DVR.res_res'] at e₁ e₂
  simp only [mulUnit, map_mul, DVR.res_res']
  refine ((congrArg₂ (· * ·) e₁ e₂).trans (mul_mul_mul_comm _ _ _ _)).trans (congrArg (HMul.hMul _) ?_)
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [res_blockUnit, res_blockUnit, ← zpow_add]

end GlobalTheory.CompanionTheory.MPDict.TensRep

namespace GlobalTheory.CompanionTheory.MPDict

open TensRep

theorem isHermRep_tens : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M N : HermLB (mpStr ℤ m n)) (A B : Geo.HermLine (Bk n)),
    IsHermRep M A → IsHermRep N B → IsHermRep (M.tens N) (A.tensor B) := by
  rintro m n M N A B ⟨u, hu₁, hu₂, hu₃⟩ ⟨v, hv₁, hv₂, hv₃⟩
  refine ⟨fun p c => mulUnit (u p.1 c) (v p.2 c), ?_, ?_, ?_⟩
  · rintro ⟨i, i'⟩ ⟨j, j'⟩ c
    exact frame_mulUnit _ _ _ _ _ _ _ _ _ _ _ _ (hu₁ i j c) (hv₁ i' j' c) _ _ _ _ _
  · rintro ⟨i, i'⟩ c c'
    exact mono_mulUnit A.a B.a _ _ _ _ _ _ _ _ _ _ (hu₂ i c c') (hv₂ i' c c') _ _ _
  · rintro ⟨i, i'⟩ c y z hz hy
    have hy' := mem_ptsIn_inf.1 hy
    have h₁ := mem_ptsIn_inf.1 hy'.1
    have e₁ := hu₃ i c y z hz (mem_ptsIn_inf.2 ⟨h₁.1, hy'.2⟩)
    have e₂ := hv₃ i' c y z hz (mem_ptsIn_inf.2 ⟨h₁.2, hy'.2⟩)
    have hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k => (hz k (c k)).1.1 (ptsIn_mono (mchart_le c k) hy'.2)
    have hp : ∏ k, ‖z ⟨k, c k⟩‖ ^ (A.a k + B.a k) =
        (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) * ∏ k, ‖z ⟨k, c k⟩‖ ^ B.a k := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => zpow_add₀ (norm_ne_zero_iff.2 (hz0 k)) _ _
    have hev := ev_mulUnit (u i c) (v i' c) hy
    change A.h z * B.h z = (∏ k, ‖z ⟨k, c k⟩‖ ^ (A.a k + B.a k)) *
      ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ N.B.U i' ⊓ mchart c)
        (mulUnit (u i c) (v i' c) : Γ(MP ℤ m n, M.B.U i ⊓ N.B.U i' ⊓ mchart c)ˣ) y‖ *
      Real.exp (((M.φ σ₀).φ i y + (N.φ σ₀).φ i' y) / 2)
    rw [e₁, e₂, hev, hp, norm_mul, add_div, Real.exp_add]
    ring

end GlobalTheory.CompanionTheory.MPDict

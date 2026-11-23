import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.GRHaar
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FactorL
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMapBis

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

instance krCpt (n : ℕ) : CompactSpace (KR n) := kRCpt n

def phi (m : ℕ) (e : ℤ) (w : ℂ) (u : GR n) : ℂ := F0 m 0 e u * ((hLoc u : ℝ) : ℂ) ^ w

def tw (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (β : M2 n → ℝ) (X : M2 n) : ℂ :=
  ∫ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * (β ((mR (k : GR n))ᴴ * X) : ℂ) ∂μK

def cw (m : ℕ) (e : ℤ) (ν : Measure (GR n)) (μK : Measure (KR n)) (β : M2 n → ℝ) (w : ℂ) : ℂ :=
  ∫ u : GR n, phi m e w u * tw m e μK β (mR u) ∂ν

theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := rfl

theorem tw_left (m : ℕ) (e : ℤ) (μK : Measure (KR n)) [μK.IsMulLeftInvariant] (β : M2 n → ℝ) (k₀ : KR n) (X : M2 n) :
    tw m e μK β (mR (k₀ : GR n) * X) = (F0 m 0 e (k₀ : GR n))⁻¹ * tw m e μK β X := by
  have h := integral_mul_left_eq_self (μ := μK)
    (fun k : KR n => (F0 m 0 e (k : GR n))⁻¹ * (β ((mR (k : GR n))ᴴ * (mR (k₀ : GR n) * X)) : ℂ)) k₀
  rw [tw, ← h, tw, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  have hk0 : (mR (k₀ : GR n))ᴴ * mR (k₀ : GR n) = 1 := k₀.2.2
  have hmul := ((mult n m 0 e).1 (k₀ : GR n) (k : GR n) k.2).1
  simp only [Subgroup.coe_mul, mR_mul]
  rw [hmul, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (mR (k₀ : GR n))ᴴ, hk0, Matrix.one_mul,
    mul_inv]
  ring

theorem conv_phi (m : ℕ) (e : ℤ) (ν : Measure (GR n)) [ν.IsMulLeftInvariant] (μK : Measure (KR n)) [μK.IsMulLeftInvariant]
    (β : M2 n → ℝ) (w : ℂ) (y : GR n) :
    ∫ u : GR n, phi m e w (y * u) * tw m e μK β (mR u) ∂ν = cw m e ν μK β w * phi m e w y := by
  obtain ⟨p, k, hp, hk, rfl⟩ := iwa n y
  have hnn : ∀ g : GR n, 0 ≤ hLoc g := fun g => by unfold hLoc; positivity
  have hphi : ∀ g : GR n, phi m e w (p * g) = phi m e w p * phi m e w g := by
    intro g
    obtain ⟨h1, h2⟩ := (mult n m 0 e).2 p g hp
    simp only [phi, h1, h2, Complex.ofReal_mul]
    rw [Complex.mul_cpow_ofReal_nonneg (hnn p) (hnn g)]
    ring
  have hK : phi m e w (p * k) = phi m e w p * F0 m 0 e k := by
    obtain ⟨h1, h2⟩ := (mult n m 0 e).1 p k hk
    simp only [phi, h1, h2]
    ring
  have hone : F0 m 0 e (1 : GR n) = 1 := by
    have h1 : toBlocks₂₁ (1 : M2 n) = 0 := by
      ext i j; simp [Matrix.toBlocks₂₁, Matrix.one_apply]
    have h2 : toBlocks₂₂ (1 : M2 n) = 1 := by
      ext i j; simp [Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]
    simp [F0, mR, f0, u1, u2, h1, h2]
  have hF : F0 m 0 e k * F0 m 0 e k⁻¹ = 1 := by
    rw [← ((mult n m 0 e).1 k k⁻¹ (inv_mem hk)).1, mul_inv_cancel, hone]
  have htw : ∀ u : GR n, tw m e μK β (mR (k⁻¹ * u)) = F0 m 0 e k * tw m e μK β (mR u) := by
    intro u
    rw [mR_mul]
    have h := tw_left m e μK β (⟨k⁻¹, inv_mem hk⟩ : KR n) (mR u)
    simp only at h
    rw [h, inv_eq_of_mul_eq_one_left hF]
  calc ∫ u : GR n, phi m e w (p * k * u) * tw m e μK β (mR u) ∂ν
      = ∫ u : GR n, phi m e w (p * k * (k⁻¹ * u)) * tw m e μK β (mR (k⁻¹ * u)) ∂ν :=
        (integral_mul_left_eq_self (fun u => phi m e w (p * k * u) * tw m e μK β (mR u)) k⁻¹).symm
    _ = ∫ u : GR n, (F0 m 0 e k * phi m e w p) * (phi m e w u * tw m e μK β (mR u)) ∂ν := by
        congr 1
        funext u
        rw [show p * k * (k⁻¹ * u) = p * u by group, hphi, htw]
        ring
    _ = cw m e ν μK β w * phi m e w (p * k) := by
        rw [integral_const_mul, hK]
        unfold cw
        ring

end PositivityTheory.Rg.Sw.HSt.Conv

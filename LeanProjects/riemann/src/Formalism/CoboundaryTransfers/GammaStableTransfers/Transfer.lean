import Formalism.LagrangeIdealLifts.LiftLagrangeIdealInt
import Formalism.CoboundaryTransfers.StatementBridge
import Formalism.CoboundaryTransfers.StatementTransfer

noncomputable section

namespace Formalism.CoboundaryTransfers

open Formalism

section Maps

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
  {B : Base ℤ_[ℓ] A} {M : ℕ}

def homToLIFT {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D']
    [IsScalarTower ℤ_[ℓ] A D'] {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W')
    (u : ℤ_[ℓ]ˣ) (hφ : B.φ B.X = B.X * B.Q) (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) :
    LIFT.Hom (W.toLIFT u hφ hγX hγQ) (W'.toLIFT u hφ hγX hγQ) where
  f := F.f
  φ_comm := F.φ_comm
  γ_comm := F.γ_comm
  N_le := F.N_le

def sesToLIFT {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    {W₀ : WachMod B M D₀} {W₁ : WachMod B M D₁} {W₂ : WachMod B M D₂} (S : SES W₀ W₁ W₂)
    (u : ℤ_[ℓ]ˣ) (hφ : B.φ B.X = B.X * B.Q) (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) :
    LIFT.SES (W₀.toLIFT u hφ hγX hγQ) (W₁.toLIFT u hφ hγX hγQ) (W₂.toLIFT u hφ hγX hγQ) where
  ι := homToLIFT S.ι u hφ hγX hγQ
  π := homToLIFT S.π u hφ hγX hγQ
  ι_inj := S.ι_inj
  exact := S.exact
  sat := S.sat

end Maps

theorem wachLatticeUnramified_statement : LemmaUU := by
  intro ℓ _ A _ _ B M u hp hφ hγX hγQ D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S e s J hs h2 hv
    hJ h1 h2' h3 h4 hCK hRS
  have hCK' : LIFT.CokerKilled (sesToLIFT S u hφ hγX hγQ) e := by
    intro n hn
    have := hCK n hn
    rw [hp] at this
    exact this
  have hRS' : LIFT.RatSurj (sesToLIFT S u hφ hγX hγQ) := by
    intro y z hyz
    have := hRS y z hyz
    rw [hp] at this
    exact this
  exact LIFT.lift_LemmaU ℓ A (toLIFT B u hφ hγX hγQ) M D₀ D₁ D₂ (W₀.toLIFT u hφ hγX hγQ)
    (W₁.toLIFT u hφ hγX hγQ) (W₂.toLIFT u hφ hγX hγQ) (sesToLIFT S u hφ hγX hγQ) e s J hs h2 hv
    hJ h1 h2' h3 h4 hCK' hRS'

end Formalism.CoboundaryTransfers

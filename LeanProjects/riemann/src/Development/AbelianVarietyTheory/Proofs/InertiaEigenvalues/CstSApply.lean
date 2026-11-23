import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

def cstS : Wq l a →+* (ZMod a → K⟦X⟧) :=
  Pi.ringHom fun τ => (C : K →+* K⟦X⟧).comp ((algebraMap O K).comp (emb t τ).toRingHom)

theorem cstS_apply (w : Wq l a) (τ : ZMod a) : cstS t K w τ = C (algebraMap O K (emb t τ w)) := rfl

variable (a) {K} in

def dpS (e n : ℕ) : ZMod a → K⟦X⟧ := fun _ => monomial n (((n / e).factorial : K)⁻¹)

end GlobalTheory.CrysPrism

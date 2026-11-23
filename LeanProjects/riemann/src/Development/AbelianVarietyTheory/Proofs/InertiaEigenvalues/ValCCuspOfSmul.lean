import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def embS {D : D7} (S : NX.RatDat D.ntw) {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool) :
    S.Ks →+* ℂ_[D.ntw.l i] :=
  iC.comp (NX.ιK S i b)

section Ball

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀) {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool)
  (j : Fin D.R.m)

theorem embC_eKs (a : S.Ks) : embC YS iC b (eKs YS a) = embS S iC b a := by
  simp only [embC, embS, RingHom.comp_apply, sideK_eKs]
  rfl

def locBall : Set (NX.FmK S ((j : ℕ) + 1)) :=
  {f | ∀ z : Pts YS iC b ((j : ℕ) + 1), ‖valC z.1 (cuspOf YS fw j f : T0.R ((j : ℕ) + 1))‖ ≤ 1}

variable {iC b} in
theorem valC_cuspOf_smul (z : FrC YS iC b ((j : ℕ) + 1)) (a : S.Ks) (f : NX.FmK S ((j : ℕ) + 1)) :
    valC z (cuspOf YS fw j (a • f) : T0.R ((j : ℕ) + 1)) = embS S iC b a * valC z (cuspOf YS fw j f : T0.R ((j : ℕ) + 1)) := by
  rw [cuspOf_smul, Submodule.coe_smul, valC_smul, embC_eKs]

end Ball

end GlobalTheory.GeoTie

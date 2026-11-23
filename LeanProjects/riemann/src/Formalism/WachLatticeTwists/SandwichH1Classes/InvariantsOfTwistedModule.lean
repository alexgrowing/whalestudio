import Formalism.WachLatticeTwists.SandwichH1Classes.ComparisonMatrixIntertwinesEndomorphisms

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

def Setup.eOh {ℓ : ℕ} [Fact ℓ.Prime] (R : Setup ℓ) : R.Tt.Om →+* R.OC :=
  R.emb.comp (algebraMap R.Tt.Om R.Tt.Oi)

structure Setup.FactsH {ℓ : ℕ} [Fact ℓ.Prime] (R : Setup ℓ) : Prop where
  pH : ∀ h ∈ R.H, R.p h ∈ R.Hs
  fixAs : ∀ h ∈ R.Hs, ∀ a, R.actA h (R.jA a) = R.jA a
  fixOi : ∀ h ∈ R.H, ∀ a, R.actO (R.p h) (R.emb a) = R.emb a
  t4 : ∀ y : R.OC, (∀ h ∈ R.H, R.actO (R.p h) y = y) → ∃ a : R.Tt.Oi, R.emb a = y
  injE : Function.Injective R.emb
  g0E : ∀ a, R.actO (R.p R.gg) (R.emb a) = R.emb (R.Tt.g0 a)

def StatUmH : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Setup ℓ) (r : ℕ) (L : Lat ℓ R.Gg r)
    (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ])) (M0 h0 : ℕ)
    (W : HypWc ℓ R.As R.AA R.WC R.jA R.ι R.φ R.Gg R.Hs R.act r L.ρ En R.πs R.ξ M0 h0),
    R.Facts r M0 h0 → R.FactsH → ∀ h ∈ R.H, UmW R L W (R.p h) = 1

structure InvariantsRemainingGroups (ℓ : ℕ) [Fact ℓ.Prime] (A H0WeightInvariants : Md ℓ) where

  M : Md ℓ

  invariantsModPower : ℕ → Md ℓ
  red : ∀ r, H0WeightInvariants →ₗ[ℤ_[ℓ]] invariantsModPower r
  dl : ∀ r, invariantsModPower r →ₗ[ℤ_[ℓ]] A
  emb : ∀ r, Submodule.torsionBy ℤ_[ℓ] M ((ℓ : ℤ_[ℓ]) ^ r) →ₗ[ℤ_[ℓ]] invariantsModPower r

def InvariantsRemainingGroups.toH0 {ℓ : ℕ} [Fact ℓ.Prime] {A H0WeightInvariants : Md ℓ} (X : InvariantsRemainingGroups ℓ A H0WeightInvariants) (piece : Piece ℓ A) :
    InvariantsCohomologyData ℓ :=
  { M := X.M, A := A, piece := piece, H0WeightInvariants := H0WeightInvariants, jm := 0, jX := 0, invariantsModPower := X.invariantsModPower, red := X.red,
    dl := X.dl, emb := X.emb }

def InvariantsOfTwistedModule : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Setup ℓ) (r : ℕ) (L : Lat ℓ R.Gg r)
    (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ])) (M0 h0 : ℕ)
    (W : HypWc ℓ R.As R.AA R.WC R.jA R.ι R.φ R.Gg R.Hs R.act r L.ρ En R.πs R.ξ M0 h0)
    (A : Matrix (Fin r) (Fin r) R.AA) (Y' : Matrix (Fin r) (Fin r) R.OC),
    R.Facts r M0 h0 → R.FactsH → A.map R.ι = (R.ι (R.jA R.x)) ^ M0 • W.Xx →
    A.map R.ϑ * Y' = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC) →
    Y' * A.map R.ϑ = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC) →
    ∀ (ρ : ℕ) (Sτ : SL R.actO ρ) (Pp : Matrix (Fin r) (Fin ρ) R.OC) (Sp : Matrix (Fin ρ) (Fin r) R.OC)
      (Cm : Matrix (Fin ρ) (Fin r) R.Tt.Om) (Bm : Matrix (Fin r) (Fin ρ) R.Tt.Om) (Uτ : Finset ℤ),
    R.TateX ρ → (∀ g, Pp.map (R.actO g) * Sτ.Mx g = (L.sl R.actO).Mx g * Pp) → Sp * Pp = 1 →
    A.map R.ϑ * Pp = Bm.map R.eOh * (Cm.map R.eOh * (A.map R.ϑ * Pp)) →
    R.Tt.HTdec (Cm * VmW R L W * Bm) R.w Uτ → 0 ∉ Uτ → Uτ.Nonempty →
    ∀ (infm : (Fin ρ → R.Tt.Om) →ₗ[ℤ_[ℓ]]
        H1 (repU R (fun g => (Cm.map R.eOh).map (R.actO g) * UmW R L W g * Bm.map R.eOh) 0))
      (infX : (Fin ρ → R.Tt.Xm) →ₗ[ℤ_[ℓ]]
        H1 (repU R (fun g => (Cm.map R.eOh).map (R.actO g) * UmW R L W g * Bm.map R.eOh) 0))
      (X : InvariantsRemainingGroups ℓ (ModuleCat.of ℤ_[ℓ] (H1 (repS R Sτ 0))) (ModuleCat.of ℤ_[ℓ] (inv0 R Sτ))),
    (pieceB R Sτ (fun g => (Cm.map R.eOh).map (R.actO g) * UmW R L W g * Bm.map R.eOh)
      (Cm * VmW R L W * Bm) (Cm.map R.eOh * (A.map R.ϑ * Pp)) (Sp * Y' * Bm.map R.eOh) 0 infm infX).InfRes →
    (pieceB R Sτ (fun g => (Cm.map R.eOh).map (R.actO g) * UmW R L W g * Bm.map R.eOh)
      (Cm * VmW R L W * Bm) (Cm.map R.eOh * (A.map R.ϑ * Pp)) (Sp * Y' * Bm.map R.eOh) 0 infm infX).T4 →
    (X.toH0 (pieceB R Sτ (fun g => (Cm.map R.eOh).map (R.actO g) * UmW R L W g * Bm.map R.eOh)
      (Cm * VmW R L W * Bm) (Cm.map R.eOh * (A.map R.ϑ * Pp)) (Sp * Y' * Bm.map R.eOh) 0 infm infX)).Union →
    (X.toH0 (pieceB R Sτ (fun g => (Cm.map R.eOh).map (R.actO g) * UmW R L W g * Bm.map R.eOh)
      (Cm * VmW R L W * Bm) (Cm.map R.eOh * (A.map R.ϑ * Pp)) (Sp * Y' * Bm.map R.eOh) 0 infm infX)).Flat →
    (X.toH0 (pieceB R Sτ (fun g => (Cm.map R.eOh).map (R.actO g) * UmW R L W g * Bm.map R.eOh)
      (Cm * VmW R L W * Bm) (Cm.map R.eOh * (A.map R.ϑ * Pp)) (Sp * Y' * Bm.map R.eOh) 0 infm infX)).LES →
    ∀ x : X.M, ((ℓ : ℤ_[ℓ]) ^ c0 ℓ (mOf ℓ R.s (M0 + h0)) Uτ) • x = 0

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

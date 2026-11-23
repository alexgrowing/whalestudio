import Formalism.WachLatticeTwists.SandwichH1Classes.StatTBW

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

section B

variable {ℓ : ℕ} [Fact ℓ.Prime] (R : Setup ℓ) {r : ℕ} (S : SL R.actO r)
  (Um : R.Gg → Matrix (Fin r) (Fin r) R.OC) (Vm : Matrix (Fin r) (Fin r) R.Tt.Om)

def repS (i : ℤ) : Representation ℤ_[ℓ] R.G (Fin r → R.OC) := ((S.twist R.χ i).rep).comp R.p

def repU (i : ℤ) : Representation ℤ_[ℓ] R.G (Fin r → R.OC) :=
  (((SL.ofFun R.actO Um).twist R.χ i).rep).comp R.p

def pieceB (Y Y' : Matrix (Fin r) (Fin r) R.OC) (i : ℤ)
    (infm : (Fin r → R.Tt.Om) →ₗ[ℤ_[ℓ]] H1 (repU R Um i))
    (infX : (Fin r → R.Tt.Xm) →ₗ[ℤ_[ℓ]] H1 (repU R Um i)) :
    Piece ℓ (ModuleCat.of ℤ_[ℓ] (H1 (repS R S i))) where
  E := ModuleCat.of ℤ_[ℓ] (H1 (repU R Um i))
  HH := ModuleCat.of ℤ_[ℓ] (H1 ((repU R Um i).comp R.H.subtype))
  Wm := ModuleCat.of ℤ_[ℓ] (Fin r → R.Tt.Om)
  WX := ModuleCat.of ℤ_[ℓ] (Fin r → R.Tt.Xm)
  gm := R.Tt.gmI Vm R.w i
  gX := R.Tt.gXI Vm R.w i
  lam := matrixMapOnH1 (S.twist R.χ i) ((SL.ofFun R.actO Um).twist R.χ i) Y' R.p
  io := matrixMapOnH1 ((SL.ofFun R.actO Um).twist R.χ i) (S.twist R.χ i) Y R.p
  infm := infm
  infX := infX
  res := H1.res (repU R Um i) R.H.subtype continuous_subtype_val

def inv0 : Submodule ℤ_[ℓ] (Fin r → R.OC) where
  carrier := {v | ∀ g, repS R S 0 g v = v}
  add_mem' := by
    intro a b ha hb g
    rw [map_add, ha g, hb g]
  zero_mem' := fun g => map_zero _
  smul_mem' := by
    intro t a ha g
    rw [map_smul, ha g]

end B

def Setup.eO {ℓ : ℕ} [Fact ℓ.Prime] (R : Setup ℓ) (a : R.Tt.Om) : R.OC :=
  R.emb (algebraMap R.Tt.Om R.Tt.Oi a)

def StatPieceB : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Setup ℓ) (r r₀ M0 h0 : ℕ) (S : SL R.actO r)
    (Um : R.Gg → Matrix (Fin r) (Fin r) R.OC) (Vm : Matrix (Fin r) (Fin r) R.Tt.Om) (U : Finset ℤ)
    (Y Y' : Matrix (Fin r) (Fin r) R.OC),
    R.Facts r₀ M0 h0 → R.TateX r → (∀ g, Y.map (R.actO g) * S.Mx g = Um g * Y) →
    Y * Y' = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC) →
    Y' * Y = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC) →
    (∀ a b, R.z * R.ϖ ∣ (Vm - 1) a b) → R.Tt.HTdec Vm R.w U →
    ∀ (i : ℤ) (infm : (Fin r → R.Tt.Om) →ₗ[ℤ_[ℓ]] H1 (repU R Um i))
      (infX : (Fin r → R.Tt.Xm) →ₗ[ℤ_[ℓ]] H1 (repU R Um i)),
      (pieceB R S Um Vm Y Y' i infm infX).InfRes → (pieceB R S Um Vm Y Y' i infm infX).T4 →
      (pieceB R S Um Vm Y Y' i infm infX).Inputs R.w U i

def StatSquare : Prop :=
  ∀ (OC : Type) [CommRing OC] (r : ℕ) (c : OC) (A B : Matrix (Fin r) (Fin r) OC),
    (∀ a : OC, c * a = 0 → a = 0) → A * B = c • (1 : Matrix (Fin r) (Fin r) OC) →
    B * A = c • (1 : Matrix (Fin r) (Fin r) OC)

def StatSec3 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (G : Type) [Group G] (OC Om : Type) [CommRing OC] [CommRing Om]
    [Algebra ℤ_[ℓ] OC] (eO : Om →+* OC) (actO : G →* (OC ≃ₐ[ℤ_[ℓ]] OC)) (r ρ : ℕ) (S : SL actO r)
    (Sτ : SL actO ρ) (Um : G → Matrix (Fin r) (Fin r) OC) (Vm : Matrix (Fin r) (Fin r) Om)
    (Y Y' : Matrix (Fin r) (Fin r) OC) (Pp : Matrix (Fin r) (Fin ρ) OC) (Sp : Matrix (Fin ρ) (Fin r) OC)
    (Cm : Matrix (Fin ρ) (Fin r) Om) (Bm : Matrix (Fin r) (Fin ρ) Om) (t : Om),
    (∀ a : OC, (ℓ : OC) * a = 0 → a = 0) → Function.Injective eO →
    (∀ g, Y.map (actO g) * S.Mx g = Um g * Y) →
    Y' * Y = (ℓ : OC) • (1 : Matrix (Fin r) (Fin r) OC) →
    (∀ g, Pp.map (actO g) * Sτ.Mx g = S.Mx g * Pp) → Sp * Pp = 1 →
    Y * Pp = Bm.map eO * (Cm.map eO * (Y * Pp)) →
    (∀ a b, t ∣ (Vm - 1) a b) →
    (Sp * Y' * Bm.map eO) * (Cm.map eO * (Y * Pp)) = (ℓ : OC) • (1 : Matrix (Fin ρ) (Fin ρ) OC) ∧
    (Cm.map eO * (Y * Pp)) * (Sp * Y' * Bm.map eO) = (ℓ : OC) • (1 : Matrix (Fin ρ) (Fin ρ) OC) ∧
    (∀ g, (Cm.map eO * (Y * Pp)).map (actO g) * Sτ.Mx g
      = ((Cm.map eO).map (actO g) * Um g * Bm.map eO) * (Cm.map eO * (Y * Pp))) ∧
    Cm * Bm = 1 ∧ ∀ a b, t ∣ (Cm * Vm * Bm - (1 : Matrix (Fin ρ) (Fin ρ) Om)) a b

def ComparisonMatrixIntertwinesEndomorphisms : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Setup ℓ) (r : ℕ) (L : Lat ℓ R.Gg r)
    (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ])) (M0 h0 : ℕ)
    (W : HypWc ℓ R.As R.AA R.WC R.jA R.ι R.φ R.Gg R.Hs R.act r L.ρ En R.πs R.ξ M0 h0)
    (A : Matrix (Fin r) (Fin r) R.AA), R.Facts r M0 h0 →
    A.map R.ι = (R.ι (R.jA R.x)) ^ M0 • W.Xx →
    ∀ E ∈ En, ∃ E' : Matrix (Fin r) (Fin r) R.As,
      A.map R.ϑ * E.map (algebraMap ℤ_[ℓ] R.OC) = (E'.map R.jA).map R.ϑ * A.map R.ϑ

def CyclotomicInvariantsZero : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Setup ℓ) (r r₀ M0 h0 : ℕ) (S : SL R.actO r)
    (Um : R.Gg → Matrix (Fin r) (Fin r) R.OC) (Vm : Matrix (Fin r) (Fin r) R.Tt.Om) (U : Finset ℤ)
    (Y Y' : Matrix (Fin r) (Fin r) R.OC),
    R.Facts r₀ M0 h0 → R.TateX r → (∀ g, Y.map (R.actO g) * S.Mx g = Um g * Y) →
    Y * Y' = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC) →
    Y' * Y = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC) →
    (∀ a b, R.z * R.ϖ ∣ (Vm - 1) a b) → R.Tt.HTdec Vm R.w U → 0 ∉ U →
    (∀ y : R.OC, (∀ h ∈ R.H, R.actO (R.p h) y = y) → ∃ a : R.Tt.Oi, R.emb a = y) →
    Function.Injective R.emb → (∀ a, R.actO (R.p R.gg) (R.emb a) = R.emb (R.Tt.g0 a)) →
    (∀ h ∈ R.H, Um (R.p h) = 1) → Um (R.p R.gg) = Vm.map R.eO →
    ∀ v ∈ inv0 R S, v = 0

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

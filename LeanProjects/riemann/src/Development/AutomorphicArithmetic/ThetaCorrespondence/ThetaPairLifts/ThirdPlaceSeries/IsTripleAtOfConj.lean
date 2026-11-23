import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GalRead

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Triple
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open Formalism.L2.Host (HChar CharFrame embLL0 eExp ValLL0)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ block)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE toFb)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
variable {D : D7}
section Reading
variable (X : NTw D.R D.host D.what₂ D.LL0 D.nd)
variable {X} {i : X.Tw} {b : Bool}
end Reading
section Comparison₂
variable (C : CharFrame D) (art : Ideles D.host.E →* Gab D.host.E D.nd.Om) {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
structure IsGaloisTripleWithReduction {i : X.Tw} {b : Bool} (ρ : Reading X i b) (s : X.Sig i) (σ : D.what₂.FT) (π : D.naut.CG D.R.r)
    (r : GalE D →* GL (Fin D.R.r) (Qbar (X.l i))) (ν : GalE D →* (X.O0 i)ˣ) (w : D.what₂.places.Pl)
    (red : Zbar (X.l i) →+* FbAt D w) : Prop where
  good : D.nd.goodRow σ
  occurs : D.what₂.isot (X.jS i s) σ ≠ ⊥
  param : IsParam σ π
  gal : _root_.UpperTheory.GalS.IsGaloisRepOfN D π (X.l i) ρ.ι r
  shift : ∃ n, IsGal art ρ.κ ρ.ι (shiftChar C) n ν
  rho : ∀ g, ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (toQ ρ.κ) =
    toQ ρ.κ ((ν g : (X.O0 i)ˣ) : X.O0 i) •
      ((r g : GL (Fin D.R.r) (Qbar (X.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (X.l i)))
  hecke : ∀ k P, k ≤ D.R.r → IsSplitPl D.host P → P ∉ X.S0 i → ∃ x : X.O0 i,
    algebraMap (X.O0 i) (X.O i) x = X.hEig i s k P ∧ ρ.toC x = heckeVal (muBase C (X.l i) (jIdx s)) π k P
  induces : ρ.Induces w
  residual : IsResidual ρ.ι r σ w red
def IsGaloisTripleAtSignature {i : X.Tw} {b : Bool} (ρ : Reading X i b) (s : X.Sig i) : Prop :=
  ∃ σ π r ν w red, _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red
structure IsGaloisTripleForExpansion (Y : NExp D.R D.host D.what₂ D.LL0 D.nd X) : Prop where
  artin : IsGlobalArtin art
  evidence : ∀ i, X.NonzeroIndexPlace i → ∀ b : Bool, ∃ ρ : Reading X i b, IsChars C art ρ ∧
    ∀ s : X.Sig i, X.side i s = b → _root_.GlobalTheory.Triple.IsGaloisTripleAtSignature C art ρ s
  vec : ∀ i, X.NonzeroIndexPlace i → ∀ s : X.Sig i, Formalism.MainNotions.BlochKatoReduction.Gen.goodE Y i s
  all : Y.sig_all
end Comparison₂
def IsGaloisTripleOfExpansion {X : NTw D.R D.host D.what₂ D.LL0 D.nd} (Y : NExp D.R D.host D.what₂ D.LL0 D.nd X) : Prop :=
  ∃ (C : CharFrame D) (art : Ideles D.host.E →* Gab D.host.E D.nd.Om), _root_.GlobalTheory.Triple.IsGaloisTripleForExpansion C art Y
def IsGaloisTriple (D : D7) : Prop := _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion D.nexp
section ReadingAPI
variable {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw} {b : Bool}
end ReadingAPI
section Chars
variable (C : CharFrame D)
variable {C} {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw} {b : Bool} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om}
end Chars
section Values
variable (μ : HChar D.host.E) (π : D.naut.CG D.R.r) (P : PlE D.host)
end Values
section API
variable {C : CharFrame D} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
  {i : X.Tw} {b : Bool} {ρ : Reading X i b} {s : X.Sig i} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GalE D →* GL (Fin D.R.r) (Qbar (X.l i))} {ν : GalE D →* (X.O0 i)ˣ} {w : D.what₂.places.Pl}
  {red : Zbar (X.l i) →+* FbAt D w}
theorem isTripleAt_of_conj_alt (good : D.nd.goodRow σ) (occurs : D.what₂.isot (X.jS i s) σ ≠ ⊥) (param : IsParam σ π)
    (gal : _root_.UpperTheory.GalS.IsGaloisRepOfN D π (X.l i) ρ.ι r) (shift : ∃ n, IsGal art ρ.κ ρ.ι (shiftChar C) n ν)
    (A : GL (Fin D.R.r) (Qbar (X.l i)))
    (rho : ∀ g, ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (toQ ρ.κ) =
      toQ ρ.κ ((ν g : (X.O0 i)ˣ) : X.O0 i) •
        ((A * r g * A⁻¹ : GL (Fin D.R.r) (Qbar (X.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (X.l i))))
    (hecke : ∀ k P, k ≤ D.R.r → IsSplitPl D.host P → P ∉ X.S0 i → ∃ x : X.O0 i,
      algebraMap (X.O0 i) (X.O i) x = X.hEig i s k P ∧ ρ.toC x = heckeVal (muBase C (X.l i) (jIdx s)) π k P)
    (induces : ρ.Induces w) (residual : IsResidual ρ.ι r σ w red) : _root_.GlobalTheory.Triple.IsGaloisTripleAtSignature C art ρ s := by
  refine ⟨σ, π, (MulAut.conj A).toMonoidHom.comp r, ν, w, red, good, occurs, param,
    _root_.GlobalTheory.Triple.isGaloisRepOfN_of_conj gal A fun _ => rfl, shift, rho, hecke, induces, residual.ss, fun g => ?_, residual.teich⟩
  obtain ⟨p, h1, h2⟩ := residual.charpoly g
  refine ⟨p, h1.trans ?_, h2⟩
  change _ = ((A * r g * A⁻¹ : GL (Fin D.R.r) (Qbar (X.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (X.l i))).charpoly
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
theorem IsGaloisTripleWithReduction.hEig_zero (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) {P : PlE D.host} (hP : IsSplitPl D.host P)
    (hS : P ∉ X.S0 i) : X.hEig i s 0 P = 1 := by
  obtain ⟨x, h1, h2⟩ := h.hecke 0 P (Nat.zero_le _) hP hS
  rw [heckeVal_zero, ← map_one ρ.toC] at h2
  rw [← h1, ρ.toC_injective h2, map_one]
theorem IsGaloisTripleWithReduction.unr_of_notMem (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) {P : PlE D.host} (hS : P ∉ X.S0 i) :
    D.naut.unr (D.naut.locG π P) := h.param.unr P fun k hk => hS (X.placesOver_subset_exceptional i k hk)
variable {Y : NExp D.R D.host D.what₂ D.LL0 D.nd X}
theorem IsGaloisTripleForExpansion.triple (h : _root_.GlobalTheory.Triple.IsGaloisTripleForExpansion C art Y) {i : X.Tw} (hi : X.NonzeroIndexPlace i) (s : X.Sig i) :
    ∃ ρ : Reading X i (X.side i s), IsChars C art ρ ∧ _root_.GlobalTheory.Triple.IsGaloisTripleAtSignature C art ρ s :=
  let ⟨ρ, h1, h2⟩ := h.evidence i hi (X.side i s)
  ⟨ρ, h1, h2 s rfl⟩
theorem IsGaloisTripleOfExpansion.allGood (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Y) : GlobalTheory.TwSys.AllGood Y := let ⟨_, _, h⟩ := h; h.vec
theorem IsGaloisTripleOfExpansion.sig_all (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Y) : Y.sig_all := let ⟨_, _, h⟩ := h; h.all
end API
end GlobalTheory.Triple
end
end

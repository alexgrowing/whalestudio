import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlacesBelowSplitCoprimeConductorOfAdmissible

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom

namespace GlobalTheory.LamTie

instance (priority := low) framePsiFintype (φ : Formalism.HC.Frame) : Fintype φ.Psi := Fintype.ofFinite _

section Host

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def Over4 (w : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  (∃ k, OverP H (H.g k) w) ∨ OverP H H.pde w ∨ OverP H H.pde' w

structure IsAuxiliaryHeckeCharacter (w0 : HeightOneSpectrum (𝓞 H.E)) (c : R.Psi → ℤ) (χ : Formalism.L2.Host.HChar H.E) : Prop where

  unitary : χ.IsUnitary

  triv : χ.TrivOn H.F

  inf : χ.HasInfQ (embPsi H) fun g => (c g : ℚ)

  unr : ∀ w, ¬ Over4 H w → below w ≠ below w0 → χ.UnrAt w

  two : ∀ w, Over4 H w → ExpAt χ w 2

  one : ∀ w, below w = below w0 → ExpAt χ w 1

def cond0 (w0 : HeightOneSpectrum (𝓞 H.E)) : Ideal (OF H.E) :=
  Ideal.span {((H.g 0 * H.g 1 * H.pde * H.pde' : ℕ) : OF H.E)} ^ 2 * (below w0).asIdeal

structure PlacesOk (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)) : Prop where

  referencePlaceOverPrime : OverP H q0 w0

  distinct : [H.g 0, H.g 1, H.pde, H.pde', q0].Nodup

  splits : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr H.E ∧
    ∀ P : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = p

def phi (g : R.Psi) : H.E →+* ℂ := ComplexEmbedding.conjugate (embPsi H g)

end Host

structure LamDat (D : D7) where

  C : CharFrame D

  q0 : ℕ

  w0 : HeightOneSpectrum (𝓞 D.host.E)

  c : Fin D.R.m → D.R.Psi → ℤ

  chi : Fin D.R.m → Formalism.L2.Host.HChar D.host.E

namespace LamDat

variable {D : D7} (Z : LamDat D)

def lam0 (l : ℕ) (j a : Fin D.R.m) : Formalism.L2.Host.HChar D.host.E := Z.C.mu0 j * Z.C.delAt l * (Z.chi a)⁻¹

def kap (j a : Fin D.R.m) (s : ℕ) (g : D.R.Psi) : ℕ := (⌊eExp D j g⌋ + Z.c a g - s).toNat

structure Ok : Prop where

  places : PlacesOk D.host Z.q0 Z.w0

  aux : ∀ a, IsAuxiliaryHeckeCharacter D.host Z.w0 (Z.c a) (Z.chi a)

  big : ∀ j a g, (BlochKatoReduction.Gen.NFun D.R : ℚ) + 1 < eExp D j g + Z.c a g

end LamDat

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def IsThOf (i : X.Tw) (ι : ℂ →+* Kbar X i) (lam : X.abelian₂ i) {I : Type} [Fintype I] (φ : I → D.host.E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (𝔣 : Ideal (OF D.host.E)) (χ : Formalism.L2.Host.HChar D.host.E) : Prop :=
  ∃ u : Kbar X i, u ≠ 0 ∧ ∀ Q, BlochKatoReduction.Gen.QOk X i Q → Finite (PicO (condQ 𝔣 (belowSet Q))) ∧
    ∃ (π : PicO (condQ 𝔣 (belowSet Q)) →* X.RCG i Q) (T : PicO (condQ 𝔣 (belowSet Q)) → ℂ),
      IsRecMap X i Q π ∧ (∀ q, IsClassTerm φ s κ (condQ 𝔣 (belowSet Q)) χ q.out (T q)) ∧
      ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (X.th i Q lam δ) = u * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q)

def IsThEmpty (i : X.Tw) (ι : ℂ →+* Kbar X i) (lam : X.abelian₂ i) {I : Type} [Fintype I] (φ : I → D.host.E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (𝔣 : Ideal (OF D.host.E)) (χ : Formalism.L2.Host.HChar D.host.E) : Prop :=
  ∃ (u : Kbar X i) (T : ℂ), u ≠ 0 ∧ IsToricSum φ s κ 𝔣 χ T ∧
    algebraMap (FractionRing (X.O i)) (Kbar X i) (∑ δ, X.th i ∅ lam δ) = u * ι T

def IsLam (Z : LamDat D) (i : X.Tw) (ι : ℂ →+* Kbar X i) (lam : X.abelian₂ i) (j a : Fin D.R.m) (s : ℕ) : Prop :=
  j.1 + 1 = X.jL i lam ∧ BlochKatoReduction.Gen.SOk X i lam s ∧
    ∀ P, P ∉ X.S0 i → algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι (((Z.lam0 (X.l i) j a).val P : ℂˣ) : ℂ) = 1

def IsLamTie (Z : LamDat D) : Prop :=
  ∀ i, X.NonzeroIndexPlace i → (∀ P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ X.S0 i) ∧
    ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
      ∀ lam : X.abelian₂ i, ∃ (j a : Fin D.R.m) (s : ℕ), IsLam X Z i (atSide X (X.sideL i lam) ι) lam j a s ∧
        IsThOf X i (atSide X (X.sideL i lam) ι) lam (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 (X.l i) j a)

def IsLamTie0 (Z : LamDat D) : Prop :=
  ∀ i, X.NonzeroIndexPlace i → ∀ lam : X.abelian₂ i, ∃ (ι : ℂ →+* Kbar X i) (j a : Fin D.R.m) (s : ℕ), BlochKatoReduction.Gen.SOk X i lam s ∧
    IsThEmpty X i ι lam (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 (X.l i) j a)

end Record

section Examples

example {R : Ranks} (H : Formalism.BasicNotions.Host R) (g : R.Psi) (x : H.E) : phi H g x = (starRingEnd ℂ) (embPsi H g x) := rfl

example {R : Ranks} (H : Formalism.BasicNotions.Host R) (w0 : HeightOneSpectrum (𝓞 H.E)) : (below w0).asIdeal ∣ cond0 H w0 := Dvd.intro_left _ rfl

example {D : D7} (Z : LamDat D) (l : ℕ) (j a : Fin D.R.m) : Z.lam0 l j a * Z.chi a = Z.C.mu0 j * Z.C.delAt l :=
  inv_mul_cancel_right _ _

example {D : D7} (Z : LamDat D) (hZ : Z.Ok) (j a : Fin D.R.m) (s : ℕ) (hs : s ≤ BlochKatoReduction.Gen.NFun D.R + 1) (g : D.R.Psi) :
    (Z.kap j a s g : ℤ) = ⌊eExp D j g⌋ + Z.c a g - s := by
  have h := hZ.big j a g
  have h1 : ((BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 - Z.c a g) ≤ ⌊eExp D j g⌋ := Int.le_floor.2 (by push_cast; linarith)
  have h2 : (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 := by exact_mod_cast hs
  exact Int.toNat_of_nonneg (by omega)

end Examples

end GlobalTheory.LamTie

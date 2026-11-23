import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.Bock

variable (Q q : ℕ) (hq : q ∣ Q) (i : ℤ)

def IsRed (φ : tw Q i ⟶ (restr (ZMod.castHom hq (ZMod q))).obj (tw q i)) : Prop :=
  ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) →
    Sec.map φ (twGen i ζ) = (show Sec ((restr (ZMod.castHom hq (ZMod q))).obj (tw q i)) U from twGen i ξ)

def redS : tw Q i ⟶ (restr (ZMod.castHom hq (ZMod q))).obj (tw q i) := pick (IsRed Q q hq i)

def IsIncl (φ : (restr (ZMod.castHom hq (ZMod q))).obj (tw q i) ⟶ tw Q i) : Prop :=
  ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) →
    Sec.map φ (show Sec ((restr (ZMod.castHom hq (ZMod q))).obj (tw q i)) U from twGen i ξ) = (Q / q) • twGen i ζ

def inclS : (restr (ZMod.castHom hq (ZMod q))).obj (tw q i) ⟶ tw Q i := pick (IsIncl Q q hq i)

def inc (E : Spc) (n : ℤ) : Ht q E n i →+ Ht Q E n i :=
  (HK.post (ZMod Q) ((chains (ZMod Q)).obj E) (inclS Q q hq i) n).comp (restrH (ZMod.castHom hq (ZMod q)) E (tw q i) n)

def IsConn {R : Type} [CommRing R] (S : ShortComplex (Shv R)) (z : Cocycle (res R S.X₃) (res R S.X₁) 1) (s : ℤˣ) : Prop :=
  ∀ (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
    S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
    ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
      CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug S.X₃)) z (zero_add 1)) = s • CohomologyClass.mk w

end GlobalTheory.EtC.Bock

end

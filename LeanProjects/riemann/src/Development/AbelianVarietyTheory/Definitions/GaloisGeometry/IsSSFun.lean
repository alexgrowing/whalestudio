import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.AbelianVarietyTheory.Definitions.Divisors.CrystallineConnectionFormCoboundaryZero
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.LogCris

variable {O : Type} [CommRing O]

abbrev PtOver (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of O)) {k : Type} [CommRing k] (κ : O →+* k) (B : Type)
    [CommRing B] : Type :=
  {z : (k →+* B) × (Spec (CommRingCat.of B) ⟶ X) // z.2 ≫ q = Spec.map (CommRingCat.ofHom (z.1.comp κ))}

def IsSSFun (ϖ : O) (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of O)) {k : Type} [CommRing k] (κ : O →+* k)
    (L : LogFun k (κ ϖ)) : Prop :=
  GlobalTheory.Et.IsStrictlySemistable ϖ q ∧
  ∃ (e : ∀ B : CommRingCat.{0}, L.Pt.obj B ≃ PtOver X q κ B) (U : L.A → X.Opens) (F : ∀ α, L.ι → Γ(X, U α))
    (G : ∀ α β, L.ι → Γ(X, U α ⊓ U β)ˣ),
    (∀ α, IsAffineOpen (U α)) ∧ (⨆ α, U α) = ⊤ ∧
    (∀ α, ∏ i, F α i = (q.appLE ⊤ (U α) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ)) ∧
    (∀ α β i, X.presheaf.map (homOfLE inf_le_left).op (F α i) =
      (G α β i : Γ(X, U α ⊓ U β)) * X.presheaf.map (homOfLE inf_le_right).op (F β i)) ∧
    (∀ α i, F α i ∈ nonZeroDivisors Γ(X, U α)) ∧
    (∀ α (x : X), x ∈ U α → ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (hV : V ≤ U α) (m r : ℕ) (_ : 1 ≤ r)
      (_ : r ≤ m) (c : Fin r ↪ L.ι)
      (ψ : (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < r),
        MvPolynomial.X j) - MvPolynomial.C ϖ}) →+* Γ(X, V)),
      ψ.Etale ∧ ψ.comp (algebraMap O _) = ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ q.appLE ⊤ V le_top).hom ∧
      (∀ j : Fin r, ∃ u : Γ(X, V)ˣ, ψ (Ideal.Quotient.mk _ (MvPolynomial.X (Fin.castLE (by omega) j))) =
        u * X.presheaf.map (homOfLE hV).op (F α (c j))) ∧
      ∀ i, i ∉ Set.range c → IsUnit (X.presheaf.map (homOfLE hV).op (F α i))) ∧
    (∀ {B B' : CommRingCat.{0}} (φ : B ⟶ B') (y : L.Pt.obj B),
      (e B' (L.Pt.map φ y)).1 = (φ.hom.comp (e B y).1.1, Spec.map φ ≫ (e B y).1.2)) ∧
    ∀ {B : CommRingCat.{0}} (y : L.Pt.obj B),
      (e B y).1.1 = L.str y ∧
      ∀ α, (L.In α y ↔ ⊤ ≤ (e B y).1.2 ⁻¹ᵁ U α) ∧
        ∀ (h : ⊤ ≤ (e B y).1.2 ⁻¹ᵁ U α),
          (∀ i, L.f α i y = GlobalTheory.Cris.evalAt (e B y).1.2 (U α) h (F α i)) ∧
          ∀ β (h' : ⊤ ≤ (e B y).1.2 ⁻¹ᵁ (U α ⊓ U β)) i,
            (L.g α β i y : B) = GlobalTheory.Cris.evalAt (e B y).1.2 (U α ⊓ U β) h' (G α β i)

end GlobalTheory.LogCris

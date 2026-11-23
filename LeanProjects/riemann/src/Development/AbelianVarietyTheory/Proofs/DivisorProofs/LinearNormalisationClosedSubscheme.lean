import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem factors_quot_iff {P : Type} [CommRing P] (I : Ideal P) (T : Scheme.{0}) (g : T ⟶ Sp P) :
    (∃ w : T ⟶ Sp (P ⧸ I), w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = g) ↔
      ∀ x ∈ I, g.appTop ((Scheme.ΓSpecIso (CommRingCat.of P)).inv x) = 0 := by
  constructor
  · rintro ⟨w, rfl⟩ x hx
    have e : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of P)).inv x) =
        (Scheme.ΓSpecIso (CommRingCat.of (P ⧸ I))).inv (Ideal.Quotient.mk I x) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, e,
      Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, map_zero]
  · intro h
    let φ : CommRingCat.of P ⟶ Γ(T, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of P)).inv ≫ g.appTop
    let ψ : CommRingCat.of (P ⧸ I) ⟶ Γ(T, ⊤) :=
      CommRingCat.ofHom (Ideal.Quotient.lift I φ.hom (fun x hx => h x hx))
    refine ⟨T.toSpecΓ ≫ Spec.map ψ, ?_⟩
    have e : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ ψ = φ := by ext x; rfl
    rw [Category.assoc, ← Spec.map_comp, e]
    simp only [φ, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]

def normEq {Rg : Type} [CommRing Rg] {mA mB : ℕ} (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤))
    (j : Fin mB) : MvPolynomial (Fin (mA * mB)) Rg :=
  MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom (β j)) -
    ∑ i, MvPolynomial.X (finProdFinEquiv (i, j)) *
      MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom (α i))

theorem appTop_affπ {Rg : Type} [CommRing Rg] {N : ℕ} (a : Γ(Sp Rg, ⊤)) :
    (affπ Rg N).appTop a = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))).inv
      (MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom a)) := by
  conv_lhs => rw [← (Scheme.ΓSpecIso (CommRingCat.of Rg)).hom_inv_id_apply a]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl

theorem normal_iff {Rg : Type} [CommRing Rg] {mA mB : ℕ} (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤))
    (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) :
    Normal (g ≫ affπ Rg (mA * mB)) (matOf g) α β ↔
      ∀ j, g.appTop ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (mA * mB)) Rg))).inv (normEq α β j)) = 0 := by
  refine forall_congr' fun j => ?_
  rw [normEq, map_sub, map_sub, sub_eq_zero, map_sum, map_sum]
  simp only [map_mul, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_affπ, matOf, coord]

end GlobalTheory.HomFixUniv

namespace GlobalTheory.HomFixUniv

theorem normal_closed : ∀ (Rg : Type) [CommRing Rg] (mA mB : ℕ) (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤)), ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), (GlobalTheory.HomFixUniv.Normal (g ≫ affπ Rg (mA * mB)) (matOf g) α β ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  intro Rg _ mA mB α β
  let I : Ideal (MvPolynomial (Fin (mA * mB)) Rg) := Ideal.span (Set.range (normEq α β))
  refine ⟨Sp (MvPolynomial (Fin (mA * mB)) Rg ⧸ I), Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)),
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective, fun T g => ?_⟩
  rw [factors_quot_iff, normal_iff]
  let φ : MvPolynomial (Fin (mA * mB)) Rg →+* Γ(T, ⊤) :=
    g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (mA * mB)) Rg))).inv.hom
  change (∀ j, φ (normEq α β j) = 0) ↔ ∀ x ∈ I, φ x = 0
  constructor
  · intro h x hx
    have hle : I ≤ RingHom.ker φ := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact h j
    exact hle hx
  · intro h j
    exact h _ (Ideal.subset_span ⟨j, rfl⟩)

end GlobalTheory.HomFixUniv

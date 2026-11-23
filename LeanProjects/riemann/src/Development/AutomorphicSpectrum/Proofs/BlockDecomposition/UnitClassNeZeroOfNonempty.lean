import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.ConeOne

variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def resI (x : X) : K →+* X.residueField x :=
  (Spec.preimage (X.fromSpecResidueField x ≫ q)).hom

theorem spec_resI (x : X) :
    Spec.map (CommRingCat.ofHom (resI q x)) = X.fromSpecResidueField x ≫ q := by
  have : CommRingCat.ofHom (resI q x) = Spec.preimage (X.fromSpecResidueField x ≫ q) := rfl
  rw [this, Spec.map_preimage]

def resPt (x : X) : PtOver X q (Ideal.Quotient.mk (⊥ : Ideal K))
    (X.residueField x ⧸ (⊥ : Ideal (X.residueField x))) :=
  ⟨(Ideal.quotientMap ⊥ (resI q x) bot_le,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal (X.residueField x)))) ≫ X.fromSpecResidueField x), by
    rw [Category.assoc, ← spec_resI, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl⟩

def resT (x : X) : Thick (smFun X q) :=
  mkT (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (X.residueField x) (resI q x) ⊥
    (dividedPowersBot _)
    ⟨fun h => absurd rfl h, fun _ => ⟨1, by simp⟩⟩
    ⟨by simp, fun a ha => by
      classical
      have : a = 0 := ha
      subst this
      rw [map_zero, dividedPowersBot_dpow_eq, dividedPowersBot_dpow_eq]
      simp only [true_and]
      split_ifs <;> simp⟩
    (resPt q x) (fun _ => rfl)

end GlobalTheory.CompanionTheory.ConeOne

open GlobalTheory.CompanionTheory.ConeOne in
theorem GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)), Nonempty X →
    oneK q ≠ 0 := by
  intro K _ X q ⟨x⟩ h
  have h1 := (Submodule.Quotient.mk_eq_zero _).1 h
  have h2 : (fun s : ComposableArrows (Thick (smFun X q)) 0 =>
      (1 : (thA (smFun X q)).obj (s.obj (Fin.last 0)))) = 0 := h1
  have h3 := congrFun h2 (ComposableArrows.mk₀ (resT q x))
  exact one_ne_zero (α := X.residueField x) h3

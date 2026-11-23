import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

lemma range_app_iso_comp {X : Scheme.{0}} {P Q E : X.Modules} (e : P ≅ Q) (f : Q ⟶ E)
    (V : X.Opens) : Set.range ((e.hom ≫ f).app V) = Set.range (f.app V) := by
  ext m
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e.hom.app V x, by rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]⟩
  · rintro ⟨y, rfl⟩
    refine ⟨e.inv.app V y, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id_assoc]

theorem secs_powSub {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (E : X.Modules) (hE : E.IsQuasicoherent) (n : ℕ) (V : X.Opens)
    (hV : IsAffineOpen V) :
    secs (powSub I E n) V =
      ((Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(E, V)) :
        Set Γ(E, V)) := by
  rw [← range_idealPowι_app I E hV n, ← range_app_iso_comp
    (Subobject.underlyingIso (idealPowι I E n)) (idealPowι I E n) V]
  unfold secs powSub
  rw [Subobject.underlyingIso_hom_comp_eq_mk]

end GlobalTheory.CompanionTheory.GE

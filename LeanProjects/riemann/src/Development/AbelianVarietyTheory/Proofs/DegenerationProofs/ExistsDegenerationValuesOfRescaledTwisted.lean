import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumOf

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.RescaleValues

theorem vF_psi_rescale {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (q : D.X → (FractionRing R)ˣ) (χ : D.X) {J : (Sp F ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : ∀ ψ : Sp F ⟶ D.P.A.left, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) :
    vF ((TauTwist.rescale D q).psi χ) (jFK (R := R) F) J =
      algebraMap (FractionRing R) F (q χ) * vF (D.psi χ) (jFK (R := R) F) J := by
  obtain ⟨z⟩ : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have e := TauTwist.val_psi_rescale q χ (jFK (R := R) F) (z := z) (J := J) (fun ψ => hJ ψ trivial)
  have e₁ : TauTwist.unitAt (jFK (R := R) F) z (q χ) =
      TorusExt.stalkUnits z (Units.map (algebraMap (FractionRing R) F).toMonoidHom (q χ)) := by
    have h := TauTwist.unitAt_spMap (𝟙 (Sp F)) (algebraMap (FractionRing R) F) z (q χ)
    rw [Category.id_comp] at h
    exact h.trans (TorusExt.gm_unitOn z _)
  refine (GaugeValues.vF_eq hJ z _ _).symm.trans ?_
  refine (congrArg (fun x => (((TorusExt.stalkUnits z).symm x : Fˣ) : F)) (e.trans (congrArg (· * _) e₁))).trans ?_
  refine Eq.trans ?_ (congrArg (_ * ·) (GaugeValues.vF_eq hJ z _ _))
  simp only [map_mul, MulEquiv.symm_apply_apply, Units.val_mul]
  rfl

theorem exists_numOf_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N) (k : ℕ) (β : N.Form k) (u : Fˣ) (q : D.X → (FractionRing R)ˣ), (∀ y, algebraMap (FractionRing R) F (q (ν.eX y)) = ((u ^ (β.be y y / 2) : Fˣ) : F)) → ∃ ν' : NumOf (TauTwist.rescale D q) F (N.twist β u), (∀ y : N.X, ν'.eX y = ν.eX y) ∧ ∀ x : N.A, ν'.eA x = ν.eA x := by
  intro R _ _ D F _ _ N ν k β u q hq
  refine ⟨{ J := ν.J, good := ν.good, th := ν.th, th_gen := ν.th_gen, eA := ν.eA, eX := ν.eX, c_eq := ν.c_eq,
            θ_eq := ν.θ_eq, σ_eq := ν.σ_eq, th_eq := ν.th_eq, ψ_eq := fun (χ : N.X) => ?_ }, fun _ => rfl, fun _ => rfl⟩
  refine Eq.trans ?_ (congrArg (· * _) (vF_psi_rescale D q (ν.eX χ) ν.good).symm)
  show ((N.ψ χ * u ^ (β.be χ χ / 2) : Fˣ) : F) = _
  rw [Units.val_mul, ν.ψ_eq, hq]
  exact (mul_comm _ _).trans (_root_.mul_assoc _ _ _).symm

end GlobalTheory.RescaleValues

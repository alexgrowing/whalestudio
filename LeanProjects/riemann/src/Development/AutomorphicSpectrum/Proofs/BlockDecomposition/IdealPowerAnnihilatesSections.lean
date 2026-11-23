import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem cst_thick_eq_zero {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (V : X.Opens) {r : R}
    (hr : r ∈ I ^ (e + 1)) : AbLaw.cst (p ≫ thick R I e) V r = 0 := by
  have key : AbLaw.cst (p ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))) V =
      (AbLaw.cst p V).comp (Ideal.Quotient.mk (I ^ (e + 1))) := by
    ext a
    have := congrArg (fun q => q.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    rw [this]
  have h0 : AbLaw.cst (p ≫ thick R I e) V r =
      AbLaw.cst (p ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))) V r := rfl
  rw [h0, key, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]

theorem pow_smul_top_secOnR (R : Type) [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (e : ℕ) (M : LB (Y e).left)
    (V : (Y e).left.Opens) :
    I ^ (e + 1) • (⊤ : Submodule R (SecOnR (toR I Y e) M V)) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro r hr s _
  rw [Submodule.mem_bot, SecOnR.smul_def, cst_thick_eq_zero I e (Y e).hom V hr, zero_smul]

end GlobalTheory.CompanionTheory.FormalAlg.Lift

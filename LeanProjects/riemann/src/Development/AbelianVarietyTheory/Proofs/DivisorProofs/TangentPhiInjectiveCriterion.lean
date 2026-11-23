import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt.CnSurj

theorem kappa_smul (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (r : Γ(Sp O, ⊤))
    (s : Γ(GlobalTheory.Conormal.conormal (GlobalTheory.LieVB.sec (zeroSec O M)), ⊤)) :
    kappa O M (r • s) = toO O r • kappa O M s := by
  letI := (isChart O M).algebra
  letI := topModule O M
  exact map_smul ((AugCot.lift ((isChart O M).aug (GlobalTheory.LieVB.sec_hom _)) (sndFn O M)
    (sndFn_der O M)) ∘ₗ ((isChart O M).augCotEquiv (GlobalTheory.LieVB.sec_hom _)).symm.toLinearMap) r s

theorem Phi_smul {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] {A : Over (Sp O)} [GrpObj A]
    (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Wmod A) :
    Phi z h (c • w) = c • Phi z h w := by
  have e : toO O (GlobalTheory.LieVB.cst O c) = c := Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of O)) c
  have h1 := map_smul (QCoh.appLinear (GlobalTheory.LieVB.cotMap z h) ⊤) (GlobalTheory.LieVB.cst O c)
    (show Γ(GlobalTheory.LieVB.omega A, ⊤) from w)
  refine (congrArg (kappa O M) h1).trans ((kappa_smul O M _ _).trans ?_)
  rw [e]
  rfl

theorem cn_surjective (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O))
    [GrpObj A] (t : G.TorsionTower A)
    (hinj : ∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M]
      (z z' : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O M ≫ z' = η[A]),
      (∀ w, Phi z h w = Phi z' h' w) → z = z')
    (hnat : ∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M]
      (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M)
      (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A),
      Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w =
        GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w))
    (n : ℕ) : Function.Surjective (cn t n) := by
  let ε := Bialgebra.counitAlgHom O (G.A n)
  let c : Wmod A →ₗ[O] AugCot ε :=
    { toFun := cn t n
      map_add' := map_add (cn t n)
      map_smul' := fun a w => Phi_smul _ _ a w }
  let N := AugCot ε ⧸ LinearMap.range c
  letI : Module Oᵐᵒᵖ N := opModule O N
  haveI : IsCentralScalar O N := opModule_central O N
  let q : AugCot ε →ₗ[O] N := (LinearMap.range c).mkQ
  let φ := (AugCot.sqZeroEquiv ε N).symm q
  let φ₀ := (AugCot.sqZeroEquiv ε N).symm 0
  have e : φ.1 = φ₀.1 := t.inj n _ _ _ <|
    hinj N _ _ (zeroSec_spOver_y t n φ.1 φ.2) (zeroSec_spOver_y t n φ₀.1 φ₀.2) fun w => by
      refine (hnat N n φ.1 φ.2 w).trans (Eq.trans ?_ (hnat N n φ₀.1 φ₀.2 w).symm)
      change AugCot.sqZeroEquiv ε N φ (c w) = AugCot.sqZeroEquiv ε N φ₀ (c w)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, LinearMap.zero_apply]
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨w, rfl⟩
  have hq : q = 0 := (AugCot.sqZeroEquiv ε N).symm.injective (Subtype.ext e)
  intro x
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range c)).1 (LinearMap.congr_fun hq x)

end GlobalTheory.SqZeroPt.CnSurj

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
open GlobalTheory.LieVB GlobalTheory.Conormal

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

theorem kappa_eq_epsIso (O : Type) [CommRing O]
    (σ : Γ(conormal (sec (zeroSec O O)), ⊤)) :
    kappa O O σ = toO O ((epsIso O).hom.app ⊤ σ) := by
  obtain ⟨b, rfl⟩ := (isChart O O).d_surjective (sec_hom (zeroSec O O)) σ
  rw [kappa_d]
  have hinj := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt O O))).hom).1
  let ε : Γ((TM O O).left, ⊤) := (Scheme.ΓSpecIso (.of (TrivSqZeroExt O O))).inv DualNumber.eps
  have hε : toTsze O O ε = DualNumber.eps := Iso.inv_hom_id_apply _ _
  have hb : b = (TM O O).hom.appLE ⊤ ⊤ le_top (cst O (toTsze O O b).fst) +
      (TM O O).hom.appLE ⊤ ⊤ le_top (cst O (toTsze O O b).snd) * ε := by
    apply hinj
    change toTsze O O b = toTsze O O _
    rw [map_add, map_mul, toTsze_base, toTsze_base, hε, Iso.inv_hom_id_apply,
      Iso.inv_hom_id_apply]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have e0 := d_base (sec_hom (zeroSec O O)) (isChart O O).le (le_preimage_top (TM O O).hom ⊤)
    (cst O (toTsze O O b).fst)
  have e1 := d_base (sec_hom (zeroSec O O)) (isChart O O).le (le_preimage_top (TM O O).hom ⊤)
    (cst O (toTsze O O b).snd)
  have e2 := d_mul (sec_hom (zeroSec O O)) (isChart O O).le
    ((TM O O).hom.appLE ⊤ ⊤ le_top (cst O (toTsze O O b).snd)) ε
  have e3 := appLE_base (sec_hom (zeroSec O O)) (isChart O O).le
    (le_preimage_top (TM O O).hom ⊤) le_rfl (cst O (toTsze O O b).snd)
  have hd : d (sec_hom (zeroSec O O)) (isChart O O).le b =
      cst O (toTsze O O b).snd • d (sec_hom (zeroSec O O)) (isChart O O).le ε := by
    conv_lhs => rw [hb]
    rw [map_add, e0, zero_add, e2, e1, smul_zero, add_zero, e3, GlobalTheory.LB.resG_self]
  have h1 : (epsIso O).hom.app ⊤ (d (sec_hom (zeroSec O O)) (isChart O O).le ε) =
      (1 : Γ(Sp O, ⊤)) := epsIso_d O
  rw [hd]
  have h2 := Scheme.Modules.Hom.app_smul (epsIso O).hom (cst O (toTsze O O b).snd)
    (d (sec_hom (zeroSec O O)) (isChart O O).le ε)
  refine Eq.trans ?_ (congrArg (toO O) h2).symm
  rw [h1]
  change _ = toO O (cst O (toTsze O O b).snd * 1)
  rw [_root_.mul_one, Iso.inv_hom_id_apply]

theorem exists_phi_eq (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A] :
    (GlobalTheory.LieVB.omega A).IsQuasicoherent →
      (∀ (l : Wmod A →ₗ[O] O), ∃ (v : TM O O ⟶ A) (h : zeroSec O O ≫ v = η[A]),
        ∀ w, Phi v h w = l w) := by
  intro hqc l
  let f : Γ(GlobalTheory.LieVB.omega A, ⊤) →ₗ[Γ(Sp O, ⊤)] Γ(Sp O, ⊤) :=
    { toFun := fun w => cst O (l w)
      map_add' := fun w w' => (congrArg (cst O) (l.map_add w w')).trans (map_add _ _ _)
      map_smul' := fun r w => by
        obtain ⟨a, rfl⟩ : ∃ a, r = cst O a := ⟨toO O r, (Iso.hom_inv_id_apply _ _).symm⟩
        have e : l (cst O a • w) = a * l w := l.map_smul a w
        exact (congrArg (cst O) e).trans (map_mul _ _ _) }
  obtain ⟨lam, hlam⟩ := (GlobalTheory.OmegaGlobal.dualApp_top_bijective (GlobalTheory.LieVB.omega A)).2 f
  obtain ⟨x, hx⟩ := GlobalTheory.LieVB.TangentSurj.tangent_surjective O A lam
  refine ⟨x.1, epsZero_comp x, fun w => ?_⟩
  have h1 := dualApp_tangent x (V := ⊤) w
  rw [hx] at h1
  have h2 : GlobalTheory.VB.dualApp lam (le_refl ⊤) w = cst O (l w) := LinearMap.congr_fun hlam w
  refine (kappa_eq_epsIso O _).trans ?_
  exact (congrArg (toO O) (h1.symm.trans h2)).trans (Iso.inv_hom_id_apply _ _)

end GlobalTheory.SqZeroPt

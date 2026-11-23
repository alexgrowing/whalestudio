import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwZ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneralLinearGroupDetMapFinOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyBijectiveOfSupportBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleLiftingLineBundleTransitionUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerLiftedCocycleImageEqPicardClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleOfMapToDegreeOneTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDefectEqOfPowEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDefectGlueQthRootsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerCocycleSubChernClassCoboundaryStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.KumPic

theorem kummer_boundary_picClass : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0), Mono κ →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U))) →
  ∀ (z : Cocycle (res ℤ (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1) (s : ℤˣ),
  (∀ (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0) (ψ : cokernel κ ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 1),
      κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) → cokernel.π κ ≫ ψ = φ ≫ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).d 0 1 →
      ∀ w : Cocycle (sgl (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1, sglι (cokernel κ) ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug (cokernel κ))) z (zero_add 1)) = s • CohomologyClass.mk w) →
  ∀ (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → ∀ y : H ℤ E (cokernel κ) 1,
    HK.post ℤ _ (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) 1 y = picClass L →
    HK.ext ℤ _ z 1 (1 + 1) rfl y = s • restrH (Int.castRingHom (ZMod q)) E (tw q 1) (1 + 1) (c1 q L) := by
  intro q _ κ h0 _ h2 _ _ h5 z s hz E L hE y hy
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_cocycle_lifting_lineBundle_transition_units q (cokernel κ) _ E L hE h5
  have hy' : y = CohomologyClass.mk (zcomp a (Cocycle.ofHom (resAug (cokernel κ))) (add_zero 1)) :=
    (GlobalTheory.T.etaleCohomology_bijective_of_support_bijective ℤ E _ (fun U hU => h5 U (hE U hU)) 1).1 (hy.trans (GlobalTheory.T.kummerLiftedCocycle_image_eq_picardClass _ _ E L a ha).symm)
  haveI : Injective ((res ℤ (twZ q)).X 0) :=
    inferInstanceAs (Injective ((injectiveResolution (twZ q)).cochainComplex.X 0))
  let φ : Gm ⟶ (res ℤ (twZ q)).X 0 := Injective.factorThru (resι ℤ (twZ q)) κ
  have hφ : κ ≫ φ = resι ℤ (twZ q) := Injective.comp_factorThru _ _
  have hd : κ ≫ (φ ≫ (res ℤ (twZ q)).d 0 1) = 0 := by
    rw [← Category.assoc, hφ, PicSpec.resι_d]
  let ψ : cokernel κ ⟶ (res ℤ (twZ q)).X 1 := cokernel.desc κ (φ ≫ (res ℤ (twZ q)).d 0 1) hd
  have hψ : cokernel.π κ ≫ ψ = φ ≫ (res ℤ (twZ q)).d 0 1 := cokernel.π_desc _ _ _
  have hψd : ψ ≫ (res ℤ (twZ q)).d 1 2 = 0 := by
    rw [← cancel_epi (cokernel.π κ), ← Category.assoc, hψ, Category.assoc, HomologicalComplex.d_comp_d,
      comp_zero, comp_zero]
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_cocycle_of_map_to_degreeOne_term (cokernel κ) (res ℤ (twZ q)) ψ hψd
  have hzw := hz φ ψ hφ hψ w hw
  have hext : HK.ext ℤ _ z 1 (1 + 1) rfl y = s • CohomologyClass.mk (zcomp a w rfl) := by
    rw [hy']
    change CohomologyClass.mk (zcomp (zcomp a (Cocycle.ofHom (resAug _)) (add_zero 1)) z rfl) = _
    have hc : zcomp (zcomp a (Cocycle.ofHom (resAug (cokernel κ))) (add_zero 1)) z rfl =
        zcomp a (zcomp (Cocycle.ofHom (resAug _)) z (zero_add 1)) rfl :=
      Cocycle.ext (Cochain.comp_assoc _ _ _ (add_zero 1) (zero_add 1) (by omega))
    rw [hc, ← cpre_mk, hzw]
    rw [Units.smul_def, Units.smul_def, map_zsmul]
    rfl
  rw [hext]
  congr 1
  refine GlobalTheory.T.kummerCocycle_sub_chernClass_coboundary q E L hE φ (GlobalTheory.T.kummerSplittingDefect_glue_qthRoots q φ (GlobalTheory.T.kummerSplittingDefect_eq_of_pow_eq q κ h2 φ hφ)) (cokernel κ) a w (fun U x v hv => ?_)
  obtain ⟨c, hc, hac⟩ := ha U x
  have hU : IsUnit (q : Γ(U, ⊤)) := hE U ⟨x.face 0⟩
  have hpow : ∀ n : ℕ, unitSec (v ^ n) = (n : ℤ) • unitSec v := by
    intro n
    induction n with
    | zero =>
      have := PicSpec.unitSec_mul (1 : (Γ(U, ⊤))ˣ) 1
      rw [mul_one] at this
      simpa using this
    | succ n ih => rw [pow_succ, PicSpec.unitSec_mul, ih]; push_cast; rw [add_smul, one_smul]
  have hcv : c = Sec.map (cokernel.π κ) (unitSec v) := by
    refine (h5 U hU).1 (hc.trans ?_)
    rw [PicSpec.sec_map_comp, cokernel.π_desc, ← hv, hpow]
    exact (map_zsmul (CupSpec.mapHom Gm Gm (unitSec v)) (q : ℤ) (𝟙 Gm)).symm
  rw [hac, PicSpec.sec_map_comp, hw, hcv, PicSpec.sec_map_comp, hψ]
  rfl

end GlobalTheory.EtC.KumPic

end

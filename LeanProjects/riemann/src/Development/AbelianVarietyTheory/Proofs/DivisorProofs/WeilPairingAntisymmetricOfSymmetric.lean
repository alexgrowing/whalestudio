import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

namespace GlobalTheory.WeilAntisymm

theorem weilIs_exchange {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {P : LB (A ⊗ A).left}
    (hP : P.IsLB) (hs : LBIso (swap P) P) {k : ℤ} {T : Over S} {a b : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs (A ⊗ A) P k (CartesianMonoidalCategory.lift a 1) (CartesianMonoidalCategory.lift 1 b) c) :
    Out.WeilIs (A ⊗ A) P k (CartesianMonoidalCategory.lift b 1) (CartesianMonoidalCategory.lift 1 a) c⁻¹ := by
  have e : CartesianMonoidalCategory.lift (snd A A) (fst A A) = (β_ A A).hom := by ext1 <;> simp
  have : IsMonHom (CartesianMonoidalCategory.lift (snd A A) (fst A A)) := e ▸ inferInstance
  have hw : LBIso (lbPow P 1) (P.pull (CartesianMonoidalCategory.lift (snd A A) (fst A A)).left) := by
    refine (CechPic.cls_eq_iff (LB.isLB_linComb hP _ _) (pull_isLB hP _)).1 ?_
    rw [CechPic.cls_lbPow hP, (CechPic.cls_eq_iff (pull_isLB hP _) hP).2 hs]
    simp
  have H := WeilIsogeny.weilIs_pull_hom globalFns_holds (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) hP hP _ hw
    (x := CartesianMonoidalCategory.lift 1 a) (y := CartesianMonoidalCategory.lift b 1) (n := k) (c := c) (by
      rwa [comp_lift, comp_lift, lift_fst, lift_snd, lift_fst, lift_snd])
  rw [Nat.cast_one, _root_.mul_one] at H
  exact CommPairing.weilIs_symm hP H

theorem conv_eq_one {R H : Type} [CommRing R] [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H] [Module.Finite R H]
    [Module.Projective R H] (U : H ⊗[R] H) (hU : TensorProduct.comm R H H U * U = 1)
    (f : CartierDual R H →ₐc[R] H) (hf : ∀ χ, f χ = TensorProduct.rid R _ (χ.ofConv.lTensor _ U)) :
    WithConv.toConv (((CartierDual.bidual R H).symm : _ →ₐc[R] H).comp (CartierDual.map f)) * WithConv.toConv f = 1 := by
  have h₁ : f.toLinearMap = CartierDual.tensorToHom R H H U :=
    LinearMap.ext fun χ => (hf χ).trans (CartierDual.tensorToHom_apply U χ).symm
  have h₂ : (((CartierDual.bidual R H).symm : _ →ₐc[R] H).comp (CartierDual.map f)).toLinearMap =
      CartierDual.tensorToHom R H H (TensorProduct.comm R H H U) :=
    LinearMap.ext fun χ => CartierDual.eq_of_forall_apply fun ψ => by
      rw [CartierDual.apply_tensorToHom_comm, ← CartierDual.apply_tensorToHom, ← h₁]
      exact CartierDual.apply_bidual_symm _ _
  have h₃ := CartierDual.tensorToHom_mul (TensorProduct.comm R H H U) U
  rw [hU, ← h₁, ← h₂] at h₃
  refine WithConv.ofConv_injective (BialgHom.ext fun χ => ?_)
  refine (LinearMap.congr_fun (congrArg WithConv.ofConv h₃) χ).symm.trans ?_
  change χ.ofConv 1 • (1 : H) = algebraMap R H (χ.ofConv 1)
  rw [Algebra.algebraMap_eq_smul_one]

theorem comm_mul_self {R H : Type} [CommRing R] [CommRing H] [Algebra R H] {A : Over (Sp R)} [GrpObj A]
    (hA : IsAbelianScheme A) {P : LB (A ⊗ A).left} (hP : P.IsLB) (hs : LBIso (swap P) P) {k : ℤ} (y : SpAlg R H ⟶ A)
    (U : (H ⊗[R] H)ˣ) (hU : Out.WeilIs (A ⊗ A) P k (T := SpAlg R (H ⊗[R] H))
      (CartesianMonoidalCategory.lift (spOver Algebra.TensorProduct.includeLeft ≫ y) 1)
      (CartesianMonoidalCategory.lift 1 (spOver Algebra.TensorProduct.includeRight ≫ y)) (unitOn U)) :
    TensorProduct.comm R H H U.val * U.val = 1 := by
  have hAA := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  let τ : H ⊗[R] H →ₐ[R] H ⊗[R] H := (Algebra.TensorProduct.comm R H H).toAlgHom
  have h := CommPairing.weilIs_pull globalFns_holds hAA hP (spOver τ) hU
  have e₁ : τ.comp Algebra.TensorProduct.includeLeft = Algebra.TensorProduct.includeRight := AlgHom.ext fun _ => rfl
  have e₂ : τ.comp Algebra.TensorProduct.includeRight = Algebra.TensorProduct.includeLeft := AlgHom.ext fun _ => rfl
  rw [comp_lift, comp_lift, MonObj.comp_one, ← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp, e₁, e₂] at h
  have e := CommutatorPairing.weilIs_unique globalFns_holds hAA hP h (weilIs_exchange hA hP hs hU)
  have m : Units.map (spOver τ).left.appTop.hom.toMonoidHom (unitOn U) =
      unitOn (Units.map (τ : H ⊗[R] H →+* H ⊗[R] H).toMonoidHom U) :=
    Units.ext (congrArg (fun q => q.hom U.val)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (τ : H ⊗[R] H →+* H ⊗[R] H)))).symm
  have inj : Function.Injective (unitOn (R := H ⊗[R] H)) :=
    (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of (H ⊗[R] H))).symm.commRingCatIsoToRingEquiv.toMulEquiv).injective
  exact congrArg Units.val (mul_eq_one_iff_eq_inv.2 (inj ((m.symm.trans e).trans (map_inv _ U).symm)))

theorem bidual_dualHom_eq_neg : GlobalTheory.Published.CubeTheorem → ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (A ⊗ A).left), IsDual A A P → LBIso (swap P) P → ∀ (𝒜 : PDivGroup p K) (t : 𝒜.TorsionTower A) (w : 𝒜 ⟶ 𝒜.dual), IsWeilHom t t P w → 𝒜.bidual.hom ≫ dualHom _ _ w = -w := by
  intro _ p _ K _ A _ hA P hP hs 𝒜 t w hw
  refine eq_neg_of_add_eq_zero_left (hom_ext_conv fun n => ?_)
  obtain ⟨U, hU, hχ⟩ := hw n
  exact conv_eq_one U.val (comm_mul_self hA hP.isLB hs (t.y n) U hU) (w.app n) hχ

end GlobalTheory.WeilAntisymm

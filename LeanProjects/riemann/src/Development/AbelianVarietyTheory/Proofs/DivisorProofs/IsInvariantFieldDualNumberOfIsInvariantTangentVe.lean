import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PreimageTranslate
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvDerBridge

theorem valR_add_of {B : Type} [CommRing B] {Z : Scheme.{0}} (a : Sp B ⟶ Z) {O : Z.Opens} (ha : ⊤ ≤ a ⁻¹ᵁ O)
    (f g : Γ(Z, O)) : valR a O (f + g) = valR a O f + valR a O g := by
  simp only [valR, dif_pos ha, map_add]

theorem valR_mul_of {B : Type} [CommRing B] {Z : Scheme.{0}} (a : Sp B ⟶ Z) {O : Z.Opens} (ha : ⊤ ≤ a ⁻¹ᵁ O)
    (f g : Γ(Z, O)) : valR a O (f * g) = valR a O f * valR a O g := by
  simp only [valR, dif_pos ha, map_mul]

theorem isInvDer_of_isInv : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (v : TanM (𝟙 (Sp K)) A) (u : epsR K ⟶ A) (dd : Fld A.left), u.left = (tv v).left → IsTangent u → IsInv A v dd → GlobalTheory.KS.IsInvDer u dd := by
  intro K _ A _ _ v u dd hu ht hd W f
  have hpre : ((fst (epsR K) A ≫ u) * snd (epsR K) A).left ⁻¹ᵁ W = (snd (epsR K) A).left ⁻¹ᵁ W :=
    GlobalTheory.InvFieldBasis.preimage_translate ht W
  refine GlobalTheory.LogKSBal.ext_valR _ _ fun B _ x hx => ?_
  obtain ⟨β, hβ⟩ : ∃ β : DualNumber K →+* B, x ≫ (fst (epsR K) A).left = spMap β :=
    ⟨(Spec.preimage (x ≫ (fst (epsR K) A).left)).hom, (Spec.map_preimage _).symm⟩
  letI : Algebra K B := (β.comp (algebraMap K (DualNumber K))).toAlgebra
  set e : B := β DualNumber.eps with he_def
  have he : e * e = 0 := by rw [he_def, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  let βa : DualNumber K →ₐ[K] B := { β with commutes' := fun _ => rfl }
  have hβe : βa = GlobalTheory.SqZero.epsTo K e he := DualNumber.algHom_ext (by simp [βa, e])
  have hxw : x ≫ (epsR K ⊗ A).hom = (Chart.sp (R₀ := K) B).hom := by
    rw [← Over.w (fst (epsR K) A), ← Category.assoc, hβ]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  let xt : Chart.sp (R₀ := K) B ⟶ epsR K ⊗ A := Over.homMk x hxw
  let z : Chart.sp (R₀ := K) B ⟶ A := xt ≫ snd (epsR K) A
  have hfst : xt ≫ fst (epsR K) A = Chart.spMap (GlobalTheory.SqZero.epsTo K e he) := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Chart.spMap_left, ← hβe]
    exact hβ
  have hmu : x ≫ ((fst (epsR K) A ≫ u) * snd (epsR K) A).left =
      ((Chart.spMap (GlobalTheory.SqZero.epsTo K e he) ≫ u : Chart.sp (R₀ := K) B ⟶ A) * z).left := by
    rw [← hfst, Category.assoc, ← MonObj.comp_mul]
    rfl
  have hz : ⊤ ≤ z.left ⁻¹ᵁ W := fun p hp => hx hp
  obtain ⟨-, H⟩ := GlobalTheory.Heat.DlogIndep.valR_translate hu ht hd e he z W hz
  rw [GlobalTheory.LogKSBal.valR_pbT x _ hpre.ge hx, hmu, H, valR_add_of x hx, valR_mul_of x hx,
    GlobalTheory.LogKSBal.valR_pbT x _ le_rfl hx, GlobalTheory.LogKSBal.valR_pbT x _ le_rfl hx,
    GlobalTheory.LogKSBal.valR_constFn _ x hx hβ]
  rfl

end GlobalTheory.InvDerBridge

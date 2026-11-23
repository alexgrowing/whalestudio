import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsTorsFrameOfSymLift
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalOfIsTwistPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueSecEqMulGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section
namespace GlobalTheory.Ex.OneGen

open TorsFrame CommPairing

theorem ThG.exists_isTorsFrame_isValueAt : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (m : ℕ), Odd m → ∀ (T : Over S) (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) (y : T ⟶ P.A) (c : Γ(T.left, ⊤)), GlobalTheory.Ex.OneGen.ThG P.A P.L rig m th y c → ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (y ^ m).left) (fun _ => 1)), IsTorsFrame P rig m (y ^ m) τ ∧ IsValueAt P.A P.L ((1 : ℕ) : ℤ) th (y ^ m) (powFrame P.A P.L (y ^ m) τ ((1 : ℕ) : ℤ)) c := by
  intro S _ P rig hr m hm T th y c H
  obtain ⟨hy, t, αT, s₁, θ, hαT, hnT, hs₁, hθ, ht, hc⟩ := H
  have hLaw : Laws := abelianSchemeLaws_all.1
  have hL := P.isLB
  obtain ⟨α₀, h₀⟩ := hLaw.mulPull S P m
  obtain ⟨α, hα, vα⟩ := exists_norm hL hr h₀
  obtain ⟨ν, hν⟩ := exists_gen_negLB hLaw.globalFns S P 1 T
  have e₁ : y.left ≫ (mulA P.A m).left = (y ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have e₂ : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ (snd T P.A).left = T.hom ≫ eSec P.A := by
    rw [← Over.comp_left, lift_snd, GlobalTheory.TorsFrame.one_left]
  have e₃ : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ (translPt P.A θ.pt).left = y.left := by
    rw [← Over.comp_left, translPt, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp, hθ.pt_eq]
    exact congrArg (·.left) (_root_.mul_one y)
  have e₄ : (snd T P.A).left ≫ (mulA P.A m).left = (snd T P.A ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]

  obtain ⟨α', hα', vα'⟩ := exists_gen hL (φ' := ![(snd T P.A).left, (snd T P.A ^ m).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e₄]
      push_cast; rfl)
    (LB.pullGen P.L _ _ α (snd T P.A).left) (DVR.pullGen_isGen _ _ _ _ hα _)

  have eα : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ P.A).left) (z : Z) (J), Good P.L z J →
      val αT r z J = val α (r ≫ (snd T P.A).left) z J := by
    intro Z r z J hJ
    refine (gen_unique hL (fst T P.A).left (ptSecT P.A 1).left NormTheta.ptSec_fst
      (CommPairing.surj_fst hLaw.globalFns P.isAb T) hαT hα' (fun w J hJ => ?_) Z r z J hJ).trans
      ((vα' _ _ z J hJ).trans (val_pull hJ _ _ _))
    have a := val_corr hJ hnT (𝟙 _)
    rw [val_pull hJ, Category.id_comp, Ex.OneGen.val_rigT _ _ w hJ, Category.id_comp] at a
    rw [a, vα' _ _ w J hJ, val_pull hJ, show (ptSecT P.A 1).left ≫ (snd T P.A).left = T.hom ≫ eSec P.A from e₂,
      vα _ _ w J hJ, zpow_sub_one, zpow_natCast]
  obtain ⟨τ, hτ, vτ⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (y ^ m).left) (ε' := fun _ => 1)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, e₃, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen P.L _ _ _ _ (GeneratorPullback.powGen P.L _ _
        (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) rig T.hom) (m ^ 2))
      (LB.invGen P.L _ _ (LB.mulGen P.L _ _ _ _
        (LB.pullGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(m ^ 2 : ℕ), -(m ^ 2 : ℕ)] θ.φ
          (lift (𝟙 T) (1 : T ⟶ P.A)).left) (LB.pullGen P.L _ _ α y.left))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hr _) _)
      (DVR.invGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
        (DVR.pullGen_isGen _ _ _ _ hα _))))
  have c₀ : ∀ (z : T.left) (J), Good P.L z J → val (LB.pullGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left]
      ![(m ^ 2 : ℕ), -(m ^ 2 : ℕ)] θ.φ (lift (𝟙 T) (1 : T ⟶ P.A)).left) (𝟙 T.left) z J =
        tval θ (lift (𝟙 T) (1 : T ⟶ P.A)).left z J := fun z J hJ =>
    (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)

  have vτ' : ∀ (z : T.left) (J), Good P.L z J → val τ (𝟙 T.left) z J =
      val rig T.hom z J ^ (m ^ 2) * (tval θ (lift (𝟙 T) (1 : T ⟶ P.A)).left z J * val α y.left z J)⁻¹ := by
    intro z J hJ
    rw [vτ _ _ z J hJ, val_mul hJ, val_inv, val_mul hJ, c₀ z J hJ, val_powGen, val_pull hJ, val_pull hJ,
      Category.id_comp, Category.id_comp]
  refine ⟨τ, ⟨by rw [← pow_mul, ← sq, hy], hτ, α, hα, corr_of_val hL fun z J hJ => ?_,
    corr_of_val hL fun z J hJ => ?_⟩, ThetaCoord.isValueAt_of_sv hL (EvVal.powFrame_isGen P.A P.L _ τ hτ _)
      fun z J hJ => ?_⟩
  · refine (val_pull hJ _ _ _).trans ((vα _ _ z J hJ).trans (Eq.symm ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ?_) (val_inv _ _)))))
    rw [← Nat.cast_pow, zpow_natCast]; rfl
  · have a : val (powFrame P.A P.L (y ^ m) τ ((m : ℤ) ^ 2)) (𝟙 _) z J = val τ (𝟙 _) z J ^ (m ^ 2) :=
      (map_zpow _ _ _).trans (by rw [← Nat.cast_pow, zpow_natCast]; rfl)
    have b := tval_pow hLaw.globalFns P.isAb hL hν hm hα hy hθ hJ
    rw [GlobalTheory.TorsFrame.one_left, vα _ _ z J hJ] at b
    rw [a, vτ' z J hJ, val_mul hJ, val_pull hJ, GlobalTheory.TorsFrame.val_rigT rig _ z hJ, Category.id_comp, Category.id_comp,
      mul_pow, inv_pow, mul_pow, b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module
  ·
    have p₁ : (ptSecT P.A 1).left ≫ (translT P.A θ.pt).left = (lift (𝟙 T) y).left := by
      rw [ptSecT, ThetaCoord.lift_translT, Category.id_comp, hθ.pt_eq, _root_.mul_one]
    have p₂ : (lift (𝟙 T) y).left ≫ (mulT P.A T m).left = (lift (𝟙 T) (y ^ m)).left :=
      ThetaCoord.lift_mulT _ _ _
    have q₁ := VVRank.sv_of_isTwistPull P.A ht (ptSecT P.A 1).left z hJ
    have q₂ := VVRank.sv_of_isTwistPull P.A hs₁ (lift (𝟙 T) y).left z hJ
    rw [p₁, q₂, p₂, hc z J hJ, Ex.OneGen.val_rigT _ _ z hJ, Category.id_comp] at q₁
    rw [eα _ _ z J hJ, show (lift (𝟙 T) y).left ≫ (snd T P.A).left = y.left by rw [← Over.comp_left, lift_snd]] at q₁
    have v₁ : val (powFrame P.A P.L (y ^ m) τ ((1 : ℕ) : ℤ)) (𝟙 T.left) z J = val τ (𝟙 T.left) z J :=
      (map_zpow _ _ _).trans (zpow_one _)
    rw [v₁, vτ' z J hJ]
    rw [zpow_natCast, show val θ.φ (ptSecT P.A 1).left z J = tval θ (lift (𝟙 T) (1 : T ⟶ P.A)).left z J from rfl] at q₁
    have hu := (tval θ (lift (𝟙 T) (1 : T ⟶ P.A)).left z J * val α y.left z J).inv_mul
    rw [Units.val_mul] at hu
    rw [Units.val_mul, ← _root_.mul_assoc, q₁]
    linear_combination (-(VVRank.sv P.A th (lift (𝟙 T) (y ^ m)).left z J)) * hu

end GlobalTheory.Ex.OneGen
end

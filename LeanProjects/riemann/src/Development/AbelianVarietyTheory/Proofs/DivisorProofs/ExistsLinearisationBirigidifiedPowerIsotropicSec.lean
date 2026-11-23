import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationInvariantRigidifiedBundle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleTranslationInvariantFirstFactoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleTranslationInvariantSecondFactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationIsosCommuteOfCommutatorPairingOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationProdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.IsoLin

variable {S : Scheme.{0}}

theorem transl_mul' {G : Over S} [GrpObj G] (x y : 𝟙_ (Over S) ⟶ G) :
    Hecke.transl (x * y) = Hecke.transl x ≫ Hecke.transl y := by
  simp only [Hecke.transl, comp_mul, Category.comp_id, Category.id_comp]
  rw [← Category.assoc _ (toUnit G) y, toUnit_unique (_ ≫ toUnit G) (toUnit G), _root_.mul_assoc]

theorem transl_comm {G : Over S} [GrpObj G] [IsCommMonObj G] (x y : 𝟙_ (Over S) ⟶ G) :
    Hecke.transl x ≫ Hecke.transl y = Hecke.transl y ≫ Hecke.transl x := by
  rw [← transl_mul', ← transl_mul', _root_.mul_comm]

theorem lift_mul_lift' {A : Over S} [GrpObj A] (a b c d : 𝟙_ (Over S) ⟶ A) :
    (lift (a * c) (b * d) : 𝟙_ (Over S) ⟶ G2 A) = lift a b * lift c d := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp]

theorem surj_appTop {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) :
    Function.Surjective (fst A A).left.appTop.hom ∧ Function.Surjective (snd A A).left.appTop.hom := by
  have h2 := (GlobalTheory.globalFns_holds S (G2 A) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA)).2
  have w1 : (G2 A).hom = (fst A A).left ≫ A.hom := (Over.w (fst A A)).symm
  have w2 : (G2 A).hom = (snd A A).left ≫ A.hom := (Over.w (snd A A)).symm
  refine ⟨?_, ?_⟩
  · rw [w1, Scheme.Hom.comp_appTop] at h2
    exact Function.Surjective.of_comp h2
  · rw [w2, Scheme.Hom.comp_appTop] at h2
    exact Function.Surjective.of_comp h2

theorem rig_lbPow {X Y : Scheme.{0}} (P : LB X) (hP : P.IsLB) (m : ℕ) (f : Y ⟶ X)
    (h : ∃ t : (P.pull f).Gen, t.IsGen) : ∃ t : ((Hecke.lbPow P m).pull f).Gen, t.IsGen := by
  have hQ : (Hecke.lbPow P m).IsLB := DVR.linComb_isLB P hP _ _
  have h0 := (GlobalTheory.CechPic.cls_eq_zero_iff (DVR.linComb_isLB P hP (fun _ : PUnit => f) (fun _ => 1))).2 h
  refine (GlobalTheory.CechPic.cls_eq_zero_iff (DVR.linComb_isLB _ hQ (fun _ : PUnit => f) (fun _ => 1))).1 ?_
  have e : GlobalTheory.CechPic.cls _ hQ = (m : ℤ) • GlobalTheory.CechPic.cls P hP := by
    refine (GlobalTheory.CechPic.cls_linComb hP (fun _ : Fin m => 𝟙 X) (fun _ => 1) hQ).trans ?_
    simp [GlobalTheory.CechPic.pull_id]
  rw [GlobalTheory.CechPic.cls_pull hQ f, e, map_zsmul,
    ← GlobalTheory.CechPic.cls_pull hP f (DVR.linComb_isLB P hP (fun _ : PUnit => f) (fun _ => 1)), h0, smul_zero]

end GlobalTheory.IsoLin

namespace GlobalTheory.IsoLin

theorem exists_linearisation_isotropic : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (m : ℕ) (H : Subgroup (𝟙_ (Over S) ⟶ A)), (∀ h ∈ H, ∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (toUnit A ≫ h) (𝟙 A)).left).Gen, t.IsGen) → (∀ h ∈ H, ∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (𝟙 A) (toUnit A ≫ h)).left).Gen, t.IsGen) → (∀ h₁ ∈ H, ∀ h₂ ∈ H, Out.WeilIs (G2 A) (GlobalTheory.UPel.HT.Hecke.lbPow P m) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 A) (lift 1 h₂) 1) → ∃ u : ∀ a : H × H, LB.Gen (LB.LinComb (GlobalTheory.UPel.HT.Hecke.lbPow P m) (K := Fin 2) ![𝟙 (G2 A).left, (GlobalTheory.UPel.HT.Hecke.transl (lift a.1.1 a.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left] ![1, -1]), (∀ a, (u a).IsGen) ∧ ∀ a c, LB.Gen.Corr (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ _ _ (u (a * c)) (LB.mulGen (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ _ _ (u a) (LB.pullGen (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ (u c) (GlobalTheory.UPel.HT.Hecke.transl (lift a.1.1 a.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left)) := by
  intro S A _ _ hA P hP hr1 hr2 m H hH1 hH2 hW
  have hQ : (Hecke.lbPow P m).IsLB := DVR.linComb_isLB P hP _ _
  have q1 := rig_lbPow P hP m _ hr1
  have q2 := rig_lbPow P hP m _ hr2
  obtain ⟨sf, ss⟩ := surj_appTop hA
  have hm1 : ∀ a c : H, (lift ((a * c : H) : 𝟙_ (Over S) ⟶ A) 1 : 𝟙_ (Over S) ⟶ G2 A) = lift (a : 𝟙_ (Over S) ⟶ A) 1 * lift (c : 𝟙_ (Over S) ⟶ A) 1 := by
    intro a c
    rw [← lift_mul_lift', _root_.mul_one, Subgroup.coe_mul]
  have hm2 : ∀ a c : H, (lift 1 ((a * c : H) : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S) ⟶ G2 A) = lift 1 (a : 𝟙_ (Over S) ⟶ A) * lift 1 (c : 𝟙_ (Over S) ⟶ A) := by
    intro a c
    rw [← lift_mul_lift', _root_.mul_one, Subgroup.coe_mul]
  obtain ⟨v₁, hv₁, cv₁⟩ := GlobalTheory.MumLin.exists_linearisation A.left (G2 A).left (fst A A).left
    (lift (𝟙 A) (1 : A ⟶ A)).left (by rw [← Over.comp_left, lift_fst, Over.id_left]) sf
    (Hecke.lbPow P m) hQ q2 H (fun a => (Hecke.transl (lift (a : 𝟙_ (Over S) ⟶ A) 1 : 𝟙_ (Over S) ⟶ G2 A)).left)
    (fun a => (Hecke.transl (a : 𝟙_ (Over S) ⟶ A)).left)
    (fun a c => by simp only [hm1, transl_mul', Over.comp_left])
    (fun a c => by simp only [Subgroup.coe_mul, transl_mul', Over.comp_left])
    (fun a => by
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp [Hecke.transl, MonObj.mul_comp, MonObj.comp_mul])
    (fun a => GlobalTheory.T.birigidified_bundle_translation_invariant_first_factor S A hA _ hQ q1 q2 a (hH1 a a.2))
  obtain ⟨v₂, hv₂, cv₂⟩ := GlobalTheory.MumLin.exists_linearisation A.left (G2 A).left (snd A A).left
    (lift (1 : A ⟶ A) (𝟙 A)).left (by rw [← Over.comp_left, lift_snd, Over.id_left]) ss
    (Hecke.lbPow P m) hQ q1 H (fun a => (Hecke.transl (lift 1 (a : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S) ⟶ G2 A)).left)
    (fun a => (Hecke.transl (a : 𝟙_ (Over S) ⟶ A)).left)
    (fun a c => by simp only [hm2, transl_mul', Over.comp_left])
    (fun a c => by simp only [Subgroup.coe_mul, transl_mul', Over.comp_left])
    (fun a => by
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp [Hecke.transl, MonObj.mul_comp, MonObj.comp_mul])
    (fun a => GlobalTheory.T.birigidified_bundle_translation_invariant_second_factor S A hA _ hQ q1 q2 a (hH2 a a.2))
  exact GlobalTheory.T.exists_linearization_prod (G2 A).left (Hecke.lbPow P m) hQ H H _ _
    (fun p => (Hecke.transl (lift (p.1 : 𝟙_ (Over S) ⟶ A) (p.2 : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S) ⟶ G2 A)).left)
    (fun p => by
      show _ = (Hecke.transl _ ≫ Hecke.transl _).left
      rw [← transl_mul', ← lift_mul_lift', _root_.mul_one, _root_.one_mul])
    (fun a b => by rw [← Over.comp_left, ← Over.comp_left, transl_comm])
    (fun a c => by simp only [hm1, transl_mul', Over.comp_left])
    (fun a c => by simp only [hm2, transl_mul', Over.comp_left])
    v₁ v₂ hv₁ hv₂ cv₁ cv₂
    (fun a b => GlobalTheory.T.translation_isos_commute_of_commutatorPairing_one S (G2 A) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) _ hQ _ _ (v₁ a) (v₂ b) (hv₁ a) (hv₂ b) (hW a a.2 b b.2))

end GlobalTheory.IsoLin

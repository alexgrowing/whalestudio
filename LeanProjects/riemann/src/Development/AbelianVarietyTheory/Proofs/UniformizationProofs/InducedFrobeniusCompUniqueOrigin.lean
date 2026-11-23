import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaOperatorsProjectiveRepresentation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EndoEqOfSections

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.IndComp

section Twist

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A] {L : LB A.left}

theorem twist_unique (hL : L.IsLB) {ψ : T ⊗ A ⟶ T ⊗ A} {n : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ ≫ snd _ _).left] ![n, -n])}
    {t u u' : LB.Sec (LPow A L n T)} (h : IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α t u)
    (h' : IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α t u') : u = u' := by
  have e : ∀ j, u.f j = u'.f j := fun j => sec_ext_val hL (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => n)
    (fun y J hJ => (VVRank.sv_of_isTwistPull A h (𝟙 _) y hJ).trans (VVRank.sv_of_isTwistPull A h' (𝟙 _) y hJ).symm) j
  obtain ⟨a, _⟩ := u
  obtain ⟨b, _⟩ := u'
  obtain rfl : a = b := funext e
  rfl

theorem exists_twist_comp (hL : L.IsLB) (ψ ψ' : T ⊗ A ⟶ T ⊗ A) (n : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ ≫ snd _ _).left] ![n, -n]))
    (α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ' ≫ snd _ _).left] ![n, -n]))
    (hα : α.IsGen) (hα' : α'.IsGen) :
    ∃ β : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, ((ψ ≫ ψ') ≫ snd _ _).left] ![n, -n]), β.IsGen ∧
      ∀ t u v : LB.Sec (LPow A L n T), IsTwistPull A L ψ' (ψ' ≫ snd _ _) rfl n n α' t u →
        IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α u v →
        IsTwistPull A L (ψ ≫ ψ') ((ψ ≫ ψ') ≫ snd _ _) rfl n n β t v := by
  obtain ⟨β, hβ, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, ((ψ ≫ ψ') ≫ snd _ _).left]) (ε' := ![n, -n])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, zpow_neg, Over.comp_left, Category.assoc]
      rw [_root_.mul_assoc, inv_mul_cancel_left])
    (LB.mulGen L _ _ _ _ α (LB.pullGen L _ _ α' ψ.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hα (DVR.pullGen_isGen _ _ _ _ hα' _))
  refine ⟨β, hβ, fun t u v hu hv' => VVRank.isTwistPull_of_sv A hL hβ fun y J hJ => ?_⟩
  rw [VVRank.sv_of_isTwistPull A hv' (𝟙 _) y hJ, VVRank.sv_of_isTwistPull A hu _ y hJ, hv _ _ y J hJ, val_mul hJ,
    val_pull hJ, Units.val_mul, _root_.mul_assoc, Over.comp_left _ _ _ ψ ψ', Category.assoc]

theorem exists_twist_id (hL : L.IsLB) (n : ℤ) :
    ∃ β : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (𝟙 (T ⊗ A) ≫ snd _ _).left] ![n, -n]), β.IsGen ∧
      ∀ t : LB.Sec (LPow A L n T), IsTwistPull A L (𝟙 _) (𝟙 _ ≫ snd _ _) rfl n n β t t := by
  obtain ⟨β, hβ, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (𝟙 (T ⊗ A) ≫ snd _ _).left]) (ε' := ![n, -n])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, Category.id_comp,
        mul_inv_cancel]
      exact Fintype.prod_empty _)
    (LB.oneGen L (Y := (T ⊗ A).left))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  refine ⟨β, hβ, fun t => VVRank.isTwistPull_of_sv A hL hβ fun y J hJ => ?_⟩
  rw [hv _ _ y J hJ, val_one, Units.val_one, _root_.one_mul, Over.id_left, Category.comp_id]

end Twist

theorem indAt_comp_unique : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p p' p'' : QkPt D.toPre F N) (ψ ψ' : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)), IndAt U.toUnifPre F N p ψ → (IndAt U.toUnifPre F N p' ψ' → QkAdd p p' p'' → IndAt U.toUnifPre F N p'' (ψ ≫ ψ')) ∧ (QkPt.Equiv D.toPre F p p' → IndAt U.toUnifPre F N p' ψ) ∧ (4 ≤ N → IndAt U.toUnifPre F N p ψ' → ψ = ψ') ∧ (p'.y = 0 → p'.g.IsZero → IndAt U.toUnifPre F N p' (𝟙 _)) := by
  intro hL R _ _ _ I hR D A G _ _ _ U F _ _ _ N hN p p' p'' ψ ψ' hψ
  have hG := hL.1.globalFns
  obtain ⟨Φ, hrel, -, hrat, hequ, hadd, hone⟩ := PhiProj.phi_projective hL R I hR D F N hN
  refine ⟨fun hψ' hs => ⟨by rw [Category.assoc, hψ'.1, hψ.1], fun w₀ hw₀ => ?_⟩, fun he => ⟨hψ.1, fun w₀ hw₀ => ?_⟩,
    fun h4 hψ' => ?_, fun hy hg => ⟨Category.id_comp _, fun w₀ hw₀ => ?_⟩⟩
  · obtain ⟨α, w, hα, hw, h⟩ := hψ.2 w₀ hw₀
    obtain ⟨α', w', hα', hw', h'⟩ := hψ'.2 w₀ hw₀
    obtain ⟨w'', hw'', hΦ⟩ := hadd p p' p'' w w' hw hw' hs
    obtain ⟨β, hβ, hc⟩ := exists_twist_comp A.isLB ψ ψ' (N : ℤ) α α' hα hα'
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine ⟨β, w'', hβ, hw'', fun t t' s s' ht ht' H => ?_⟩
    obtain ⟨u, hu⟩ := VVRank.exists_isTwistPull A.A (hm := rfl) A.isLB hα' t
    obtain ⟨v, hv⟩ := VVRank.exists_isTwistPull A.A (hm := rfl) A.isLB hα u
    obtain rfl : v = t' := twist_unique A.isLB (hc t u v hu hv) H
    have e₁ := ((hrel p' w' hw').2 _ _).1 (h' t u s _ ht ((he u _).2 rfl) hu)
    have e₂ := ((hrel p w hw).2 _ _).1 (h u v _ s' ((he u _).2 rfl) ht' hv)
    refine ((hrel p'' w'' hw'').2 _ _).2 ?_
    rw [hΦ, LinearMap.comp_apply, ← e₁, e₂]
  · obtain ⟨α, w, hα, hw, h⟩ := hψ.2 w₀ hw₀
    obtain ⟨w', hw', hΦ⟩ := hequ p p' w hw he
    refine ⟨α, w', hα, hw', fun t t' s s' ht ht' H => ((hrel p' w' hw').2 _ _).2 ?_⟩
    rw [hΦ]
    exact ((hrel p w hw).2 _ _).1 (h t t' s s' ht ht' H)
  · obtain ⟨w₀, hw₀⟩ := U.ext
    obtain ⟨α, w, hα, hw, h⟩ := hψ.2 w₀ hw₀
    obtain ⟨α', w', hα', hw', h'⟩ := hψ'.2 w₀ hw₀
    obtain ⟨c, hc, hΦ⟩ := hrat p w w' hw hw'
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine AutUniq.endo_eq_of_sections hL R A F N h4 ψ ψ' hψ.1 hψ'.1 α α' hα hα'
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc)) fun t t₁ t₂ h₁ h₂ j => ?_
    have e₁ := ((hrel p w hw).2 _ _).1 (h t t₁ _ _ ((he t _).2 rfl) ((he t₁ _).2 rfl) h₁)
    have e₂ := ((hrel p w' hw').2 _ _).1 (h' t t₂ _ _ ((he t _).2 rfl) ((he t₂ _).2 rfl) h₂)
    rw [hΦ, LinearMap.smul_apply, ← e₁] at e₂
    exact congrArg (fun x => LB.Sec.f x j) (e.injective (e₂.trans (e.map_smul c t₁).symm))
  · obtain ⟨w, hw⟩ := (CoefBasic.coef_basic R D.toPre F N p'.g).2.1 hg.1
    obtain ⟨β, hβ, hc⟩ := exists_twist_id (T := TFK (R := R) F) A.isLB (N : ℤ)
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine ⟨β, w, hβ, hw.1, fun t t' s s' ht ht' H => ((hrel p' w hw.1).2 _ _).2 ?_⟩
    obtain rfl : t = t' := twist_unique A.isLB (hc t) H
    rw [hone p' w hy hg hw]
    exact ((he _ _).1 ht').symm.trans ((he _ _).1 ht)

end GlobalTheory.UT.IndComp

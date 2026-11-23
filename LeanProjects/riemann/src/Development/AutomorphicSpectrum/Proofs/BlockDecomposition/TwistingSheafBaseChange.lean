import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsTautologicalLineAt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeTwistingSheaf

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_chartHom {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (N : ℕ) (j : Fin (N + 1)) :
    ∃ c : ChartR R N j →+* ChartR R' N j,
      chart R' N j ≫ GlobalTheory.ProjSpace.baseChange N φ = spMap c ≫ chart R N j ∧
      ∀ k, c (ratio R N j k) = ratio R' N j k := by
  have key : ∀ (s : MvPolynomial (Fin (N + 1)) R') (_ : s = MvPolynomial.X j)
      (hd : s ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R' 1),
      ∃ ψ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R') s →+* ChartR R' N j,
        chart R' N j = spMap ψ ≫ Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R') s hd one_pos ∧
        ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R') (hf),
          ψ (HomogeneousLocalization.Away.mk _ hd n f hf) =
            HomogeneousLocalization.Away.mk _ (X_mem R' N j) n f hf := by
    rintro _ rfl hd
    refine ⟨RingHom.id _, ?_, fun _ _ _ => rfl⟩
    have e : spMap (RingHom.id (ChartR R' N j)) = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp]
    rfl
  obtain ⟨ψ, h1, h2⟩ := key (GlobalTheory.ProjSpace.gradedMap N φ (MvPolynomial.X j)) (MvPolynomial.map_X φ j)
    ((GlobalTheory.ProjSpace.gradedMap N φ).2 (X_mem R N j))
  refine ⟨ψ.comp (HomogeneousLocalization.Away.map (GlobalTheory.ProjSpace.gradedMap N φ) (MvPolynomial.X j)), ?_, fun k => ?_⟩
  · rw [h1, Category.assoc, GlobalTheory.ProjSpace.baseChange, Proj.awayι_comp_map _ _ one_pos _ (X_mem R N j),
      ← Spec.map_comp_assoc]
    rfl
  · change ψ (HomogeneousLocalization.Away.map (GlobalTheory.ProjSpace.gradedMap N φ) (MvPolynomial.X j) _) = _
    rw [ratio, HomogeneousLocalization.Away.map_mk, h2]
    simp [ratio]

theorem isTwistingSheaf_pullback {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{0}} (p : X ⟶ Sp R)
    (D : E.LineData X) (hO : IsTautologicalLine p D) :
    IsTautologicalLine (pullback.snd p (spMap φ)) (D.pb (pullback.fst p (spMap φ))) := by
  obtain ⟨N, i, hi, hp, het, s, hs, hu⟩ := hO
  have H := GlobalTheory.ProjSpace.isPullback_baseChange N φ
  have hw : (pullback.fst p (spMap φ) ≫ i) ≫ PSpace.str R N = pullback.snd p (spMap φ) ≫ spMap φ := by
    rw [Category.assoc, hp]
    exact pullback.condition
  obtain ⟨i', hi1, hi2⟩ : ∃ i' : pullback p (spMap φ) ⟶ PSpace R' N,
      i' ≫ GlobalTheory.ProjSpace.baseChange N φ = pullback.fst p (spMap φ) ≫ i ∧
      i' ≫ PSpace.str R' N = pullback.snd p (spMap φ) :=
    ⟨H.lift _ _ hw, H.lift_fst _ _ hw, H.lift_snd _ _ hw⟩
  have Hl : IsPullback i' (pullback.fst p (spMap φ)) (GlobalTheory.ProjSpace.baseChange N φ) i := by
    refine IsPullback.of_right (h₁₂ := PSpace.str R' N) (v₁₃ := spMap φ) (h₂₂ := PSpace.str R N) ?_ hi1 H.flip
    rw [hi2, hp]
    exact (IsPullback.of_hasPullback p (spMap φ)).flip
  have hc : IsClosedImmersion i' :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) Hl.flip hi
  choose c hc1 hc2 using fun j => exists_chartHom φ N j
  have hm : ∀ j, (pullback.fst i' (chart R' N j) ≫ pullback.fst p (spMap φ)) ≫ i =
      (pullback.snd i' (chart R' N j) ≫ spMap (c j)) ≫ chart R N j := fun j => by
    rw [Category.assoc, Category.assoc, ← hc1, ← hi1, ← Category.assoc, pullback.condition, Category.assoc]
  let m : ∀ j, pullback i' (chart R' N j) ⟶ pullback i (chart R N j) := fun j => pullback.lift _ _ (hm j)
  have hm1 : ∀ j, m j ≫ pullback.fst i (chart R N j) =
      pullback.fst i' (chart R' N j) ≫ pullback.fst p (spMap φ) := fun j => pullback.lift_fst _ _ _
  have hm2 : ∀ j, m j ≫ pullback.snd i (chart R N j) =
      pullback.snd i' (chart R' N j) ≫ spMap (c j) := fun j => pullback.lift_snd _ _ _
  have hl : ∀ j, (m j ≫ s j) ≫ D.f = pullback.fst i' (chart R' N j) ≫ pullback.fst p (spMap φ) := fun j => by
    rw [Category.assoc, hs, hm1]
  refine ⟨N, i', hc, hi2, ?_, fun j => pullback.lift (m j ≫ s j) (pullback.fst i' (chart R' N j)) (hl j),
    fun j => pullback.lift_snd _ _ _, ?_⟩
  · change Etale (pullback.snd D.f (pullback.fst p (spMap φ)))
    infer_instance
  · intro V j k a b h
    have h₀ : (a ≫ m j) ≫ pullback.fst i (chart R N j) = (b ≫ m k) ≫ pullback.fst i (chart R N k) := by
      rw [Category.assoc, Category.assoc, hm1, hm1, ← Category.assoc, ← Category.assoc, h]
    have e := hu V j k (a ≫ m j) (b ≫ m k) h₀
    have ueq : ∀ {a₁ a₂ b₁ b₂ : V ⟶ D.Y} (_ : a₁ = a₂) (_ : b₁ = b₂) (h₁ : a₁ ≫ D.f = b₁ ≫ D.f)
        (h₂ : a₂ ≫ D.f = b₂ ≫ D.f), D.u a₁ b₁ h₁ = D.u a₂ b₂ h₂ := by
      intro a₁ a₂ b₁ b₂ ha hb h₁ h₂
      subst ha hb
      rfl
    have nat : ∀ x, (spMap (c j)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (ChartR R N j))).inv.hom x) =
        (Scheme.ΓSpecIso (CommRingCat.of (ChartR R' N j))).inv.hom (c j x) := fun x =>
      (congrArg (fun f => f.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (c j)))).symm
    have hs₂ : (a ≫ m j) ≫ pullback.snd i (chart R N j) =
        (a ≫ pullback.snd i' (chart R' N j)) ≫ spMap (c j) := by
      rw [Category.assoc, hm2, Category.assoc]
    refine (congrArg Units.val (ueq (by simp) (by simp) _ _)).trans (e.trans ?_)
    rw [hs₂, Scheme.Hom.comp_appTop]
    change (a ≫ pullback.snd i' (chart R' N j)).appTop.hom ((spMap (c j)).appTop.hom _) = _
    rw [nat, hc2]

end GlobalTheory.CompanionTheory.ConeTwistingSheaf

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearChangeEulerProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveOfTrivAxes
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyAmpleClosedImmersion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KernelNear

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem evc_symm {P : LB (G ⊗ G).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd G G) (fst G G)).left))
    {Y : Over S} (a b : Y ⟶ G) : evc hP a b = evc hP b a := by
  have e := congrArg (CechPic.pull (lift b a).left) ((cls_eq_iff hP (pull_isLB hP _)).2 hs)
  rw [cls_pull hP _ (pull_isLB hP _), ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd] at e
  exact e.symm

theorem evc_eq_zero_of_triv {P : LB (G ⊗ G).left} (hP : P.IsLB) {T : Over S} {x : T ⟶ G}
    (hx : Triv (P.pull (lift (snd G T ≫ x) (fst G T)).left)) {Y : Over S} (t : Y ⟶ T) (w : Y ⟶ G) :
    evc hP (t ≫ x) w = 0 := by
  have e := congrArg (CechPic.pull (lift w t).left) ((triv_ev_iff hP _ _).1 hx)
  rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e

theorem memKL_of_triv {P : LB (G ⊗ G).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd G G) (fst G G)).left))
    (a₁ : IsAdditive P) (a₂ : IsAdditive (AbDual.swap P)) {T : Over S} {x : T ⟶ G}
    (hx : Triv (P.pull (lift (snd G T ≫ x) (fst G T)).left)) :
    MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) x := by
  have hL : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  have hD : (Out.translDiff G (P.pull (lift (𝟙 G) (𝟙 G)).left) x).IsLB := LB.isLB_linComb hL _ _
  have hdiag : ∀ {Y : Over S} (y : Y ⟶ G), CechPic.pull y.left (cls _ hL) = evc hP y y := fun y => by
    rw [cls_pull hP _ hL, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
    rfl
  have z : cls _ hD = 0 := by
    have e₁ := pull_translDiff hL x hD (fst T G) (snd T G)
    rw [lift_fst_snd, Over.id_left, pull_id, hdiag, hdiag] at e₁
    rw [e₁, (isAdditive_iff hP).1 a₁, (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).1 a₂,
      (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).1 a₂, evc_eq_zero_of_triv hP hx, evc_eq_zero_of_triv hP hx,
      evc_symm hP hs (snd T G) (fst T G ≫ x), evc_eq_zero_of_triv hP hx]
    simp
  intro p
  refine ⟨⊤, trivial, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  rw [cls_pull hD, z, map_zero]

end GlobalTheory.KernelNear

namespace GlobalTheory.KernelNear

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

theorem exists_finite_kernel_near : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ W : S'.Opens, (∀ V : S'.Opens, V ≤ W → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) → ∀ s ∈ W, ∃ (V₀ : S'.Opens) (Z : Over S') (i : Z ⟶ G), s ∈ V₀ ∧ Mono i ∧ IsFinite (Z.hom ∣_ V₀) ∧ (∀ T : Over S', Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ z : T ⟶ Z, z ≫ i = 1) ∧ (∀ (T : Over S') (a b : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i) * (b ≫ i)) ∧ (∀ (T : Over S') (a : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i)⁻¹) ∧ (∀ (T : Over S') (x : T ⟶ G), Set.range T.hom.base ⊆ (V₀ : Set S') → (∃ c : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, c.IsGen) → ∃ z : T ⟶ Z, z ≫ i = x) ∧ (∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧ ∃ c : (P.pull (lift (snd G (Over.mk (U.ι ≫ T.hom)) ≫ (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T) ≫ z ≫ i) (fst G (Over.mk (U.ι ≫ T.hom)))).left).Gen, c.IsGen) := by
  intro S' _ G _ _ P hG hP h₁ h₂ hs W hW s hsW
  obtain ⟨V₀, hV₀, hsV, hVW⟩ := exists_isAffineOpen_mem_and_subset (X := S') (U := W) hsW
  obtain ⟨D, _, Q, h, hDab, q, -, hh, e⟩ :=
    GlobalTheory.DualHomPull.exists_dual_hom S' G G (𝟙 G) P hG hG inferInstance hP h₁ h₂
  obtain ⟨a₁, a₂⟩ := GlobalTheory.CubeAxes.additive_of_triv_axes hG hP h₁ h₂
  have hD : ∀ {Y : Over S'} (a b : Y ⟶ G), evc hP a b = evc q.isLB a (b ≫ h) := fun a b => by
    have e' := (cls_eq_iff (pull_isLB hP _) (pull_isLB q.isLB _)).2 e
    rw [MonoidalCategory.id_tensorHom_id, Over.id_left, cls_pull hP _ (pull_isLB hP _), pull_id,
      cls_pull q.isLB _ (pull_isLB q.isLB _)] at e'
    rw [evc, e', ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, ← Category.assoc, lift_snd]
    rfl
  have K : ∀ {T : Over S'} (x : T ⟶ G), Triv (P.pull (lift (snd G T ≫ x) (fst G T)).left) ↔ x ≫ h = 1 := by
    intro T x
    rw [triv_ev_iff hP, evc_symm hP hs, hD, Category.assoc]
    refine ⟨fun hx => q.eq_one _ ((triv_ev_iff q.isLB _ _).2 hx), fun hx => ?_⟩
    rw [hx, MonObj.comp_one]
    exact evc_one_right q.isLB q.zero _
  have : Mono (η[D]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
  have kerh : ∀ {T : Over S'} (z : T ⟶ pullback h (η[D])), (z ≫ pullback.fst h (η[D])) ≫ h = 1 := fun z => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, toUnit_unique (z ≫ pullback.snd _ _) (toUnit _)]
    rfl
  have fac : ∀ {T : Over S'} (x : T ⟶ G), x ≫ h = 1 → ∃ z : T ⟶ pullback h (η[D]), z ≫ pullback.fst h (η[D]) = x :=
    fun x hx => ⟨pullback.lift x (toUnit _) (by rw [hx]; rfl), pullback.lift_fst _ _ _⟩
  have hcl : IsClosedImmersion (pullback.fst h (η[D])).left := by
    have hpb := (IsPullback.of_hasPullback h (η[D])).map (Over.forget S')
    have := hDab.proper
    have : IsClosedImmersion ((η[D]).left ≫ D.hom) := by
      rw [Over.w (η[D])]
      exact (inferInstance : IsClosedImmersion (𝟙 S'))
    have : IsClosedImmersion (η[D]).left := IsClosedImmersion.of_comp _ D.hom
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip this
  refine ⟨V₀, pullback h (η[D]), pullback.fst h (η[D]), hsV, inferInstance,
    GlobalTheory.T.relatively_ample_closed_immersion S' G P hG hP V₀ hV₀ (hW V₀ fun _ hx => hVW hx) _ _ hcl
      (fun T z _ => memKL_of_triv hP hs a₁ a₂ ((K _).2 (kerh z))), ?_, ?_, ?_, ?_, ?_⟩
  · intro T _
    exact fac 1 (MonObj.one_comp h)
  · intro T a b _
    refine fac _ ?_
    rw [MonObj.mul_comp, kerh, kerh, _root_.mul_one]
  · intro T a _
    refine fac _ ?_
    rw [GrpObj.inv_comp, kerh, inv_one]
  · intro T x _ hx
    exact fac x ((K x).1 hx)
  · intro T z _ p
    refine ⟨⊤, trivial, (K _).2 ?_⟩
    rw [Category.assoc, Category.assoc, ← Category.assoc z, kerh, MonObj.comp_one]

end GlobalTheory.KernelNear

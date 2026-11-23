import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLatticesIsoFormsProportionalRamification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordinateEqUnitMulPsiQuotient
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.TraitPull

theorem isMonomial_pull {V R : Type} [CommRing V] [IsDomain V] [CommRing R] [IsDomain R]
    {Dg : DegPre V} {Dg' : DegPre R} {ϖ : V} {β : LinearMap.BilinForm ℤ Dg.X} (hm : IsMonomial Dg ![ϖ] ![β])
    (h : V →+* R) (ε : Dg'.X ≃+ Dg.X)
    (hc : ∀ y r, PsiCoord Dg (ε y) r → ∃ u : Rˣ, PsiCoord Dg' y (u * h r)) :
    IsMonomial Dg' ![h ϖ]
      ![β.compl₁₂ (ε : Dg'.X →+ Dg.X).toIntLinearMap (ε : Dg'.X →+ Dg.X).toIntLinearMap] := by
  intro y
  obtain ⟨u, n, hn, hy⟩ := hm (ε y)
  obtain ⟨u', hu'⟩ := hc y _ hy
  refine ⟨u' * Units.map h.toMonoidHom u, n, Fin.forall_fin_one.2 (hn 0), ?_⟩
  have e : (u' : R) * h ((u : V) * ∏ i, ![ϖ] i ^ n i) =
      ((u' * Units.map h.toMonoidHom u : Rˣ) : R) * ∏ i, ![h ϖ] i ^ n i := by
    simp [Fin.prod_univ_one, map_mul, map_pow]
    ring
  exact e ▸ hu'

theorem exists_pull_unif : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (h : T.V →+* R) (hK : FractionRing T.V →+* FractionRing R), IsLocalHom h → (∀ a, hK (algebraMap T.V _ a) = algebraMap R _ (h a)) → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (_ : Unif (maximalIdeal R) D A G) (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left) (ε : D.toPre.X ≃+ T.D.toPre.X), IsSemiAbelian G ∧ IsGrpPullback A.A F.univ.A (spMap hK ≫ T.y) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧ ∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) (h T.ϖ) ^ (T.β (ε a) (ε b')) := by
  intro g n o _ ζ F T R _ _ _ hB hdvr h hK hl hhK
  have hinj : Function.Injective h := by
    intro a b hab
    have e := congrArg (algebraMap R (FractionRing R)) hab
    rw [← hhK, ← hhK] at e
    exact IsFractionRing.injective T.V (FractionRing T.V) (hK.injective e)
  have hϖ : h T.ϖ ≠ 0 := fun e => T.irr.ne_zero (hinj (e.trans (map_zero h).symm))
  have hRC := TraitUniq.isCN_of_base hB
  obtain ⟨κ, hκ, hκβ⟩ := TraitUniq.genFib T h hK hhK
  have hα := hκ.comp T.cart
  have w₁ := hα.1.w
  let α₂B := pullback.map ((Over.pullback (jK R)).obj ((Over.pullback (spMap h)).obj T.G)).hom
    ((Over.pullback (jK R)).obj ((Over.pullback (spMap h)).obj T.G)).hom F.univ.A.hom F.univ.A.hom
    (κ ≫ T.α) (κ ≫ T.α) (spMap hK ≫ T.y) w₁.symm w₁.symm
  have hsqB : IsSquare (κ ≫ T.α) α₂B := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨D', A', U', ε, L, hLl, hL, hΛ, hc⟩ := TraitUniq.pull T hRC h hinj hl hK _ _
    (isGrpPullback_pullback T.G (spMap h)) κ hκ hκβ α₂B hsqB
  haveI := U'.gen_hom
  haveI : IsMonHom U'.gen.symm.hom := inferInstanceAs (IsMonHom U'.gen.inv)
  have hgi := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso U'.gen.symm
  have hα' := (hgi.comp hα).congr (Category.id_comp _) rfl
  let H : G2 A'.A ⟶ G2 ((Over.pullback (jK R)).obj ((Over.pullback (spMap h)).obj T.G)) :=
    lift (fst A'.A A'.A ≫ U'.gen.inv) (snd A'.A A'.A ≫ U'.gen.inv)
  have hP := F.univ.isLB
  have hAL := A'.isLB
  have hΛA : (abelian₂ A'.A A'.L).IsLB := LB.isLB_linComb hAL _ _
  have hΛB : (abelian₂ _ L).IsLB := LB.isLB_linComb hLl _ _
  have e1 : GlobalTheory.CechPic.pull U'.gen.hom.left (GlobalTheory.CechPic.cls _ hAL) = GlobalTheory.CechPic.cls _ hLl := by
    rw [← GlobalTheory.CechPic.cls_pull hAL _ (pull_isLB hAL _)]
    exact (GlobalTheory.CechPic.cls_eq_iff _ hLl).2
      (LBIso.trans (pull_isLB hAL _) (pull_isLB U'.LG.isLB _) hLl U'.ext hL.symm)
  have hgi' : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have e2 : GlobalTheory.CechPic.cls _ hAL = GlobalTheory.CechPic.pull U'.gen.inv.left (GlobalTheory.CechPic.cls _ hLl) := by
    rw [← e1, ← GlobalTheory.CechPic.pull_comp, hgi', GlobalTheory.CechPic.pull_id]
  have eB : GlobalTheory.CechPic.cls _ hΛB = GlobalTheory.CechPic.pull α₂B (GlobalTheory.CechPic.cls _ hP) := by
    rw [← GlobalTheory.CechPic.cls_pull hP _ (pull_isLB hP _)]
    exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 hΛ
  have cA : GlobalTheory.CechPic.cls _ hΛA = GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls _ hAL) (fst A'.A A'.A) (snd A'.A A'.A) :=
    GlobalTheory.CechPic.cls_cube_two hAL _ _ hΛA
  have cB : GlobalTheory.CechPic.cls _ hΛB = GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls _ hLl) (fst _ _) (snd _ _) :=
    GlobalTheory.CechPic.cls_cube_two hLl _ _ hΛB
  have eA : GlobalTheory.CechPic.cls _ hΛA = GlobalTheory.CechPic.pull (H.left ≫ α₂B) (GlobalTheory.CechPic.cls _ hP) := by
    rw [cA, e2, GlobalTheory.CechPic.lam_pull, GlobalTheory.CechPic.pull_comp, ← eB, cB, GlobalTheory.CechPic.pull_lam, lift_fst, lift_snd]
  refine ⟨_, inferInstance, inferInstance, D', A', U', U'.gen.inv.left ≫ κ ≫ T.α, H.left ≫ α₂B, ε,
    IsSemiAbelian.pullback (spMap h) T.G T.semi, hα', ⟨?_, ?_⟩,
    (GlobalTheory.CechPic.cls_eq_iff hΛA (pull_isLB hP _)).1 (eA.trans (GlobalTheory.CechPic.cls_pull hP _ _).symm), ?_⟩
  · rw [Category.assoc, hsqB.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc]
  · rw [Category.assoc, hsqB.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc]
  · intro a b' x hx
    obtain ⟨x₁, h₁⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord D'.toPre (a + b')
    obtain ⟨x₂, h₂⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord D'.toPre a
    obtain ⟨x₃, h₃⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord D'.toPre b'
    obtain ⟨u₀, hu₀⟩ := GlobalTheory.TauCoordQuot.main R D'.toPre a b' x x₁ x₂ x₃ hx h₁ h₂ h₃
    obtain ⟨r₁, c₁, e₁⟩ :=
      GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top D' _) h₁
    obtain ⟨r₂, c₂, e₂⟩ :=
      GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top D' _) h₂
    obtain ⟨r₃, c₃, e₃⟩ :=
      GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top D' _) h₃
    have hm := isMonomial_pull T.mono h ε hc
    obtain ⟨u, hu⟩ := hm.tau (fun i y z => by fin_cases i; exact T.symm (ε y) (ε z))
      (Fin.forall_fin_one.2 hϖ) c₂ c₃ c₁
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, LinearMap.compl₁₂_apply,
      AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_coe] at hu
    refine ⟨u₀ * u, ?_⟩
    have key : algebraMap R (FractionRing R) (u₀ : R) * algebraMap R (FractionRing R) r₁ *
        (algebraMap R (FractionRing R) r₂)⁻¹ * (algebraMap R (FractionRing R) r₃)⁻¹ =
        algebraMap R (FractionRing R) (u₀ : R) * (algebraMap R (FractionRing R) r₁ /
          (algebraMap R (FractionRing R) r₂ * algebraMap R (FractionRing R) r₃)) := by
      rw [div_eq_mul_inv, mul_inv]; ring
    rw [hu₀, e₁, e₂, e₃, key, hu]
    simp only [Units.val_mul, map_mul]
    ring

end GlobalTheory.Poinc.TraitPull

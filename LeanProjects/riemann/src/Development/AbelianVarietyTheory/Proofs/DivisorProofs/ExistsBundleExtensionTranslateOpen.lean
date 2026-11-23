import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyOfTrivialModEpsilon
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum
open GlobalTheory.CechPic

theorem exists_ext_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (L : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left), L.IsLB → ExtLam G L PP →
    ∀ (O : G.left.Opens) (N : LB O.toScheme), N.IsLB →
    LBIso (N.pull (pullback.fst O.ι (pullback.fst G.hom (jK R)))) (L.pull (pullback.snd O.ι (pullback.fst G.hom (jK R)))) →
    ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, ∃ N' : LB ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).toScheme, N'.IsLB ∧
      LBIso (N'.pull (pullback.fst ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).ι (pullback.fst G.hom (jK R))))
        (L.pull (pullback.snd ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).ι (pullback.fst G.hom (jK R)))) := by
  intro R _ _ G _ _ L PP hL hExt O N hN hNL a
  have hPP : PP.IsLB := hExt.1
  let GK := (Over.pullback (jK R)).obj G
  let J := pullback.fst G.hom (jK R)
  let T := (𝟙 G * (toUnit G ≫ a)).left
  let V := T ⁻¹ᵁ O
  let σ := (lift (𝟙 G) (toUnit G ≫ a)).left
  obtain ⟨N', hN', hc⟩ := cls_surj (pull (T ∣_ O) (cls N hN) - pull (V.ι ≫ σ) (cls PP hPP))
  refine ⟨N', hN', ?_⟩
  let p₁ := pullback.fst V.ι J
  let p₂ := pullback.snd V.ι J
  rw [← cls_eq_iff (pull_isLB hN' _) (pull_isLB hL _), cls_pull hN', cls_pull hL, hc]

  have hNL' : pull (pullback.fst O.ι J) (cls N hN) = pull (pullback.snd O.ι J) (cls L hL) := by
    rw [← cls_pull hN, ← cls_pull hL]
    exact (cls_eq_iff (pull_isLB hN _) (pull_isLB hL _)).2 hNL

  obtain ⟨κ₂, hκ, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (jK R) G GK J (isGrpPullback_pullback G (jK R))
  have hLamc : lam (cls L hL) (fst GK GK) (snd GK GK) = pull κ₂ (cls PP hPP) := by
    rw [← cls_cube_two hL (fst GK GK) (snd GK GK) (LB.isLB_linComb hL _ _), ← cls_pull hPP κ₂ (pull_isLB hPP _)]
    exact (cls_eq_iff (LB.isLB_linComb hL _ _) (pull_isLB hPP _)).2 (hExt.2 κ₂ hκ)

  have hw : p₁ ≫ V.ι ≫ G.hom = p₂ ≫ GK.hom ≫ jK R := by
    rw [← Category.assoc, pullback.condition, Category.assoc]
    exact congrArg (p₂ ≫ ·) pullback.condition
  let Ty : Over (Sp (FractionRing R)) := Over.mk (p₂ ≫ GK.hom)
  let y : Ty ⟶ GK := Over.homMk p₂ rfl
  have haw : a.left ≫ G.hom = 𝟙 _ := by simpa using Over.w a
  let aK : 𝟙_ (Over (Sp (FractionRing R))) ⟶ GK :=
    Over.homMk (pullback.lift (jK R ≫ a.left) (𝟙 _) (by rw [Category.assoc, haw]; simp)) (pullback.lift_snd _ _ _)
  let aY : Ty ⟶ GK := toUnit Ty ≫ aK
  have hzero : ∀ (z : 𝟙_ (Over (Sp (FractionRing R))) ⟶ GK) (c : Pic GK.left), pull (toUnit Ty ≫ z).left c = 0 := by
    intro z c
    rw [Over.comp_left, pull_comp, GlobalTheory.DualOpen.pic_sp_local_eq_zero (FractionRing R) (pull z.left c), map_zero]
  have haY : aY.left ≫ J = p₁ ≫ V.ι ≫ G.hom ≫ a.left := by
    have : aY.left = (p₂ ≫ GK.hom) ≫ aK.left := rfl
    rw [this, Category.assoc, show aK.left ≫ J = jK R ≫ a.left from pullback.lift_fst _ _ _, ← Category.assoc,
      ← Category.assoc, ← Category.assoc]
    simp only [Category.assoc]
    rw [← Category.assoc p₁, ← Category.assoc (p₁ ≫ V.ι), Category.assoc p₁, hw]
    simp only [Category.assoc]

  have hsq : (lift y aY).left ≫ κ₂ = p₁ ≫ V.ι ≫ σ := by
    apply pullback.hom_ext
    · show ((lift y aY).left ≫ κ₂) ≫ (fst G G).left = (p₁ ≫ V.ι ≫ σ) ≫ (fst G G).left
      rw [Category.assoc, hκ.1, ← Category.assoc, ← Over.comp_left, lift_fst]
      simp only [Category.assoc, σ, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id]
      exact pullback.condition.symm
    · show ((lift y aY).left ≫ κ₂) ≫ (snd G G).left = (p₁ ≫ V.ι ≫ σ) ≫ (snd G G).left
      rw [Category.assoc, hκ.2, ← Category.assoc, ← Over.comp_left, lift_snd, haY]
      show p₁ ≫ V.ι ≫ G.hom ≫ a.left = (p₁ ≫ V.ι ≫ (lift (𝟙 G) (toUnit G ≫ a)).left) ≫ (snd G G).left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Over.toUnit_left]
  have hlam : pull (p₁ ≫ V.ι ≫ σ) (cls PP hPP) = @id (Pic (pullback V.ι J)) (pull (y * aY).left (cls L hL)) - pull p₂ (cls L hL) := by
    have h := congrArg (pull (lift y aY).left) hLamc
    rw [pull_lam, lift_fst, lift_snd, ← pull_comp, hsq] at h
    rw [← h, lam, hzero, show (1 : Ty ⟶ GK) = toUnit Ty ≫ 1 from (MonObj.comp_one _).symm, hzero]
    simp only [sub_zero, add_zero]
    rfl

  let u : Over.mk (Ty.hom ≫ jK R) ⟶ G := Over.homMk (p₁ ≫ V.ι) (by simpa [Ty] using hw)
  have hmul : (y * aY).left ≫ J = p₁ ≫ V.ι ≫ T := by
    have e := (isGrpPullback_pullback G (jK R)).2 Ty y aY u (u ≫ toUnit G ≫ a) (pullback.condition (f := V.ι) (g := J))
      (by rw [haY, Over.comp_left, Over.comp_left, Over.toUnit_left]; show (p₁ ≫ V.ι) ≫ _ = _; simp only [Category.assoc])
    have e' : u * (u ≫ toUnit G ≫ a) = u ≫ (𝟙 G * (toUnit G ≫ a)) := by rw [MonObj.comp_mul, Category.comp_id]
    rw [← e, e', Over.comp_left]
    exact Category.assoc _ _ _
  have hq : (p₁ ≫ (T ∣_ O)) ≫ O.ι = (y * aY).left ≫ J := by
    rw [Category.assoc, morphismRestrict_ι, hmul]
  have hN2 := congrArg (pull (pullback.lift _ _ hq)) hNL'
  rw [← pull_comp, ← pull_comp, pullback.lift_fst, pullback.lift_snd] at hN2
  rw [map_sub, ← pull_comp, ← pull_comp, hN2, hlam]
  exact sub_sub_cancel _ _

end GlobalTheory.Mum

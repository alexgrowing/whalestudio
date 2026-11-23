import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianTorsionFiniteAndClosedPointFiniteOrde

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomExt

theorem comp_pow_eq_one_of_pullback_hom {X T Z : Scheme.{0}} (g : T ⟶ X) {G G' Γ : Over X}
    [GrpObj G] [GrpObj G'] (F : (Over.pullback g).obj G ⟶ (Over.pullback g).obj G') [IsMonHom F]
    (p : Γ ⟶ G) (q : Γ ⟶ G') (c : Z ⟶ Γ.left) (s : Z ⟶ pullback G.hom g)
    (h₁ : s ≫ pullback.fst G.hom g = c ≫ p.left)
    (h₂ : s ≫ F.left ≫ pullback.fst G'.hom g = c ≫ q.left) (n : ℕ)
    (h : c ≫ (p ^ n).left = c ≫ (1 : Γ ⟶ G).left) :
    c ≫ (q ^ n).left = c ≫ (1 : Γ ⟶ G').left := by

  let pc : Over.mk (c ≫ Γ.hom) ⟶ Γ := Over.homMk c
  let ps : Over.mk (s ≫ pullback.snd G.hom g) ⟶ (Over.pullback g).obj G := Over.homMk s
  have ht : (Over.mk (s ≫ pullback.snd G.hom g)).hom ≫ g = c ≫ Γ.hom := by
    simp only [Over.mk_hom, Category.assoc, ← pullback.condition, reassoc_of% h₁, Over.w]
  have hp : GlobalTheory.TorsionLift.ptsEquiv g G _ _ ht ps = pc ≫ p := by
    apply Over.OverMorphism.ext
    rw [GlobalTheory.TorsionLift.ptsEquiv_left]
    simpa [ps, pc] using h₁
  have hq : GlobalTheory.TorsionLift.ptsEquiv g G' _ _ ht (ps ≫ F) = pc ≫ q := by
    apply Over.OverMorphism.ext
    rw [GlobalTheory.TorsionLift.ptsEquiv_left]
    simpa [ps, pc] using h₂
  have h1 : (1 : Over.mk (c ≫ Γ.hom) ⟶ G) = pc ≫ 1 := (MonObj.comp_one pc).symm
  have hpn : (pc ≫ p) ^ n = 1 := by
    rw [← MonObj.comp_pow, h1]
    apply Over.OverMorphism.ext
    exact h
  have hps : ps ^ n = 1 := by
    apply (GlobalTheory.TorsionLift.ptsEquiv g G _ _ ht).injective
    rw [map_pow, hp, hpn, map_one]
  have hqn : (pc ≫ q) ^ n = 1 := by
    rw [← hq, ← map_pow, ← MonObj.pow_comp, hps, MonObj.one_comp, map_one]
  have key : pc ≫ q ^ n = pc ≫ 1 := by
    rw [MonObj.comp_pow, hqn, MonObj.comp_one]
  exact congrArg (fun x => Over.Hom.left x) key

theorem exists_iso_pullback_pullback {X T Z : Scheme.{0}} (p : Z ⟶ T) (f : T ⟶ X) (r : Z ⟶ X)
    (h : p ≫ f = r) (G : Over X) [GrpObj G] :
    ∃ e : (Over.pullback r).obj G ≅ (Over.pullback p).obj ((Over.pullback f).obj G),
      IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst (pullback.snd G.hom f) p ≫ pullback.fst G.hom f =
        pullback.fst G.hom r := by
  subst h
  refine ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.pullCompIso p f G, inferInstance, ?_⟩
  have key := congrArg (fun x => Over.Hom.left x)
    (conjugateEquiv_counit (Over.mapPullbackAdj (p ≫ f))
      ((Over.mapPullbackAdj p).comp (Over.mapPullbackAdj f)) (Over.mapComp p f).symm.hom G)
  have e : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pullCompIso p f G).hom.left =
      ((conjugateEquiv (Over.mapPullbackAdj (p ≫ f))
        ((Over.mapPullbackAdj p).comp (Over.mapPullbackAdj f)) (Over.mapComp p f).symm.hom).app
          G).left := rfl
  rw [e]
  simpa [Adjunction.comp_counit_app] using key

private lemma pullback_map_left_comp_fst {S S' : Scheme.{0}} (φ : S' ⟶ S) {A B : Over S} (F : A ⟶ B) :
    ((Over.pullback φ).map F).left ≫ pullback.fst B.hom φ = pullback.fst A.hom φ ≫ F.left := by
  simp
  exact pullback.lift_fst _ _ _

theorem exists_hom_along_dvr
    (H : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
      [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'],
      IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶
        (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
    {X U : Scheme.{0}} (j : U ⟶ X) {G G' : Over X} [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') [IsMonHom f]
    (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
    [Algebra T K] [IsFractionRing T K] (a : Sp T ⟶ G.left) (c : Sp K ⟶ pullback G.hom j)
    (hc : c ≫ pullback.fst G.hom j = spMap (algebraMap T K) ≫ a) :
    ∃ (F : (Over.pullback (a ≫ G.hom)).obj G ⟶ (Over.pullback (a ≫ G.hom)).obj G')
      (s : Sp T ⟶ pullback G.hom (a ≫ G.hom)), IsMonHom F ∧
      s ≫ pullback.fst G.hom (a ≫ G.hom) = a ∧ s ≫ pullback.snd G.hom (a ≫ G.hom) = 𝟙 _ ∧
      spMap (algebraMap T K) ≫ s ≫ F.left ≫ pullback.fst G'.hom (a ≫ G.hom) =
        c ≫ f.left ≫ pullback.fst G'.hom j := by
  have huj : (c ≫ pullback.snd G.hom j) ≫ j = spMap (algebraMap T K) ≫ (a ≫ G.hom) := by
    rw [Category.assoc, ← pullback.condition, reassoc_of% hc]
  obtain ⟨e₁, he₁, hf₁⟩ := exists_iso_pullback_pullback (c ≫ pullback.snd G.hom j) j _ huj G
  obtain ⟨e₁', he₁', hf₁'⟩ := exists_iso_pullback_pullback (c ≫ pullback.snd G.hom j) j _ huj G'
  obtain ⟨e₂, he₂, hf₂⟩ :=
    exists_iso_pullback_pullback (spMap (algebraMap T K)) (a ≫ G.hom) _ rfl G
  obtain ⟨e₂', he₂', hf₂'⟩ :=
    exists_iso_pullback_pullback (spMap (algebraMap T K)) (a ≫ G.hom) _ rfl G'
  let fK := e₂.inv ≫ e₁.hom ≫ (Over.pullback (c ≫ pullback.snd G.hom j)).map f ≫ e₁'.inv ≫ e₂'.hom
  have hfK : IsMonHom fK := inferInstance
  obtain ⟨F, ⟨hF, hFK⟩, -⟩ := H T K ((Over.pullback (a ≫ G.hom)).obj G)
    ((Over.pullback (a ≫ G.hom)).obj G')
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (a ≫ G.hom) G hG)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (a ≫ G.hom) G' hG') fK hfK
  have hs : a ≫ G.hom = 𝟙 _ ≫ a ≫ G.hom := (Category.id_comp _).symm
  refine ⟨F, pullback.lift a (𝟙 _) hs, hF, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩

  have hK : (spMap (algebraMap T K) ≫ pullback.lift a (𝟙 _) hs) ≫
      ((Over.pullback (a ≫ G.hom)).obj G).hom = 𝟙 _ ≫ spMap (algebraMap T K) := by
    show (spMap (algebraMap T K) ≫ pullback.lift a (𝟙 _) hs) ≫ pullback.snd G.hom (a ≫ G.hom) = _
    rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  set σK := pullback.lift _ _ hK with hσK
  have inv_fst₁' : e₁'.inv.left ≫ pullback.fst G'.hom (spMap (algebraMap T K) ≫ a ≫ G.hom) =
      pullback.fst (pullback.snd G'.hom j) (c ≫ pullback.snd G.hom j) ≫ pullback.fst G'.hom j := by
    rw [← hf₁', ← Category.assoc, ← Over.comp_left, e₁'.inv_hom_id]
    simp
  have inv_fst₂ : e₂.inv.left ≫ pullback.fst G.hom (spMap (algebraMap T K) ≫ a ≫ G.hom) =
      pullback.fst (pullback.snd G.hom (a ≫ G.hom)) (spMap (algebraMap T K)) ≫
        pullback.fst G.hom (a ≫ G.hom) := by
    rw [← hf₂, ← Category.assoc, ← Over.comp_left, e₂.inv_hom_id]
    simp
  have hpt : σK ≫ e₂.inv.left ≫ e₁.hom.left ≫ pullback.fst _ _ = c := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      erw [hf₁]
      rw [inv_fst₂, hσK]
      erw [pullback.lift_fst_assoc]
      rw [Category.assoc, pullback.lift_fst, hc]
    · have hcond : pullback.fst (((Over.pullback j).obj G).hom) (c ≫ pullback.snd G.hom j) ≫
          pullback.snd G.hom j = pullback.snd _ _ ≫ c ≫ pullback.snd G.hom j := pullback.condition
      have hw₁ : e₁.hom.left ≫
          pullback.snd (((Over.pullback j).obj G).hom) (c ≫ pullback.snd G.hom j) =
          pullback.snd G.hom (spMap (algebraMap T K) ≫ a ≫ G.hom) := Over.w e₁.hom
      have hw₂ : e₂.inv.left ≫ pullback.snd G.hom (spMap (algebraMap T K) ≫ a ≫ G.hom) =
          pullback.snd (((Over.pullback (a ≫ G.hom)).obj G).hom) (spMap (algebraMap T K)) :=
        Over.w e₂.inv
      simp only [Category.assoc]
      rw [hcond, reassoc_of% hw₁, reassoc_of% hw₂, hσK, pullback.lift_snd_assoc,
        Category.id_comp]
  have step : spMap (algebraMap T K) ≫ pullback.lift a (𝟙 _) hs ≫ F.left =
      σK ≫ fK.left ≫ pullback.fst _ _ := by
    rw [← hFK, hσK, pullback_map_left_comp_fst, pullback.lift_fst_assoc, Category.assoc]
  have hmap : ((Over.pullback (c ≫ pullback.snd G.hom j)).map f).left ≫
      pullback.fst (pullback.snd G'.hom j) (c ≫ pullback.snd G.hom j) =
      pullback.fst (((Over.pullback j).obj G).hom) (c ≫ pullback.snd G.hom j) ≫ f.left :=
    pullback_map_left_comp_fst _ f
  rw [reassoc_of% step]
  simp only [fK, Over.comp_left, Category.assoc]
  erw [hf₂']
  rw [inv_fst₁', reassoc_of% hmap, reassoc_of% hpt]

end GlobalTheory.HomExt

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalSymmetricExtension
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.CubicalPackage

theorem surjective_appTop_of_injective {X S P S' : Scheme.{0}} {p : X ⟶ S} {q : P ⟶ S'} {d : P ⟶ X} {f : S' ⟶ S}
    (w : d ≫ p = q ≫ f) {e : S ⟶ X} {e' : S' ⟶ P} (he' : e' ≫ q = 𝟙 _) (hee : e' ≫ d = f ≫ e)
    (hd : Function.Injective d.appTop.hom) (hq : Function.Surjective q.appTop.hom) :
    Function.Surjective p.appTop.hom := by
  intro a
  obtain ⟨b, hb⟩ := hq (d.appTop.hom a)
  have c : ∀ {A B C : Scheme.{0}} (g : A ⟶ B) (h : B ⟶ C) (x : Γ(C, ⊤)),
      g.appTop.hom (h.appTop.hom x) = (g ≫ h).appTop.hom x := fun g h x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  refine ⟨e.appTop.hom a, hd ?_⟩
  rw [c, w, ← c, c f e, ← hee, ← c, ← hb, c e' q, he', Scheme.Hom.id_appTop]
  rfl

variable {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
  [IsFractionRing V K] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
  {A : Over (Spec (CommRingCat.of K))} [GrpObj A] [IsCommMonObj A] {F : A.left ⟶ G.left}

theorem surjective_cube_of_generic [Flat G.hom] (gp : IsGrpPullback A G (etaK V K) F)
    (h : Function.Surjective (G3 A).hom.appTop.hom) : Function.Surjective (G3 G).hom.appTop.hom := by
  have hp := gp.1
  have : Flat (G3 G).hom := by
    show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom)
    infer_instance
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd (G3 G).hom (etaK V K))
  let x : Fin 3 → (P ⟶ A) := fun i => Over.homMk
    (hp.lift (pullback.fst _ _ ≫ (x3 G i).left) P.hom (by
      rw [Category.assoc, Over.w]; exact pullback.condition)) (hp.lift_snd _ _ _)
  have hx : ∀ i, (x i).left ≫ F = pullback.fst _ _ ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
  let l : P ⟶ G3 A := lift (x 0) (lift (x 1) (x 2))
  have lx : ∀ i, l ≫ x3 A i = x i := fun i => by fin_cases i <;> simp [l, x3]
  have f3 : ∀ i, (cubeMapOf gp).F3 ≫ (x3 G i).left = (x3 A i).left ≫ F := cubeMap_comp_proj_three (cubeMapOf gp)
  have hl : l.left ≫ (cubeMapOf gp).F3 = pullback.fst (G3 G).hom (etaK V K) := hom_ext_triple _ fun i => by
    rw [Category.assoc, f3, ← Category.assoc, ← Over.comp_left, lx, hx]
  have inj : Function.Injective (l.left ≫ (cubeMapOf gp).F3).appTop.hom := by
    rw [hl]
    exact Exist.CubicalExtension.app_injective_generic (IsPullback.of_hasPullback _ _) ⊤
  refine surjective_appTop_of_injective (d := (cubeMapOf gp).F3) (f := etaK V K)
    (Over.w (lift (pushPt hp.w (x3 A 0)) (lift (pushPt hp.w (x3 A 1)) (pushPt hp.w (x3 A 2)))))
    (e := eSec (G3 G)) (e' := eSec (G3 A)) (Over.w η[G3 A]) ?_ ?_ h
  · rw [CubeExtension.eSec_three, CubeExtension.eSec_three]
    refine hom_ext_triple _ fun i => ?_
    have a : ∀ {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B],
        (lift (1 : 𝟙_ (Over S) ⟶ B) (lift (1 : 𝟙_ (Over S) ⟶ B) (1 : 𝟙_ (Over S) ⟶ B))).left ≫ (x3 B i).left =
          eSec B := fun B _ _ => by
      rw [← Over.comp_left, eSec]
      fin_cases i <;> simp [x3, Hom.one_def]
    rw [Category.assoc, f3, ← Category.assoc, a, Category.assoc, a]
    exact (cubeMapOf gp).e_comm
  · rw [Scheme.Hom.comp_appTop] at inj
    exact Function.Injective.of_comp (f := l.left.appTop.hom) inj

theorem exists_package : Laws → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (L : RigLB G), LBIso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom (jK V))) → ∃ P : CP G, P.L = L) := by
  intro laws V _ _ _ hV A G _ _ hG eA hA L h₁
  have := hV.1
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := A.isAb.comm
  have : IsMonHom eA.symm.hom := inferInstanceAs (IsMonHom eA.inv)
  have gp : IsGrpPullback A.A G (jK V) (eA.inv.left ≫ pullback.fst G.hom (jK V)) :=
    ((isGrpPullback_of_iso eA.symm).comp (isGrpPullback_pullback G (jK V))).congr (Category.id_comp _) rfl
  have hi : eA.inv.left ≫ eA.hom.left = 𝟙 _ := by rw [← Over.comp_left, eA.inv_hom_id, Over.id_left]
  obtain ⟨r, hr⟩ := A.rigid
  obtain ⟨w, hw⟩ : LBIso A.L (L.L.pull (eA.inv.left ≫ pullback.fst G.hom (jK V))) :=
    LBIso.chartPull (chartPullSec A.L _ eA.inv.left hi) (chartPullSame L.L _ _ _ eA.inv.left fun _ => rfl) h₁
  obtain ⟨c⟩ := (laws.cube _ A ⟨A.L, r, A.isLB, hr⟩ rfl).1
  obtain ⟨c'⟩ := PolExtension.nonempty_cubical laws.cubicalExtends gp L c w hw
  obtain ⟨s, hs, hs'⟩ := PolExtension.exists_symmetry gp L.isLB A.isLB A.sym w hw
  exact ⟨CP.ofSurjective (surjective_cube_of_generic gp (surjective_cube laws.globalFns A.isAb)) L c' s hs hs', rfl⟩

end GlobalTheory.CubicalPackage

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.WeilBound.CoreStatements.HodgeTatePoints.MhBase
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Mh

open scoped CategoryTheory.Obj

section Bridge
variable {S' S : Scheme.{0}} (x : S' ⟶ S) (G : Over S)

def toPull {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) : Y ⟶ (Over.pullback x).obj G :=
  Over.homMk (pullback.lift g.left Y.hom (by simpa using Over.w g)) (pullback.lift_snd _ _ _)

theorem toPull_fst {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) :
    (toPull x G g).left ≫ pullback.fst G.hom x = g.left := pullback.lift_fst _ _ _

variable {x G} in
theorem hom_ext_pull {Y : Over S'} {y z : Y ⟶ (Over.pullback x).obj G}
    (h : y.left ≫ pullback.fst G.hom x = z.left ≫ pullback.fst G.hom x) : y = z := by
  ext
  refine pullback.hom_ext h ?_
  have h1 := Over.w y
  have h2 := Over.w z
  simp only [Over.pullback_obj_hom] at h1 h2
  rw [h1, h2]

theorem toPull_eq {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) :
    toPull x G g = toPull x _ (𝟙 (Over.mk (Y.hom ≫ x))) ≫ (Over.pullback x).map g := by
  apply hom_ext_pull
  have h1 : ((Over.pullback x).map g).left ≫ pullback.fst G.hom x = pullback.fst _ x ≫ g.left :=
    pullback.lift_fst _ _ _
  have h2 := toPull_fst x _ (𝟙 (Over.mk (Y.hom ≫ x)))
  rw [toPull_fst, Over.comp_left, Category.assoc, h1, ← Category.assoc, h2]
  simp

def toPullHom [GrpObj G] (Y : Over S') : (Over.mk (Y.hom ≫ x) ⟶ G) →* (Y ⟶ (Over.pullback x).obj G) where
  toFun := toPull x G
  map_one' := by
    rw [toPull_eq, Functor.map_one, MonObj.comp_one]
  map_mul' g h := by
    rw [toPull_eq, toPull_eq x G g, toPull_eq x G h, Functor.map_mul, MonObj.comp_mul]

def ofPull {Y : Over S'} (y : Y ⟶ (Over.pullback x).obj G) : Over.mk (Y.hom ≫ x) ⟶ G :=
  Over.homMk (y.left ≫ pullback.fst G.hom x) (by
    have h1 := Over.w y
    simp only [Over.pullback_obj_hom] at h1
    simp [pullback.condition, reassoc_of% h1])

theorem toPull_ofPull {Y : Over S'} (y : Y ⟶ (Over.pullback x).obj G) : toPull x G (ofPull x G y) = y := by
  apply hom_ext_pull
  rw [toPull_fst]
  rfl

end Bridge

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

def torFst (S : Scheme.{0}) (X : Type) [AddCommGroup X] :
    (splitTorus S X).left ⟶ Spec (CommRingCat.of (AddMonoidAlgebra ZU.{0} X)) :=
  pullback.fst (splitTorusAff ZU X).hom (toZ S)

def chi {Y : Scheme.{0}} (g : Y ⟶ (splitTorus S X).left) : Multiplicative X →* Γ(Y, ⊤) :=
  (pb (g ≫ torFst S X)).toMonoidHom.comp (AddMonoidAlgebra.of ZU.{0} X)

theorem chi_apply {Y : Scheme.{0}} (g : Y ⟶ (splitTorus S X).left) (x : Multiplicative X) :
    chi g x = pb (g ≫ torFst S X) (AddMonoidAlgebra.single x.toAdd 1) := rfl

theorem chi_comp {Y Y' : Scheme.{0}} (f : Y' ⟶ Y) (g : Y ⟶ (splitTorus S X).left) (x : Multiplicative X) :
    chi (f ≫ g) x = f.appTop (chi g x) := by
  rw [chi_apply, chi_apply, Category.assoc, pb_comp]

theorem chi_ext {Y : Scheme.{0}} {g h : Y ⟶ (splitTorus S X).left}
    (w : g ≫ (splitTorus S X).hom = h ≫ (splitTorus S X).hom) (e : ∀ x, chi g x = chi h x) : g = h := by
  refine pullback.hom_ext (f := (splitTorusAff ZU X).hom) (g := toZ S) ?_ w
  refine pb_ext (j := g ≫ torFst S X) (j' := h ≫ torFst S X) (RingHom.congr_fun ?_)
  refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun m => e (Multiplicative.ofAdd m)
  have e1 : ∀ k : Y ⟶ (splitTorus S X).left, pb (k ≫ torFst S X) (AddMonoidAlgebra.single 0 r) = pb (toZ Y) r := by
    intro k
    refine (pb_spec (k ≫ torFst S X) (algebraMap ZU.{0} (AddMonoidAlgebra ZU.{0} X)) r).symm.trans ?_
    congr 2
    exact specULiftZIsTerminal.hom_ext _ _
  rw [e1, e1]

theorem exists_chi (Y : Over S) (c : Multiplicative X →* Γ(Y.left, ⊤)) :
    ∃ g : Y ⟶ splitTorus S X, ∀ x, chi g.left x = c x := by
  obtain ⟨j, hj⟩ := exists_pb (AddMonoidAlgebra.liftNCRingHom (k := ZU.{0}) (pb (toZ Y.left)) c
    fun _ _ => Commute.all _ _)
  refine ⟨Over.homMk (pullback.lift (f := (splitTorusAff ZU X).hom) (g := toZ S) j Y.hom
    (specULiftZIsTerminal.hom_ext _ _)) (pullback.lift_snd _ _ _), fun x => ?_⟩
  have e : (pullback.lift (f := (splitTorusAff ZU X).hom) (g := toZ S) j Y.hom
    (specULiftZIsTerminal.hom_ext _ _)) ≫ torFst S X = j := pullback.lift_fst _ _ _
  refine (congrArg (fun k => pb k (AddMonoidAlgebra.single x.toAdd 1)) e).trans ?_
  rw [hj, AddMonoidAlgebra.liftNCRingHom_single, map_one, _root_.one_mul]
  rfl

theorem pb_mul_aff {Y : Over (Spec ZU.{0})} (g h : Y ⟶ splitTorusAff ZU X) (x : X) :
    pb (A := AddMonoidAlgebra ZU.{0} X) (g * h).left (AddMonoidAlgebra.single x 1) =
      pb (A := AddMonoidAlgebra ZU.{0} X) g.left (AddMonoidAlgebra.single x 1) *
        pb (A := AddMonoidAlgebra ZU.{0} X) h.left (AddMonoidAlgebra.single x 1) := by
  let A := AddMonoidAlgebra ZU.{0} X
  let q : Y.left ⟶ Spec (CommRingCat.of (A ⊗[ZU.{0}] A)) := (lift g h).left ≫ (pullbackSpecIso ZU.{0} A A).hom
  have e0 : (g * h).left = q ≫ Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom ZU.{0} A : A →+* A ⊗[ZU.{0}] A)) := rfl
  have e1 : q ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = g.left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift g h).left ≫ ·) (pullbackSpecIso_hom_fst ZU.{0} A A)).trans
      (congrArg (·.left) (lift_fst g h)))
  have e2 : q ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom Algebra.TensorProduct.includeRight)) = h.left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift g h).left ≫ ·) (pullbackSpecIso_hom_snd ZU.{0} A A)).trans
      (congrArg (·.left) (lift_snd g h)))
  rw [e0, ← e1, ← e2, pb_spec, pb_spec, pb_spec, ← map_mul]
  congr 1
  simp [A, AddMonoidAlgebra.comul_single]

theorem chi_mul {Y : Over S} (g h : Y ⟶ splitTorus S X) (x : Multiplicative X) :
    chi (g * h).left x = chi g.left x * chi h.left x := by
  let g' := ofPull (toZ S) (splitTorusAff ZU X) g
  let h' := ofPull (toZ S) (splitTorusAff ZU X) h
  have e : g * h = toPull (toZ S) (splitTorusAff ZU X) (g' * h') :=
    ((map_mul (toPullHom (toZ S) (splitTorusAff ZU X) Y) g' h').trans
      (congrArg₂ (· * ·) (toPull_ofPull _ _ g) (toPull_ofPull _ _ h))).symm
  have e' : (g * h).left ≫ torFst S X = (g' * h').left := by
    rw [e]
    exact toPull_fst _ _ _
  rw [chi_apply, e']
  exact pb_mul_aff g' h' x.toAdd

theorem chi_one (Y : Over S) (x : Multiplicative X) : chi (1 : Y ⟶ splitTorus S X).left x = 1 := by
  have h := chi_mul (1 : Y ⟶ splitTorus S X) 1 x
  rw [_root_.mul_one] at h
  have hu : IsUnit (chi (1 : Y ⟶ splitTorus S X).left x) := (Group.isUnit x).map _
  exact (hu.mul_eq_left.1 h.symm)

theorem chi_pow {Y : Over S} (g : Y ⟶ splitTorus S X) (x : Multiplicative X) (n : ℕ) :
    chi (g ^ n).left x = chi g.left x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, chi_one]
  | succ n ih => rw [pow_succ, pow_succ, chi_mul, ih]

theorem pow_eq_one_iff_chi {Y : Over S} (g : Y ⟶ splitTorus S X) (n : ℕ) :
    g ^ n = 1 ↔ ∀ x, chi g.left x ^ n = 1 := by
  refine ⟨fun h x => by rw [← chi_pow, h, chi_one], fun h => Over.OverMorphism.ext (chi_ext ?_ fun x => ?_)⟩
  · exact (Over.w _).trans (Over.w _).symm
  · rw [chi_pow, h, chi_one]

end PositivityTheory.HtPt.Mh

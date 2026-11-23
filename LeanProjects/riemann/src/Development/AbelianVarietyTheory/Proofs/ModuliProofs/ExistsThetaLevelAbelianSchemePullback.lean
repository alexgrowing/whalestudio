import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaObjPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left}

theorem pushHom_injective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Injective (pushHom h T) :=
  fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w, Over.w]))

theorem pushHom_surjective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Surjective (pushHom h T) :=
  fun y => ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem map_linComb {T : Over S} {T' : Over S'} (ρ : (T' ⟶ A') →* (T ⟶ A)) {n : ℕ} (y : Fin n → (T' ⟶ A'))
    (a : Fin n → ℕ) : ρ (Out.linComb y a) = Out.linComb (fun i => ρ (y i)) a := by
  unfold Out.linComb
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact map_pow ρ _ _

def toBase (f : S' ⟶ S) : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S := Over.homMk f (by simp)

theorem exists_sec (h : IsGrpPullback A' A f φ) (x : Out.baseOver S ⟶ A) :
    ∃ x' : Out.baseOver S' ⟶ A', pushHom h _ x' = toBase f ≫ x :=
  pushHom_surjective h _ _

end GlobalTheory.ThetaObjPull

namespace GlobalTheory

open ThetaObjPull PolBaseChange

theorem tObj_pull : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0})
    (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s), f ≫ s = s' →
    ∃ t' : TObj g k J b s', TMap t' t f := by
  intro o _ g k J b S S' s s' f t hs
  subst hs
  have h := isGrpPullback_pullback t.A f
  have hL' := pull_isLB t.isLB (pullback.fst t.A.hom f)
  have hiso := lbIso_refl hL'
  obtain ⟨hab, hamp, hk⟩ := pol_pull _ _ _ _ _ _ _ _ t.isLB hL' t.ab h hiso
  choose pt hpt using fun i => exists_sec h (t.pt i)
  have hpt' : ∀ i, (pt i).left ≫ pullback.fst t.A.hom f = f ≫ (t.pt i).left := fun i =>
    congrArg (fun z => z.left) (hpt i)
  have := t.hom
  have := t.ab.comm
  refine ⟨{ A := (Over.pullback f).obj t.A
            ab := hab
            dim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 t.dim
            L := t.L.pull (pullback.fst t.A.hom f)
            isLB := hL'
            rigid := rigidified_pull h t.rigid
            sym := sym_pull h t.sym
            ample := hamp t.ample
            ktriv := hk t.ktriv
            pt := pt
            torsion := fun i => pushHom_injective h _ ?_
            bij := fun K _ _ x y hy => ?_
            pairing := fun i j => ?_
            act := fun j => (Over.pullback f).map (t.act j)
            hom := fun j => inferInstance }, pullback.fst t.A.hom f, h, hiso, hpt', fun j => pullback.lift_fst _ _ _⟩
  · rw [map_pow, map_one, hpt]
    exact (map_pow (preHom (toBase f)) _ _).symm.trans (by rw [t.torsion, map_one])
  · have key : ∀ c : Ix g k, pushHom h (Over.mk x) (Out.linComb (fun i =>
        (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S') ≫ pt i) (fun i => (c i).val)) =
        Out.linComb (fun i => (Over.homMk (x ≫ f) (by simp) : Over.mk (x ≫ f) ⟶ Out.baseOver S) ≫ t.pt i)
          (fun i => (c i).val) := fun c => by
      rw [map_linComb]
      congr 1
      funext i
      apply Over.OverMorphism.ext
      show (x ≫ (pt i).left) ≫ _ = (x ≫ f) ≫ (t.pt i).left
      rw [Category.assoc, hpt', Category.assoc]
    have hy' : pushHom h (Over.mk x) y ^ k = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨c, hc, hu⟩ := t.bij K (x ≫ f) (pushHom h (Over.mk x) y) hy'
    exact ⟨c, pushHom_injective h _ ((key c).trans hc), fun c' hc' => hu c' ((key c').symm.trans (congrArg _ hc'))⟩
  · refine (weilIs_grpPullback_of_comm _ _ _ _ f _ _ _ t.isLB hL' h hiso (Out.baseOver S') k (pt i) (pt j)
      (toBase f ≫ t.pt i) (toBase f ≫ t.pt j) _ (hpt' i).symm (hpt' j).symm).2 ?_
    have w := CommPairing.weilIs_pull globalFns_holds t.ab t.isLB (toBase f) (t.pairing i j)
    rw [map_zpow] at w
    have e : Units.map (toBase f).left.appTop.hom.toMonoidHom (unitS s b.ζ) = unitS (f ≫ s) b.ζ := by
      apply Units.ext
      show f.appTop.hom (s.appTop.hom _) = (f ≫ s).appTop.hom _
      rw [Scheme.Hom.comp_appTop]
      rfl
    exact e ▸ w

end GlobalTheory

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

namespace GlobalTheory

theorem exists_level_baseChange : Laws → ∀ (S S' : Scheme.{0}) [IsLocallyNoetherian S] [IsLocallyNoetherian S'] (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → P'.g = P.g → ∀ (k : ℕ) (ze : Γ(S, ⊤)ˣ) (ze' : Γ(S', ⊤)ˣ), f.appTop.hom ze.val = ze'.val → IsPrimitiveRoot ze' k → ∀ lev : Out.Level P k ze, ∃ lev' : Out.Level P' k ze', ∀ (i : Fin (2 * P.g)) (i' : Fin (2 * P'.g)), (i : ℕ) = i' → (lev'.pt i').left ≫ φ = f ≫ (lev.pt i).left := by
  intro hL S S' _ _ f P P' φ h hiso hg k ze ze' hz hprim lev
  have e : 2 * P'.g = 2 * P.g := congrArg (2 * ·) hg
  have cast : ∀ {n n' : ℕ} (e : n' = n) {T : Over S} (y : Fin n → (T ⟶ P.A)) (a : Fin n' → ℕ),
      linComb (fun i => y (Fin.cast e i)) a = linComb y (fun i => a (Fin.cast e.symm i)) := by
    intro n n' e T y a
    subst e
    rfl
  choose pt hpt using fun i => ThetaObjPull.exists_sec h (lev.pt (Fin.cast e i))
  have hpt' : ∀ i, (pt i).left ≫ φ = f ≫ (lev.pt (Fin.cast e i)).left := fun i =>
    congrArg (fun z => z.left) (hpt i)
  have key : ∀ (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ S') (c : Fin (2 * P'.g) → ℕ),
      pushHom h (Over.mk x) (linComb (fun i =>
        (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S') ≫ pt i) c) =
      linComb (fun i => (Over.homMk (x ≫ f) (by simp) : Over.mk (x ≫ f) ⟶ baseOver S) ≫ lev.pt i)
        (fun i => c (Fin.cast e.symm i)) := fun K _ x c => by
    rw [ThetaObjPull.map_linComb]
    refine Eq.trans ?_ (cast e _ c)
    congr 1
    funext i
    apply Over.OverMorphism.ext
    show (x ≫ (pt i).left) ≫ _ = (x ≫ f) ≫ (lev.pt _).left
    rw [Category.assoc, hpt', Category.assoc]
  have := P.isAb.comm
  refine ⟨{ pt := pt
            prim := hprim
            torsion := fun i => ThetaObjPull.pushHom_injective h _ ?_
            indep := fun K _ _ x c c' hc => ?_
            span := fun K _ _ x y hy => ?_
            pairing := fun i j => ?_ }, fun i i' hi => ?_⟩
  · rw [map_pow, map_one, hpt]
    exact (map_pow (preHom (ThetaObjPull.toBase f)) _ _).symm.trans (by rw [lev.torsion, map_one])
  · have q := lev.indep K (x ≫ f) (fun i => c (Fin.cast e.symm i)) (fun i => c' (Fin.cast e.symm i))
      ((key K x _).symm.trans ((congrArg (pushHom h (Over.mk x)) hc).trans (key K x _)))
    funext i
    exact congrFun q (Fin.cast e i)
  · have hy' : pushHom h (Over.mk x) y ^ k = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨c, hc⟩ := lev.span K (x ≫ f) (pushHom h (Over.mk x) y) hy'
    exact ⟨fun i => c (Fin.cast e i), ThetaObjPull.pushHom_injective h _ ((key K x _).trans hc)⟩
  · refine (weilIs_grpPullback_of_comm _ _ _ _ f _ _ _ P.isLB P'.isLB h hiso (baseOver S') k (pt i) (pt j)
      (ThetaObjPull.toBase f ≫ lev.pt _) (ThetaObjPull.toBase f ≫ lev.pt _) _ (hpt' i).symm (hpt' j).symm).2 ?_
    have w := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (ThetaObjPull.toBase f)
      (lev.pairing (Fin.cast e i) (Fin.cast e j))
    rw [map_zpow] at w
    have e₁ : Units.map (ThetaObjPull.toBase f).left.appTop.hom.toMonoidHom ze = ze' := Units.ext hz
    have e₂ : stdSymp P.g (Fin.cast e i) (Fin.cast e j) = stdSymp P'.g i j := by
      simp only [stdSymp, Fin.val_cast, hg]
    rw [e₁, e₂] at w
    exact w
  · obtain rfl : i = Fin.cast e i' := Fin.ext hi
    exact hpt' i'

end GlobalTheory

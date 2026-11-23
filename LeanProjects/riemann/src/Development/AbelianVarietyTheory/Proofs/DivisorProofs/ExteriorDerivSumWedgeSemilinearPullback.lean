import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem clRel_pullForm : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (w : GlobForm s) (n : ℕ) (u v : Fin n → GlobForm s), ClRel (OAff s) w u v → ClRel (OAff s') (GlobalTheory.CechDR.pullForm h w) (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) := by
  intro R R' _ _ X X' s s' σ φ h w n u v hw T'
  have hp : ∀ (ω : GlobForm s) (p : Pair φ), (GlobalTheory.CechDR.pullForm h ω).1 (Opposite.op p.1.1) =
      (semiHom_secPull h p).m1 (ω.1 (Opposite.op p.1.2)) :=
    fun ω p ↦ ((isPullForm_iff.1 (isPullForm_pullForm h ω)) p).symm
  have hg : ∀ (ω : GlobForm s') {T T' : AffOp X'} (a : T ⟶ T'), p1 (OAff s') a (ω.1 T) = ω.1 T' :=
    fun ω _ _ a ↦ (ω.2 a).symm
  rw [← sub_eq_zero]
  refine twoForm_sep_of_basis s' (pairFst φ) (pair_cover_affine φ s') T' _ fun t a ↦ ?_
  rw [map_sub, sub_eq_zero, pOm_dOne, hg]
  have e1 : ∀ k, pOm (OAff s') 2 a (wedge R' _ ((GlobalTheory.CechDR.pullForm h (u k)).1 T')
      ((GlobalTheory.CechDR.pullForm h (v k)).1 T')) = wedge R' _ ((GlobalTheory.CechDR.pullForm h (u k)).1 ((pairFst φ).obj t))
      ((GlobalTheory.CechDR.pullForm h (v k)).1 ((pairFst φ).obj t)) := fun k ↦
    (pOm_wedge (OAff s') a _ _).trans (by rw [hg, hg])
  refine Eq.trans ?_ ((map_sum (pOm (OAff s') 2 a) _ _).trans (Finset.sum_congr rfl fun k _ ↦ e1 k)).symm
  have key : ∀ p : Pair φ, dOne R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h w).1 (Opposite.op p.1.1)) =
      ∑ k, wedge R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h (u k)).1 (Opposite.op p.1.1))
        ((GlobalTheory.CechDR.pullForm h (v k)).1 (Opposite.op p.1.1)) := by
    intro p
    calc dOne R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h w).1 (Opposite.op p.1.1))
        = dOne R' (Sec s' p.1.1.1) ((semiHom_secPull h p).m1 (w.1 (Opposite.op p.1.2))) :=
          congrArg _ (hp w p)
      _ = (semiHom_secPull h p).mOm 2 (dOne R (Sec s p.1.2.1) (w.1 (Opposite.op p.1.2))) :=
          (SemiHom.mOm_dOne _ _).symm
      _ = (semiHom_secPull h p).mOm 2 (wsum (OAff s) u v (Opposite.op p.1.2)) :=
          congrArg ((semiHom_secPull h p).mOm 2) (hw (Opposite.op p.1.2))
      _ = (semiHom_secPull h p).mOm 2 (∑ k, wedge R (Sec s p.1.2.1) ((u k).1 (Opposite.op p.1.2))
            ((v k).1 (Opposite.op p.1.2))) := rfl
      _ = ∑ k, (semiHom_secPull h p).mOm 2 (wedge R (Sec s p.1.2.1) ((u k).1 (Opposite.op p.1.2))
            ((v k).1 (Opposite.op p.1.2))) := map_sum _ _ _
      _ = ∑ k, wedge R' (Sec s' p.1.1.1) ((semiHom_secPull h p).m1 ((u k).1 (Opposite.op p.1.2)))
            ((semiHom_secPull h p).m1 ((v k).1 (Opposite.op p.1.2))) :=
          Finset.sum_congr rfl fun k _ ↦ SemiHom.mOm_wedge (semiHom_secPull h p) ((u k).1 (Opposite.op p.1.2))
            ((v k).1 (Opposite.op p.1.2))
      _ = ∑ k, wedge R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h (u k)).1 (Opposite.op p.1.1))
            ((GlobalTheory.CechDR.pullForm h (v k)).1 (Opposite.op p.1.1)) :=
          Finset.sum_congr rfl fun k _ ↦ congrArg₂ (fun a b ↦ wedge R' (Sec s' p.1.1.1) a b)
            (hp (u k) p).symm (hp (v k) p).symm
  exact key t.unop

end GlobalTheory.AbCoh

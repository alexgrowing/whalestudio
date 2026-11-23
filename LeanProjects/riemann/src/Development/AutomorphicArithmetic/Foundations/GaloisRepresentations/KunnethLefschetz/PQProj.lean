import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.LRingPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz

theorem qProj_holds : QProj := by
  unfold QProj
  intro hI l _ k _ G d e Z X p ι h n m r s t h1 h2 h3 h4 a b
  have key : ∀ (x : Hl l (sch.obj X) n 0) (y : Hl l (sch.obj Z) m 0),
      G.q h h2 (cupV l Z h1 (pb l ι n ((1 : ℚ_[l]) ⊗ₜ x)) ((1 : ℚ_[l]) ⊗ₜ y)) =
        cupV l X h4 ((1 : ℚ_[l]) ⊗ₜ x) (G.q h h3 ((1 : ℚ_[l]) ⊗ₜ y)) := by
    intro x y
    rw [LRingPf.pb_tmul, LRingPf.cupV_eq l hI.a11 Z, LRingPf.cupV_eq l hI.a11 X, LRingPf.cupQ_tmul]
    simp only [Gys0.q, LinearMap.baseChange_tmul]
    rw [LRingPf.cupQ_tmul]
    congr 1
    refine Subtype.ext (funext fun j => ?_)
    exact G.proj j h h1 h2 h3 h4 (x.1 j) (y.1 j)
  have hfg : ((cupV l Z h1 ∘ₗ pb l ι n).compr₂ (G.q h h2)) = (cupV l X h4).compl₂ (G.q h h3) :=
    LRingPf.ext2 fun x y => key x y
  exact DFunLike.congr_fun (DFunLike.congr_fun hfg a) b

end UpperTheory.Gal.KunnethLefschetz

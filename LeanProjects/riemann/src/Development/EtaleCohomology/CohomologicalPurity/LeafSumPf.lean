import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut.SumCut

def LeafChainsSum : Prop := ∀ (R : Type) [CommRing R] (A : Type) (E : A → Spc) (c : Cofan E), Nonempty (IsColimit c) →
  Nonempty (IsColimit (Cofan.mk ((chains R).obj c.pt) fun a => (chains R).map (c.inj a)))

def LeafHKSum : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (A : Type) (K : A → Cx R) (c : Cofan K),
  Nonempty (IsColimit c) → ∀ n : ℤ, Function.Bijective fun (x : HK R c.pt F n) (a : A) => HK.pull R (c.inj a) F n x

end LateralTheory.CohomologicalPurity.TubeCut.SumCut

namespace LateralTheory.CohomologicalPurity.TubeCut
open SumCut

theorem LeafSum_of (hc : LeafChainsSum) (hk : LeafHKSum) : LeafSum := by
  intro R _ F A E c hc' n
  exact hk R F A (fun a => (chains R).obj (E a)) _ (hc R A E c hc') n

end LateralTheory.CohomologicalPurity.TubeCut

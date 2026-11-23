import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProductUniformizationTorusIsPower

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowTorusProj

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PowTorus

section Pow

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}

theorem exists_factor (P : UnifPowOf pD pA pG U' U) (e : ℕ) (i : Fin j) :
    ∃ h : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X,
      h ≫ (U.gt e).i = (U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i) := by
  have := pD.pw.hom i
  have hd : ((U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i)) ≫ (U.gt e).q =
      toUnit _ ≫ η[thickObj R I e D.toPre.P.A] := by
    rw [Category.assoc, ← P.q_pr e i, ← Category.assoc, (U'.gt e).isKernel.w, Category.assoc]
    exact congrArg (toUnit _ ≫ ·) (IsMonHom.one_hom ((Over.pullback (thick R I e)).map (pD.pw.pr i)))
  exact ⟨(U.gt e).isKernel.lift _ _ hd, (U.gt e).isKernel.lift_fst _ _ _⟩

set_option maxHeartbeats 800000 in

theorem char_prod (P : UnifPowOf2 pD pA pG U' U) (e : ℕ)
    (h : Fin j → (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X))
    (hh : ∀ i, h i ≫ (U.gt e).i = (U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i))
    (x : D'.toPre.X) (z : (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X).left) :
    gm (𝟙 _) z ⊤ (charUnit _ D'.toPre.X x) = ∏ i, gm (h i).left z ⊤ (charUnit _ D.toPre.X (pD.xe x i)) := by
  obtain ⟨J, hJ₀⟩ := TLinPf.idx_exists D.toPre.P.L D.toPre.P.isLB z
  have hJ : Good D.toPre.P.L z J := hJ₀
  obtain ⟨J', hJ₁⟩ := TLinPf.idx_exists D'.toPre.P.L D'.toPre.P.isLB z
  have hJ' : Good D'.toPre.P.L z J' := hJ₁
  obtain ⟨hψ, H⟩ := P.t_pr e x
  have E := box_gen_val_along pD.w hψ _ (fun i => (U.gt e).t (pD.xe x i)) H (U'.gt e).i.left z hJ hJ'
  have E₁ := prod_on_torus (U'.gt e) x (omB pD z J J')
  have E₂ := val_on_torus (U'.gt e) x hJ' (𝟙 _)
  rw [Category.id_comp] at E₂
  refine E₂.symm.trans ((_root_.one_mul _).symm.trans ((congrArg (· * _) E₁.symm).trans
    (E.trans (Finset.prod_congr rfl fun i _ => ?_))))
  refine Eq.trans ?_ (val_on_torus (U.gt e) (pD.xe x i) hJ (h i))
  rw [hh i]
  rfl

end Pow

theorem exists_torus_proj : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) (_ : UnifPowOf2 pD pA pG U' U) (e : ℕ) (s : Fin j), ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X, (U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr s) = t ≫ (U.gt e).i ∧ ∀ χ : D.toPre.X, t.left.appTop.hom (charUnit _ D.toPre.X χ).val = (charUnit _ D'.toPre.X (pD.xe.symm (Pi.single s χ))).val := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U P e s
  choose h hh using exists_factor P.toUnifPowOf e
  refine ⟨h s, (hh s).symm, fun χ => fn_ext fun z _ => ?_⟩
  have E := char_prod P e h hh (pD.xe.symm (Pi.single s χ)) z
  rw [AddEquiv.apply_symm_apply, Finset.prod_eq_single s (fun k _ hk => by
    rw [Pi.single_eq_of_ne hk]; exact gm_char_zero _ z) (fun hi => (hi (Finset.mem_univ s)).elim),
    Pi.single_eq_same] at E
  have a := gs_pull (𝟙 _) (h s).left z ⊤ trivial (charUnit _ D.toPre.X χ).val
  rw [Category.id_comp] at a
  exact a.trans ((gs_unit _ z ⊤ trivial _).trans ((congrArg Units.val E.symm).trans
    (gs_unit _ z ⊤ trivial _).symm))

end GlobalTheory.PowTorusProj

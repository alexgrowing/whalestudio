import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcVarZpowInjective
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PolDeg
variable {R : Type} [CommRing R] [IsDomain R]

def ofDeg (D : DegPre R) (hB : D.TauBimult) : Data R := Wit.ofDeg D hB

theorem ofDeg_X (D : DegPre R) (hB : D.TauBimult) : (ofDeg D hB).X = D.X := rfl

theorem ofDeg_c (D : DegPre R) (hB : D.TauBimult) (a : D.X) : (ofDeg D hB).c a = D.c a := rfl

theorem exists_nontrivial (k : Type) [Field k] : ∃ Q : Data (PowerSeries k), Nontrivial Q.X :=
  ⟨ofDeg (GlobalTheory.ToricData.arcDataInt k).toPre (GlobalTheory.ToricData.arcDataInt k).tau_bimult, inferInstanceAs (Nontrivial ℤ)⟩

theorem refines_ofDeg (D : DegPre R) (hB : D.TauBimult) :
    Refines (ofDeg D hB) (RingHom.id R) D (AddEquiv.refl _) :=
  Wit.refines_ofDeg D hB

theorem inhabited_and_refines :
    (∀ (k : Type) [Field k], ∃ Q : Data (PowerSeries k), Nontrivial Q.X) ∧
    ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult),
      Refines (ofDeg D hB) (RingHom.id R) D (AddEquiv.refl _) :=
  ⟨fun k _ => exists_nontrivial k, fun _ _ _ D hB => refines_ofDeg D hB⟩

open GlobalTheory.ToricData ReciprocityTheory.ChartRestriction.G.Out.InhTate in

theorem isMonomialTau_arcData (k : Type) [Field k] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (be : LinearMap.BilinForm ℤ X) (hs : ∀ y z, be y z = be z y) (hp : ∀ y, y ≠ 0 → 0 < be y y)
    (he : ∀ y, (2 : ℤ) ∣ be y y) :
    (ofDeg (arcData k be hs hp he).toPre (arcData k be hs hp he).tau_bimult).IsMonomialTau
      ![PowerSeries.X] ![be] := fun (a b : X) => by
  refine ⟨arcVar k ^ (be a b), ?_, cg _ _ 1, cg_isGen _ _ _, fun z J hJ => ?_⟩
  · rw [Fin.prod_univ_one]
    exact Units.val_zpow_eq_zpow_val _ _
  have e1 := (Wit.exists_tau (arcData k be hs hp he).toPre a b).choose_spec.2 _ (𝟙 _) z J hJ
  refine e1.trans ?_
  have e2 : val ((arcData k be hs hp he).toPre.tau a b) (𝟙 _) z J = gm (𝟙 _) z ⊤ (unitOn (arcVar k ^ (be a b))) := by
    exact (congrArg (gm _ z _) (arcData_tau_isConst k be hs hp he a b _)).trans (gm_res _ z _ (hJ.mem _ _) _)
  rw [e2]
  refine Eq.trans ?_ (congrArg (_ * ·) ((gm_res _ z _ (hJ.mem _ _) _).trans (map_one _))).symm
  exact (_root_.mul_one _).symm

end GlobalTheory.PolDeg

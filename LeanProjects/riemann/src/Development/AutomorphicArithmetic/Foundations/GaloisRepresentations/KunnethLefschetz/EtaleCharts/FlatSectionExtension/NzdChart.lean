import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartNzdAlg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.EtaleSplit

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.nzdChart :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d), (π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t k) ∈ nonZeroDivisors Γ(Y, (B.c α).C k) := by
  intro K _ W Z Y q i π D d B α k
  exact UpperTheory.Gal.KunnethLefschetz.G.PX.chartNzdAlg
    (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x)
    (π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom
    (B.c α).t ((B.c α).u k) k
    (UpperTheory.Gal.KunnethLefschetz.G.PX.etaleSplit B α) ((B.c α).surj k) ((B.c α).rel k)

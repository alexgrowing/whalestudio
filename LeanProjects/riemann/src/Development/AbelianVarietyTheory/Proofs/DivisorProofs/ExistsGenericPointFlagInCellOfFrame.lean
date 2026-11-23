import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BearsFlagUnitriangularIffMemCellStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.GenericCell

theorem upM_zero_eq {ι : Type} {m : ι → ℕ} {K : Type} [Field K] : upM (0 : Cell m → K) = 1 := by
  funext τ
  ext a b
  simp only [upM, upU, Matrix.of_apply, Pi.zero_apply, Pi.one_apply, Matrix.one_apply]
  split_ifs <;> simp_all

theorem exists_inCell_genericPoint : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (z : X.X) (A : Mat m X.Fn), A ∈ E.S z → ∃ u : Cell m → Y.Fn, InCell E E' φ f A u (genericPoint Y.X) := by
  intro F _ X Y ι _ m E E' φ f hR z A hA
  have hgX : A ∈ E.S (genericPoint X.X) := Fr.mem_genericPoint hA
  have hcp : (ratOf X).pt (IsLocalRing.closedPoint X.Fn) = genericPoint X.X := Scheme.fromSpecStalk_closedPoint
  obtain ⟨p, ⟨hpf, hpb⟩, -⟩ := hR.lifts X.Fn (ratOf X).pt A (hcp ▸ hgX) (upM 0) (by rw [upM_zero_eq]; exact Par.one)
  have hfp : f (p (IsLocalRing.closedPoint X.Fn)) = genericPoint X.X := by
    have h1 := congrArg (fun g : Sp X.Fn ⟶ X.X => g (IsLocalRing.closedPoint X.Fn)) hpf
    simp only [Scheme.Hom.comp_apply] at h1
    exact h1.trans hcp
  obtain ⟨u, hu, -⟩ := (GlobalTheory.T.bearsFlag_unitriangular_iff_mem_cell F X Y ι m E E' φ f hR A X.Fn p (hfp ▸ hgX) 0).1 hpb
  refine ⟨u, Fr.mem_of_specializes (hfp ▸ hgX) ((genericPoint_specializes _).map f.continuous), Fr.mem_genericPoint hu⟩

end GlobalTheory.FlagCell2.GenericCell

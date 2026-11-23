import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EmDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureIntegralPointsNonzero

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.ColumnSplitting.YvInt

variable {D : D7} {a b c : ℕ}

theorem cv_cA (v : Pl D) (z : AE D) : cv D v (cA D z) = sigR _ D.sp.cm.sig (cv D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy]
  | tmul a x => rfl

theorem intOff_mm {S : Finset (Pl D)} {x : Mx D a b} {y : Mx D b c} (hx : IntOff S x) (hy : IntOff S y) :
    IntOff S (mm x y) := by
  intro v hv i j
  have h : mm x y i j = ∑ k, x i k * y k j := Matrix.mul_apply
  have hs : ∑ k, x i k * y k j ∈ (intLoc D.host.F D.host.E v).comap (cv D v) :=
    Subring.sum_mem _ fun k _ => Subring.mul_mem _ (Subring.mem_comap.2 (hx v hv i k))
      (Subring.mem_comap.2 (hy v hv k j))
  rw [h]
  exact Subring.mem_comap.1 hs

theorem intOff_adj {S : Finset (Pl D)} {x : Mx D a b} (hx : IntOff S x) : IntOff S (adj x) := by
  intro v hv i j
  have h : adj x i j = cA D (x j i) := rfl
  rw [h, cv_cA]
  exact sigR_mem_intLoc _ (hx v hv j i)

theorem exists_finset_intOff (x : Mx D a b) : ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → IntOff S x := by
  have hbad : {v : Pl D | ¬ ∀ i j, cv D v (x i j) ∈ intLoc D.host.F D.host.E v}.Finite :=
    GlobalTheory.CompanionTheory.ColumnSplitting.exists_intOff x
  refine ⟨hbad.toFinset, fun S hS v hv => ?_⟩
  by_contra hc
  exact hv (hS (hbad.mem_toFinset.2 hc))

theorem intOff_yv (D : D7) (r t : ℕ) (V : HSp D) (b₀ : HermE D r) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ z : Mx D V.rank r × Mx D V.rank t,
      IntOff S z.1 → IntOff S z.2 → IntOff S (yv V b₀ z) := by
  classical
  obtain ⟨S₁, h₁⟩ := exists_finset_intOff (rat b₀.1⁻¹ : Mx D r r)
  obtain ⟨S₂, h₂⟩ := exists_finset_intOff (gA V)
  refine ⟨S₁ ∪ S₂, fun S hS z hz₁ hz₂ => ?_⟩
  exact intOff_mm (h₁ S (Finset.union_subset_left hS))
    (intOff_mm (intOff_adj hz₁) (intOff_mm (h₂ S (Finset.union_subset_right hS)) hz₂))

end GlobalTheory.CompanionTheory.ColumnSplitting.YvInt

end

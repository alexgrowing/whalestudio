import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombSmoothCurv
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry CategoryTheory MeasureTheory Set GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CxPts GlobalTheory.TrueGeo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ProjVar Formalism.L2.Pj Formalism.L2.Geo GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClosedRefCurv

section General

variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {ι : Type} [Fintype ι]

def nbhd (Δ : ι → Y.Dv) (y : Pts Y σ) : Set (Pts Y σ) := ⋂ i, Var.eqnSet σ (Δ i) (Var.eqn (Δ i) y)

theorem isOpen_nbhd (Δ : ι → Y.Dv) (y : Pts Y σ) : IsOpen (nbhd Δ y) :=
  isOpen_iInter_of_finite fun _ => Var.isOpen_eqnSet _ _

theorem mem_nbhd (Δ : ι → Y.Dv) (y : Pts Y σ) : y ∈ nbhd Δ y := Set.mem_iInter.2 fun i => Var.mem_eqnSet (Δ i) y

theorem isPotential_neg_sum_curvMet {Δ : ι → Y.Dv} (m : ∀ i, Var.Met Y σ (Δ i)) (hm : ∀ i, Y.mSmooth σ (Δ i) (m i))
    (a : ι → ℝ) (y : Pts Y σ) :
    IsPotential (Y.an σ) (fun c z ξ => -∑ i, a i * curvMet (m i) c z ξ) (nbhd Δ y)
      (fun z => ∑ i, (-a i) * Var.Met.wt (m i) (Var.eqn (Δ i) y) z) := by
  have hW := isOpen_nbhd (σ := σ) Δ y
  have hs : ∀ i, (Y.an σ).SmoothOn (nbhd Δ y) (Var.Met.wt (m i) (Var.eqn (Δ i) y)) := fun i =>
    ((hm i).2 _).mono (fun z hz => ⟨trivial, Set.mem_iInter.1 hz i⟩)
  refine ⟨hW, fun j => ContDiffOn.sum fun i _ => contDiffOn_const.mul (hs i j), fun c z hz hzW ξ => ?_⟩
  have hcd : ∀ i, ContDiffAt ℝ 2 ((fun w => (-a i) * Var.Met.wt (m i) (Var.eqn (Δ i) y) w) ∘ c.e.symm) (c.e z) :=
    fun i => contDiffAt_const.mul ((hs i).contDiffAt_two hW hz hzW)
  have hl : ∀ i, c.levi (fun w => (-a i) * Var.Met.wt (m i) (Var.eqn (Δ i) y) w) z ξ =
      (-a i) * c.levi (Var.Met.wt (m i) (Var.eqn (Δ i) z)) z ξ := fun i => by
    rw [AlgChart.levi_const_mul _ ((hs i).contDiffAt_two hW hz hzW),
      CombCurv.levi_wt_frame (hm i) hz (Set.mem_iInter.1 hzW i) (Var.mem_eqnSet _ z)]
  simp only [curvMet, ddcForm]
  rw [CombCurv.levi_sum Finset.univ _ hcd ξ, Finset.sum_congr rfl fun i _ => hl i, Finset.sum_div,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end General

end GlobalTheory.ClosedRefCurv

namespace GlobalTheory

open GlobalTheory.ClosedRefCurv in

theorem thW_refMet_isClosedForm : OnCore fun D O x _ => ∀ c (σ : D.what₂.LL →+* ℂ) (u : D.what₂.Tau → Fin O.N → ℝ), GlobalTheory.Published.IsClosedForm (AnRead.all (O.var c).str σ (O.var c).dim) (thW (refMet x O.Φ) c σ u) := by
  intro D O x P _ _ _ c σ u y
  obtain ⟨ho, hs, he⟩ := isPotential_neg_sum_curvMet (fun r : DV.Rt D.what₂.Tau O.N => refMet x O.Φ c σ (rootExp _ r))
    (fun r => (GlobalTheory.metsOf_smooth _ _ _ _ _ _ _ x O.Φ c σ _).2.1) (fun r => u r.1 r.2) y
  exact ⟨_, _, mem_nbhd _ y, ho, (AnRead.smoothOn_iff _ _ ho).1 hs, he⟩

end GlobalTheory

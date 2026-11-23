import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ShFam.CombCurv
open ReciprocityTheory.L2DbarEstimates
variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ}

variable {ι : Type} [Fintype ι]

theorem levi_const (c : AlgChart Y.str σ Y.dim) (a : ℝ) (y : Pts Y σ) (ξ : Fin Y.dim → ℂ) :
    c.levi (fun _ => a) y ξ = 0 := by
  rw [AlgChart.levi, ReciprocityTheory.L2DbarEstimates.Y.cmpb_leviV_const, Complex.zero_re]

theorem levi_wt_frame {Δ : Y.Dv} {m : Var.Met Y σ Δ} (hm : Var.mSmooth Y σ Δ m) {c : AlgChart Y.str σ Y.dim}
    {g g' : Y.Fnˣ} {y : Pts Y σ} (hy : y ∈ c.e.source) (hg : y ∈ Var.eqnSet σ Δ g) (hg' : y ∈ Var.eqnSet σ Δ g')
    (ξ : Fin Y.dim → ℂ) : c.levi (m.wt g') y ξ = c.levi (m.wt g) y ξ :=
  AnRead.levi_eq_of_add_log (R := Y.an σ) ((Var.isOpen_eqnSet Δ g).inter (Var.isOpen_eqnSet Δ g'))
    ((hm.2 g).mono (fun _ hz => ⟨trivial, hz.1⟩)) (Var.holoOn_tv Δ g g') (fun _ hz => Var.tv_ne_zero hz.1 hz.2)
    (fun _ hz => Var.Met.wt_trans (hm.1 trivial) hz.1 hz.2) hy ⟨hg, hg'⟩ ξ

theorem levi_sum {κ : Type} (s : Finset κ) {c : AlgChart Y.str σ Y.dim} {y : Pts Y σ} (f : κ → Pts Y σ → ℝ)
    (hf : ∀ k, ContDiffAt ℝ 2 (f k ∘ c.e.symm) (c.e y)) (ξ : Fin Y.dim → ℂ) :
    c.levi (fun z => ∑ k ∈ s, f k z) y ξ = ∑ k ∈ s, c.levi (f k) y ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using levi_const c 0 y ξ
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [AlgChart.levi_add (g := fun z => ∑ k ∈ s, f k z) (hf a) (ContDiffAt.sum fun k _ => hf k) ξ, ih]

end GlobalTheory.ShFam.CombCurv

namespace GlobalTheory.ShFam.CombCurv
section Comb
variable {F : Type} [Field F] [NumberField F] {Y : Var F} {ι : Type} [Fintype ι]
  (ρ : ι → Adl (cxSt F) Y) (t : ι → ℚ) (g : ∀ σ, Pts Y σ → ℝ) (σ : F →+* ℂ)

end Comb
end GlobalTheory.ShFam.CombCurv

namespace GlobalTheory.ShFam.CombCurv
section Main
variable {F : Type} [Field F] [NumberField F] {Y : Var F} {ι : Type} [Fintype ι]
  (ρ : ι → Adl (cxSt F) Y) (t : ι → ℚ) (g : ∀ σ, Pts Y σ → ℝ) (σ : F →+* ℂ)

def nbhd (y₀ : Pts Y σ) : Set (Pts Y σ) := ⋂ i, Var.eqnSet σ (ρ i).D (eqn (ρ i).D (under y₀))

theorem isOpen_nbhd (y₀ : Pts Y σ) : IsOpen (nbhd ρ σ y₀) :=
  isOpen_iInter_of_finite fun _ => Var.isOpen_eqnSet _ _

omit [Fintype ι] in
theorem mem_nbhd (y₀ : Pts Y σ) : y₀ ∈ nbhd ρ σ y₀ := Set.mem_iInter.2 fun _ => Base.isEqn_eqn _ _

def wtNear (y₀ z : Pts Y σ) : ℝ :=
  ∑ i, (combNum ρ t i : ℝ) * (Var.Met.wt ((ρ i).m σ) (eqn (ρ i).D (under y₀)) z +
    2 * ((ρ i).n : ℕ) * (ρ i).ci (InfinitePlace.mk σ)) + 2 * ((combDen ρ t : ℕ) : ℝ) * g σ z

variable {ρ g σ}

end Main
end GlobalTheory.ShFam.CombCurv

namespace GlobalTheory.ShFam.CombCurv
section Curv
variable {F : Type} [Field F] [NumberField F] {Y : Var F} {ι : Type} [Fintype ι]
  {ρ : ι → Adl (cxSt F) Y} (t : ι → ℚ) {g : ∀ σ, Pts Y σ → ℝ} {σ : F →+* ℂ}

end Curv
end GlobalTheory.ShFam.CombCurv

namespace GlobalTheory.ShFam.CombCurv

end GlobalTheory.ShFam.CombCurv

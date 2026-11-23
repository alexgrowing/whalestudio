import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic
open ReciprocityTheory.L2DbarEstimates (V leviV)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem semiPos_of_isFS : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (D : ℕ) (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ),
    IsFS M f w → M.SemiPos D := by
  intro k _ X _ p D M J _ f w hM σ i c y hy ξ
  classical
  obtain ⟨ρ, -, hreg, hφ⟩ := hM
  have hx : under y ∈ M.B.U i := mem_ptsIn.1 hy.2
  obtain ⟨hr, j0, hu⟩ := hreg (under y) i hx
  choose U hU a ha using fun j => (hr j).exists_fnOf
  let G (j : J) (v : V D) : ℂ := (Real.exp (w j) : ℂ) * ev p σ (U j) (a j) (c.e.symm v)
  let S : Set (CxPts p σ) := ptsIn p σ (M.B.U i) ∩ ⋂ j, ptsIn p σ (U j)
  have hSo : IsOpen S := (isOpen_ptsIn _).inter (isOpen_iInter_of_finite fun j => isOpen_ptsIn _)
  have hyS : y ∈ S := ⟨hy.2, Set.mem_iInter.2 fun j => mem_ptsIn.2 (hU j)⟩
  have hO := isOpen_over c.e hSo
  have hmO := mem_over c.e hy.1 hyS

  have hval (z : CxPts p σ) (hz : z ∈ S) (j : J) :
      ratVal (f j * (ρ i : X.functionField)) z = ev p σ (U j) (a j) z := by
    rw [← ha j]
    exact ratVal_fnOf (Set.mem_iInter.1 hz.2 j) _ _
  have hterm (z : CxPts p σ) (hz : z ∈ S) (j : J) :
      ‖ratVal (f j * (ρ i : X.functionField)) z‖ ^ 2 * Real.exp (2 * w j) =
        Complex.normSq ((Real.exp (w j) : ℂ) * ev p σ (U j) (a j) z) := by
    rw [hval z hz j, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq,
      ← Real.exp_add]
    ring_nf
  have hG (j : J) : ContDiffAt ℂ 2 (G j) (c.e y) := by
    have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (U j))
    have hm := mem_over c.e hy.1 (mem_ptsIn.2 (hU j))
    exact contDiffAt_const.mul ((((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho
      (c.holo (U j) (a j))).contDiffAt (ho.mem_nhds hm)).of_le (by norm_cast)))
  let e := Fintype.equivFin J
  let u (b : Fin (Fintype.card J)) (v : V D) : ℝ := Complex.normSq (G (e.symm b) v)
  have hsum (v : V D) : ∑ b, u b v = ∑ j, Complex.normSq (G j v) :=
    Equiv.sum_comp e.symm fun j => Complex.normSq (G j v)
  have hev : (fun v => (((M.φ σ).φ i (c.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
      fun v => ((Real.log (∑ b, u b v) : ℝ) : ℂ) := by
    filter_upwards [hO.mem_nhds hmO] with v hv
    rw [hφ σ _ i hv.2.1, hsum]
    congr 2
    exact Finset.sum_congr rfl fun j _ => hterm _ hv.2 j
  have hpos : 0 < ∑ b, u b (c.e y) := by
    rw [hsum]
    simp only [G, c.e.left_inv hy.1]
    refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨j0, Finset.mem_univ _, ?_⟩
    rw [← hterm y hyS j0]
    exact mul_pos (pow_pos (norm_pos_iff.2 (ratVal_ne_zero hu)) 2) (Real.exp_pos _)
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr hev]
  exact ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg
    (fun b => ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp (hG _))
    (fun b => ReciprocityTheory.L2DbarEstimates.logPshAt_normSq (hG _)) hpos ξ

end GlobalTheory.HSNef

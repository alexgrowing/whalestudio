import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem jn_firstCols {D : D7} {a r t n : ℕ} (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) :
    (jn hn w v).submatrix id (fun j : Fin r => finCongr hn (Fin.castAdd t j)) = w := by
  ext i j
  have e : (finSumFinEquiv.trans (finCongr hn)).symm (finCongr hn (Fin.castAdd t j)) = Sum.inl j := by
    rw [Equiv.symm_apply_eq]
    simp
  simp only [jn, Matrix.submatrix_apply, id, e, Matrix.fromCols_apply_inl]

theorem continuous_jn_pair {D : D7} {a r t n : ℕ} (hn : r + t = n) :
    Continuous fun p : Mx D a r × Mx D a t => jn hn p.1 p.2 := by
  refine continuous_matrix fun i j => ?_
  simp only [jn, Matrix.submatrix_apply, id]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm j with k | k
  · simpa using (continuous_fst.matrix_elem i k)
  · simpa using (continuous_snd.matrix_elem i k)

theorem continuous_orb_shear : IkSch → Dom → OrbFin → Shift → JnBl → Ext0 → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t)
    (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), x₀.det ≠ 0 →
    ∀ Φ ∈ schwartzA θ B.rank n,
      Continuous (fun y : Mx D W.rank t => orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀)) := by
  intro hIk hDom hOrb hShift hJn hExt D n t B W d hn I θ hθ x₀ hx Φ hΦ
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨hT, -, hS, -, -⟩ := top_mx (D := D) W.rank t
  obtain ⟨hT', -, -, -, -⟩ := top_mx (D := D) W.rank W.rank
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hBor : BorelSpace (GA D W) := ⟨rfl⟩
  have hΨ : ikp I Φ ∈ schwartzA θ W.rank n := (hIk D n t B W d I θ hθ Φ hΦ).2
  have hcΨ : Continuous (ikp I Φ) := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ _ hΨ).1
  have hinj : Function.Injective fun j : Fin W.rank => finCongr hn (Fin.castAdd t j) := by
    intro a b h
    exact Fin.castAdd_injective _ _ ((finCongr hn).injective h)
  obtain ⟨M, hM, -, hMd⟩ := hDom D θ hθ W.rank n W.rank _ hinj _ hΨ
  have hcM : Continuous M := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ M hM).1
  have hform : ∀ (y : Mx D W.rank t) (h : GA D W),
      (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (mm (mt W h⁻¹) (rat (ext0 hn x₀))) =
        ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) := by
    intro y h
    rw [hShift D n t B W d hn I Φ y, hExt D n t W hn x₀ h, hJn D n t W.rank W.rank hn]
  have hfun : (fun y : Mx D W.rank t => orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀)) =
      fun y => ∫ h, ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) ∂I.m := by
    funext y
    exact integral_congr_ae (Eventually.of_forall fun h => hform y h)
  rw [hfun]
  have hcw := continuous_ww (D := D) (W := W) x₀
  have hb : Integrable (fun h => M (ww W x₀ h)) I.m :=
    ⟨(hcM.comp hcw).aestronglyMeasurable, hOrb D θ hθ W I.m I.haar x₀ hx M hM⟩
  have hpt : ∀ (h : GA D W), Continuous fun y : Mx D W.rank t => ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) := by
    intro h
    refine hcΨ.comp ((continuous_jn_pair hn).comp (continuous_const.prodMk ?_))
    exact (continuous_const.matrix_mul continuous_id).add continuous_const
  have hmeas : ∀ y : Mx D W.rank t, Continuous fun h : GA D W => ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) := by
    intro y
    refine hcΨ.comp ((continuous_jn_pair hn).comp (hcw.prodMk ?_))
    exact (hcw.matrix_mul continuous_const).add continuous_const
  have hF : FirstCountableTopology (Mx D W.rank t) :=
    @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ hS
  refine continuous_of_dominated (bound := fun h => ‖M (ww W x₀ h)‖)
    (fun y => (hmeas y).aestronglyMeasurable) (fun y => Eventually.of_forall fun h => ?_) hb.norm
    (Eventually.of_forall hpt)
  have h1 := hMd (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0))
  rw [jn_firstCols] at h1
  exact h1.trans (Complex.re_le_norm _)

end GlobalTheory.CompanionTheory.ColumnSplitting

end

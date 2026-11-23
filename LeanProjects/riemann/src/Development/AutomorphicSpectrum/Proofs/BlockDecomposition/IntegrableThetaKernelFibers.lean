import Mathlib
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

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Form

theorem continuous_jn_pair {D : D7} {a r t n : ℕ} (hn : r + t = n) :
    Continuous fun z : Mx D a r × Mx D a t => jn hn z.1 z.2 := by
  unfold jn
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.submatrix_apply, id]
  cases (finSumFinEquiv.trans (finCongr hn)).symm j with
  | inl c => simpa using continuous_fst.matrix_elem i c
  | inr c => simpa using continuous_snd.matrix_elem i c

theorem continuous_yv_pair {D : D7} {r t : ℕ} (V : HSp D) (b₀ : HermE D r) :
    Continuous (yv (t := t) V b₀) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  unfold yv ip
  exact continuous_const.matrix_mul ((continuous_adj.comp continuous_fst).matrix_mul
    (continuous_const.matrix_mul continuous_snd))

theorem nuT_form : ZpEq → AcEq → JnPi → Ext0 → Fub4 → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t)
    (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure →
    ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → ∀ Φ ∈ schwartzA θ B.rank n,
    ∀ η ∈ schwartzA θ W.rank t, Integrable (core hn I x₀ Φ η) (I.νK.prod (Q0 I μ)) →
    Integrable (fun z => Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z))) (nuT hn I μ x₀) ∧
    ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z)) ∂(nuT hn I μ x₀) =
      ∫ y, orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀) * conj (η y) ∂μ := by
  intro hZ hA hJ hE hF D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx Φ hΦ η hη hint
  obtain ⟨g1, g2⟩ := top_pair (D := D) B.rank W.rank t
  obtain ⟨-, -, p3, -, p5⟩ := top_mx (D := D) B.rank W.rank
  obtain ⟨-, -, p3', -, p5'⟩ := top_mx (D := D) B.rank t
  have hΦc := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ Φ hΦ).1
  have hηc := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ η hη).1
  have hGc : Continuous fun z : Mx D B.rank W.rank × Mx D B.rank t =>
      Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z)) :=
    (hΦc.comp (continuous_jn_pair hn)).mul
      (Complex.continuous_conj.comp (hηc.comp (continuous_yv_pair B b₀)))
  have hπ := measurable_pi hn I x₀
  have hcomp : (fun z : Mx D B.rank W.rank × Mx D B.rank t => Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z))) ∘
      (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) = core hn I x₀ Φ η := by
    funext p
    obtain ⟨k, q⟩ := p
    simp only [Function.comp, core]
    rw [hJ D n t B W d hn x₀ _ q, (hA D W.rank t B b₀ _ _).2.1, (hZ D n t B W d hn b₀ hb x₀ hx q).2.1]
  refine ⟨?_, ?_⟩
  · unfold nuT
    rw [integrable_map_measure hGc.aestronglyMeasurable hπ.aemeasurable, hcomp]
    exact hint
  · have e1 : ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z)) ∂(nuT hn I μ x₀) =
        ∫ p, core hn I x₀ Φ η p ∂(I.νK.prod (Q0 I μ)) := by
      unfold nuT
      rw [integral_map hπ.aemeasurable hGc.aestronglyMeasurable, ← hcomp]
      rfl
    rw [e1]
    obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
    obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
    obtain ⟨-, k2, k3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
    have : BorelSpace (GA D W) := ⟨rfl⟩
    obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
    have := hf.1
    have := I.haar
    have := I.probK
    have e2 := (hF I.l.K (GA D W) (Mx D t n) (Mx D W.rank t) I.νK I.m I.μ₁ μ).1 _ hint
    unfold Q0
    rw [e2]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [core]
    simp_rw [integral_mul_const]
    congr 1
    unfold orb
    refine integral_congr_ae (ae_of_all _ fun h => ?_)
    simp only [hE D n t W hn x₀ h, ikp, ikS, projS, XU]
    refine integral_congr_ae (ae_of_all _ fun u => integral_congr_ae (ae_of_all _ fun k => ?_))
    simp only [mm, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.ColumnSplitting.Form

end

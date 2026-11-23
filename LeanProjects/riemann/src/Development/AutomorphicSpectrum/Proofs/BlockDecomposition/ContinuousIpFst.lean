import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EmDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestAlg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbscissaConvergenceIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedBlockFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousThetaKernelComponents
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IpSmulRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulInvSub

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.OrbExist

variable {D : D7} {a n r t : ℕ}

theorem continuous_qv (V : HSp D) (b₀ : HermE D r) :
    Continuous (fun z : Mx D V.rank r × Mx D V.rank t => qv V b₀ z) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hip : ∀ {X : Type} [TopologicalSpace X] {a c : ℕ} {f : X → Mx D V.rank a} {g : X → Mx D V.rank c},
      Continuous f → Continuous g → Continuous (fun x => ip V (f x) (g x)) := by
    intro X _ a c f g hf hg
    unfold ip
    exact (continuous_adj.comp hf).matrix_mul (continuous_const.matrix_mul hg)
  have hyv : Continuous (fun z : Mx D V.rank r × Mx D V.rank t => yv V b₀ z) := by
    unfold yv
    exact continuous_const.matrix_mul (hip continuous_fst continuous_snd)
  have hpr : Continuous (fun x : Mx D V.rank r × Mx D V.rank t => pr b₀ (yv V b₀ x) (yv V b₀ x)) := by
    unfold pr
    exact (continuous_adj.comp hyv).matrix_mul (continuous_const.matrix_mul hyv)
  unfold qv
  have h1 : Continuous (fun z : Mx D V.rank r × Mx D V.rank t => ip V z.2 z.2) := hip continuous_snd continuous_snd
  have hn : ContinuousNeg (AE D) := IsTopologicalRing.toContinuousNeg
  have ha : ContinuousAdd (AE D) := IsTopologicalSemiring.toContinuousAdd
  exact continuous_matrix fun i j => (h1.matrix_elem i j).add (hpr.matrix_elem i j).neg |>.congr fun z => (sub_eq_add_neg _ _).symm

theorem continuous_ip_fst (V : HSp D) :
    Continuous (fun z : Mx D V.rank r × Mx D V.rank t => ip V z.1 z.1) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  unfold ip
  exact (continuous_adj.comp continuous_fst).matrix_mul (continuous_const.matrix_mul continuous_fst)

theorem continuous_pch₂ {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {X : Type} [TopologicalSpace X]
    {f g : X → Mx D t t} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => pch ψ (f x) (g x)) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have htr : Continuous (trA : AE D → AF D.host.F) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hhalf : Continuous (halfTr : AE D → AF D.host.F) := by
    unfold halfTr
    exact continuous_const.mul htr
  unfold pch
  exact hψ.1.comp (hhalf.comp (hf.matrix_mul hg).matrix_trace)

theorem isClosed_fixed (e : AE D) :
    IsClosed {z : Mx D a r × Mx D a t | e • z.1 = z.1 ∧ e • z.2 = z.2} := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, h1, -⟩ := GlobalTheory.CompanionTheory.ColumnSplitting.top_mx (D := D) a r
  obtain ⟨-, -, -, h2, -⟩ := GlobalTheory.CompanionTheory.ColumnSplitting.top_mx (D := D) a t
  have c1 : Continuous fun x : Mx D a r => e • x := continuous_const_smul e
  have c2 : Continuous fun x : Mx D a t => e • x := continuous_const_smul e
  exact (isClosed_eq (c1.comp continuous_fst) continuous_fst).inter (isClosed_eq (c2.comp continuous_snd) continuous_snd)

theorem conj_cancel (g : GL (Fin t) (AE D)) (q : Mx D t t) :
    mm (mm (adj (g⁻¹).1) (mm (mm (adj g.1) q) g.1)) (g⁻¹).1 = q := by
  have h1 : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : (adj (g⁻¹).1 * adj g.1 : Mx D t t) = 1 := by
    have := adj_mul (D := D) g.1 (g⁻¹).1
    rw [← this, h1, adj_one_r]
  simp only [mm]
  calc _ = (adj (g⁻¹).1 * adj g.1 : Mx D t t) * q * (g.1 * (g⁻¹).1) := by simp only [Matrix.mul_assoc]
    _ = q := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem comp_mem {θ : InfFam D} (hθ : IsInfFam θ) {hn : r + t = n} {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e)
    (hR : ∀ f ∈ algA (a := a) θ hn S e,
      ∃ Φ ∈ schwartzA θ a n, Good S e Φ ∧ HasCompactSupport Φ ∧ f = fun z => Φ (jn hn z.1.1 z.1.2))
    (hSt : AlgStab) (h : GL (Fin a) (AE D)) (g : GL (Fin n) (AE D)) (hh : e • (h.1 - 1) = h.1 - 1) (hg : e • (g.1 - 1) = g.1 - 1)
    (Θ : XS D a r t e → XS D a r t e)
    (hΘ : ∀ z, jn hn (Θ z).1.1 (Θ z).1.2 = mm (mm h.1 (jn hn z.1.1 z.1.2)) g.1) (f : XS D a r t e → ℂ)
    (hf : f ∈ algA (a := a) θ hn S e) : f ∘ Θ ∈ algA (a := a) θ hn S e := by
  obtain ⟨Φ, h1, h2, h3, rfl⟩ := hR f hf
  obtain ⟨m1, m2, m3⟩ := hSt D θ hθ a n S e hS h g hh hg Φ h1 h2 h3
  refine Submodule.subset_span ⟨_, m1, m2, m3, ?_⟩
  funext z
  simp only [Function.comp, hΘ]

theorem trans_int₁ {X N : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace N] [MeasurableSpace N]
    [BorelSpace N] (σ : Measure X) (lam : Measure N) (k : N → X → ℂ) (f : X → ℂ) (Θ : X ≃ₜ X)
    (h₁ : σ.map Θ = σ) (hk : ∀ x, ∀ᵐ z ∂σ, k x z = k x (Θ z)) :
    ∫ x, ∫ z, f (Θ z) * k x z ∂σ ∂lam = ((1 : ℝ≥0) : ℂ) * ∫ x, ∫ z, f z * k x z ∂σ ∂lam := by
  have := trans_int σ lam k f Θ (Homeomorph.refl N) 1 1 (by rw [one_smul]; exact h₁) (by simp) hk
  simpa using this

theorem kap (A : ℝ≥0) (hA : A ≠ 0) (N r t : ℕ) (hN : N = r + 2 * t) : (A⁻¹) ^ N * ((A⁻¹)⁻¹) ^ t = (A⁻¹) ^ (r + t) := by
  subst hN
  rw [inv_inv, two_mul, ← add_assoc, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hA, one_pow, mul_one]

theorem absA_inv (D : D7) (u : (AE D)ˣ) : absA D u⁻¹ = (absA D u)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, inv_mul_cancel, map_one]

theorem absA_ne (D : D7) (u : (AE D)ˣ) : absA D u ≠ 0 := by
  have h1 : absA D u * absA D u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  intro h
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

end GlobalTheory.CompanionTheory.OrbExist

end

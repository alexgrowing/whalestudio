import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueAdelicMatrixRealComponentsFinitePartStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPolynomialMulGaussianOfAnnihilatedStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.Slice

variable {D : D7}

theorem compAt_add' (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} (x y : Mx D m n) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y :=
  Matrix.ext fun i j => by
    show θ τ (infPart D (x i j + y i j)) = θ τ (infPart D (x i j)) + θ τ (infPart D (y i j))
    rw [RingHom.map_add, RingHom.map_add]

theorem finMap_add {m n : ℕ} (x y : Mx D m n) :
    (x + y).map (finPart D) = x.map (finPart D) + y.map (finPart D) :=
  Matrix.ext fun i j => by
    show finPart D (x i j + y i j) = finPart D (x i j) + finPart D (y i j)
    rw [RingHom.map_add]

theorem slice_polyGauss : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : RealMat V), (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ (N : ℕ), ∀ φ ∈ schwartzA θ V.rank n, (∀ L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ), L.length = N → L.foldr (fun q g => annS V l s θ q.1 q.2 g) φ = 0) → ∀ x₀ : Mx D V.rank n, ∃ p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ, ∀ x : Mx D V.rank n, x.map (finPart D) = x₀.map (finPart D) → φ x = evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) := by
  intro D θ hθ V n l s hs N φ hφ hL x₀
  have hE := fun z : D.what₂.Tau → Fin V.rank → Fin n → ℂ =>
    GlobalTheory.T.existsUnique_adelicMatrix_realComponents_finitePart D θ hθ V.rank n (fun τ => Matrix.of (z τ)) x₀
  let ι : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → Mx D V.rank n := fun z => Classical.choose (hE z).exists
  have hι : ∀ z, (∀ τ, compAt θ τ (ι z) = Matrix.of (z τ)) ∧ (ι z).map (finPart D) = x₀.map (finPart D) :=
    fun z => Classical.choose_spec (hE z).exists
  have huniq : ∀ z x, (∀ τ, compAt θ τ x = Matrix.of (z τ)) → x.map (finPart D) = x₀.map (finPart D) → x = ι z :=
    fun z x h1 h2 => (hE z).unique ⟨h1, h2⟩ (hι z)
  have hline : ∀ z τ (X : Matrix (Fin V.rank) (Fin n) ℂ) (w : D.what₂.Tau → Fin V.rank → Fin n → ℂ),
      w τ = X → (∀ τ', τ' ≠ τ → w τ' = 0) → ∀ t : ℝ, ι (z + t • w) = ι z + lineAt θ τ X t := by
    intro z τ X w hw0 hw1 t
    have hLn : IsLineAt θ τ X (lineAt θ τ X) :=
      Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ V.rank n τ X)
    symm
    apply huniq
    · intro τ'
      rw [compAt_add', (hι z).1, hLn.2.2 t τ']
      ext i j
      by_cases h : τ' = τ
      · subst h
        rw [if_pos rfl]
        show z τ' i j + ((t : ℂ) • X) i j = z τ' i j + t • w τ' i j
        rw [hw0, Complex.real_smul]
        rfl
      · rw [if_neg h]
        show z τ' i j + (0 : Matrix (Fin V.rank) (Fin n) ℂ) i j = z τ' i j + t • w τ' i j
        rw [hw1 τ' h]
        simp
    · rw [finMap_add, (hι z).2, hLn.2.1 t, add_zero]
  have hcomm : ∀ τ X (g : Mx D V.rank n → ℂ),
      annC V l s τ X (fun z => g (ι z)) = fun z => annS V l s θ τ X g (ι z) := by
    intro τ X g
    funext z
    simp only [annC, annS]
    congr 1
    · congr 1
      funext t
      congr 1
      apply hline z τ X
      · simp
      · intro τ' h
        simp [h]
    · rw [(hι z).1]
  have hfold : ∀ L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ),
      L.foldr (fun q g => annC V l s q.1 q.2 g) (fun z => φ (ι z)) =
        fun z => (L.foldr (fun q g => annS V l s θ q.1 q.2 g) φ) (ι z) := by
    intro L
    induction L with
    | nil => rfl
    | cons q L ih => simp only [List.foldr_cons, ih, hcomm]
  have hsm : ∀ ψ : Mx D V.rank n → ℂ, ψ ∈ schwartzA θ V.rank n → ContDiff ℝ ∞ (fun z => ψ (ι z)) := by
    intro ψ hψ
    unfold schwartzA at hψ
    induction hψ using Submodule.span_induction with
    | mem ψ hψ =>
      obtain ⟨f, g, -, rfl⟩ := hψ
      have e : (fun z => f (fun τ i j => compAt θ τ (ι z) i j) * g (fun i j => finPart D (ι z i j))) =
          fun z => f z * g (fun i j => finPart D (x₀ i j)) := by
        funext z
        congr 1
        · congr 1
          funext τ i j
          rw [(hι z).1]
          rfl
        · congr 1
          funext i j
          exact congrFun (congrFun (hι z).2 i) j
      simp only
      rw [e]
      exact (f.smooth ⊤).mul contDiff_const
    | zero => exact contDiff_const
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  have hsmooth := hsm φ hφ
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_polynomial_mul_gaussian_of_annihilated D V n l s hs N (fun z => φ (ι z)) hsmooth (fun L hLN => by
    rw [hfold, hL L hLN]
    rfl)
  refine ⟨p, fun x hx => ?_⟩
  have hx' : x = ι (fun τ i j => compAt θ τ x i j) := huniq _ x (fun τ => rfl) hx
  calc φ x = φ (ι (fun τ i j => compAt θ τ x i j)) := by rw [← hx']
    _ = _ := hp _

end GlobalTheory.StdUnn.Slice

end

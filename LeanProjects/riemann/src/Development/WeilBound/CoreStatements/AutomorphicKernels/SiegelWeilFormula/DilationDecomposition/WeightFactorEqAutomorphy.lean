import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocDerBig
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocForm
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SmulOneConj
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

open PositivityTheory.Rg.Sw.Glob (aC ptZ jC gC actZ jF IsSiegel gZf)
open Matrix

variable {n : ℕ}

def Gf (e : ℤ) (p q : ℕ) (t : ℝ) {m : ℕ} (X : Fin n → ℝ) (y : GR n) (z : ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  jC e p q y X z * gC (fun _ : Fin m => true) t (2 * Real.pi) (ptZ y X z Complex.I) (ptZ y X z (-Complex.I)) u

def GfBound : Prop := ∀ (m n : ℕ) (e : ℤ) (p q : ℕ) (t : ℝ) (X : Fin n → ℝ), |t| = 2 * Real.pi →
  (∀ (y : GR n) u, DifferentiableOn ℂ (fun z => Gf e p q t (m := m) X y z u) (strip X)) ∧
  ContinuousOn (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => Gf e p q t X p'.1 p'.2.1 p'.2.2)
    (Set.univ ×ˢ (strip X ×ˢ Set.univ)) ∧
  ∀ (y₀ : GR n) (z₀ : ℂ), z₀ ∈ strip X → ∃ (N : Set (GR n × ℂ)) (δ C : ℝ), N ∈ 𝓝 (y₀, z₀) ∧ 0 < δ ∧
    ∀ p' ∈ N, p'.2 ∈ strip X → ∀ u : Fin m → Fin n → ℂ,
      ‖Gf e p q t X p'.1 p'.2 u‖ ≤ C * Real.exp (-(δ * ∑ a, ∑ j, ‖u a j‖ ^ 2))

theorem weight_factor_eq_automorphy (p q : ℕ) (e : ℤ) (y : GR n) : F0 p q e y = jF e p q y (Complex.I • 1) := by
  simp only [F0, f0, jF, u1, u2, Matrix.mul_smul, Matrix.mul_one, conjTranspose_smul, conjTranspose_one, Complex.star_def,
    Complex.conj_I, neg_smul, Matrix.mul_neg, mul_assoc]

open PositivityTheory.Rg.Sw.Glob.DRealH in

theorem gf_real (e : ℤ) (p q : ℕ) (t : ℝ) {m : ℕ} (X : Fin n → ℝ) (a : ℝ → GR n)
    (ha : ∀ s, IsDil X s (a s)) (y : GR n) (s : ℝ) :
    Gf e p q t (m := m) X y s = fun u => F0 p q e (y * a s) *
      gZf (fun _ : Fin m => true) t (2 * Real.pi) (actZ (y * a s) (Complex.I • 1)) u := by
  funext u
  rw [weight_factor_eq_automorphy]
  have hg : InG (mR (y * a s)) := (y * a s).2
  have hM : mR (y * a s) = mR y * aC X s := by
    have h1 : mR (y * a s) = mR y * mR (a s) := rfl
    rw [h1, ha s]
    unfold aC
    have e1 : (fun j => ((Real.exp (s * X j) : ℝ) : ℂ)) = fun j => Complex.exp ((s : ℂ) * X j) := by
      funext j; rw [Complex.ofReal_exp]; push_cast; ring_nf
    have e2 : (fun j => ((Real.exp (-(s * X j)) : ℝ) : ℂ)) = fun j => Complex.exp (-((s : ℂ) * X j)) := by
      funext j; rw [Complex.ofReal_exp]; push_cast; ring_nf
    rw [e1, e2]
  obtain ⟨h1, h2, h3, h4⟩ := blocks_of_inG hg
  have hI : star Complex.I ≠ Complex.I := by
    rw [Complex.star_def, Complex.conj_I]
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have hconj := conj_frac h1 h2 h3 h4 Complex.I hI
  have hsI : star Complex.I = -Complex.I := by rw [Complex.star_def, Complex.conj_I]
  rw [hsI] at hconj
  simp only [Gf, jC, gC, jF, gZf, actZ, ptZ]
  rw [← hM]
  simp only [Matrix.mul_smul, Matrix.mul_one, smul_one_conj, hsI]
  rw [hconj]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem abs_tw {d : SD σ} (R : RD d) (w : InfinitePlace F) : |2 * Real.pi * ((R.sg w : ℤ) : ℝ)| = 2 * Real.pi := by
  rcases Int.units_eq_one_or (R.sg w) with h | h <;> simp [h, abs_of_pos Real.pi_pos]

end PositivityTheory.SiegelWeilFormula.Kdil

end

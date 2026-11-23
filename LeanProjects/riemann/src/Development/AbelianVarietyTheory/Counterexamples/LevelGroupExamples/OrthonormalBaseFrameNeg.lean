import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInfEmbUnique

noncomputable section

namespace GlobalTheory.LettersCheck

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem isInfEmb_unique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (τ : E →+* ℂ) (θ θ' : Ainf F ⊗[F] E →+* ℂ) (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) (h' : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ') :
    θ = θ' :=
  by apply _root_.UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption

theorem xiR_pos (D : D7) : 0 < xiR D := by
  unfold xiR
  refine norm_pos_iff.2 ((map_ne_zero _).2 ?_)
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h
    have h1 := sq_emb D D.host.φ₀
    rw [h, map_zero] at h1
    have h2 : (D.host.d : ℂ) = 0 := by linear_combination h1
    have h3 := D.host.qd_big.2
    have h4 : D.host.d = 0 := by exact_mod_cast h2
    omega
  show -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) ≠ 0
  exact div_ne_zero (by simp) (mul_ne_zero (normK_ne_zero D) hs)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem lminor_sgn (p0 : ℕ) (i : Fin (r + 1)) :
    lminor (Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) i = ((psgn p0 i : ℝ) : ℂ) := by
  unfold lminor psgn
  rw [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, Complex.ofReal_prod,
    ← Fin.prod_univ_eq_prod_range (fun a => ((sgn p0 a : ℝ) : ℂ))]
  rfl

theorem psgn_sq (p0 i : ℕ) : psgn p0 i * psgn p0 i = 1 := by
  unfold psgn
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold sgn
  split_ifs <;> norm_num

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G P = P.transpose * (G.map τ * P.map (starRingEnd ℂ)) := by
  ext a b
  simp [gram, hermC, col, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

theorem unit_of_x0Orth (X : Data E r) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (h : IsOrthogonalFrame X x₀) :
    (fun τ : X.Ψ => (x₀ τ.1 : Fin r → Fin r → ℂ)) ∈ X.dom ∧
      ∀ τ i, ‖dmin X.Gm (fun τ : X.Ψ => (x₀ τ.1 : Fin r → Fin r → ℂ)) τ i‖ = 1 := by
  have hd : ∀ (τ : X.Ψ) i, dmin X.Gm (fun τ : X.Ψ => (x₀ τ.1 : Fin r → Fin r → ℂ)) τ i =
      ((psgn X.p0 i : ℝ) : ℂ) := fun τ i => by
    rw [← lminor_sgn, ← h τ.1 τ.2]
    rfl
  refine ⟨fun τ => ⟨?_, fun i => ?_⟩, fun τ i => ?_⟩
  · show (x₀ τ.1).det ≠ 0
    intro h0
    have h1 := congrArg Matrix.det (h τ.1 τ.2)
    rw [gram_eq, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, Matrix.det_diagonal] at h1
    refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h1.symm
    unfold sgn
    split_ifs <;> simp
  · rw [hd, Complex.ofReal_re, psgn_sq]
    exact one_pos
  · rw [hd, Complex.norm_real]
    have h := congrArg abs (psgn_sq X.p0 i)
    rw [abs_mul, abs_one] at h
    have h0 := abs_nonneg (psgn X.p0 i)
    rw [Real.norm_eq_abs]
    nlinarith

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}

theorem relab_val (c : Coeff l) (τ : E →+* ℂ) : relab c c.F.val.toRingHom τ = τ := by
  ext a
  rfl

end GlobalTheory.LettersCheck

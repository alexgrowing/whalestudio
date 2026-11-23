import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ZReAddZImStar
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivOne
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.RealParExplicit

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.IInvH

variable {D : D7} {m n : ℕ}

theorem isUe_zRe (ε : Fin m → Bool) (a b : Fin m) : IsUe ε (zRe ε a b) := by
  have e1 : star ((1 : ℂ) / 2) = 1 / 2 := by simp
  ext i j
  simp only [IsUe, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply, zRe, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.single_apply, star_mul', star_sub, e1]
  by_cases h1 : a = i <;> by_cases h2 : b = j <;> by_cases h3 : b = i <;> by_cases h4 : a = j <;>
    simp only [h1, h2, h3, h4, and_true, true_and, and_false, false_and, if_true, if_false, mul_zero, zero_mul, sub_zero,
      zero_sub, add_zero, zero_add, mul_one, star_one, star_zero, star_neg, neg_zero, star_mul', sgn_star] <;>
    (try subst_vars) <;> unfold sgn <;> split_ifs <;>
    first | (exfalso; tauto) | (simp only [star_one, star_zero]; ring) | norm_num | (simp only [star_one, star_zero]; norm_num)

theorem isUe_zIm (ε : Fin m → Bool) (a b : Fin m) : IsUe ε (zIm ε a b) := by
  have e2 : star (-(Complex.I / 2)) = Complex.I / 2 := by
    apply Complex.ext <;> simp <;> norm_num
  ext i j
  simp only [IsUe, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply, zIm, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.single_apply, star_mul', star_add, e2]
  by_cases h1 : a = i <;> by_cases h2 : b = j <;> by_cases h3 : b = i <;> by_cases h4 : a = j <;>
    simp only [h1, h2, h3, h4, and_true, true_and, and_false, false_and, if_true, if_false, mul_zero, zero_mul, sub_zero,
      zero_sub, add_zero, zero_add, mul_one, star_one, star_zero, star_neg, neg_zero, star_mul', sgn_star] <;>
    (try subst_vars) <;> unfold sgn <;> split_ifs <;>
    first | (exfalso; tauto) | (simp only [star_one, star_zero]; ring) | ring | (simp only [star_one, star_zero]; norm_num)

theorem thetaInt_at {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V))
    (Φ : schwartzA θ V.rank n) (g : G D n) : thetaInt ω ν Φ g = thetaInt ω ν (ω g Φ) 1 := by
  have h : theta ω Φ g = theta ω (ω g Φ) 1 := by
    funext h
    simp only [theta, map_one, Module.End.one_apply]
  simp only [thetaInt, h]

theorem thetaInt_smul {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V))
    (r : ℂ) (Φ : schwartzA θ V.rank n) (g : G D n) : thetaInt ω ν (r • Φ) g = r * thetaInt ω ν Φ g := by
  have h : theta ω (r • Φ) g = fun h => r * theta ω Φ g h := by
    funext h
    simp only [theta, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact tsum_mul_left
  simp only [thetaInt, h, GlobalTheory.AutomorphicL2Unitary.descend, MeasureTheory.average_eq, integral_const_mul]
  exact (mul_smul_comm _ _ _).symm

theorem phiS_of_mem {θ : InfFam D} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ) (Ψ : Mx D m n → ℂ)
    (P : PX m n) (h : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n) : phiS θ τ fr c Ψ P = ⟨_, h⟩ := by
  unfold phiS; rw [dif_pos h]

theorem tens_add_smul {θ : InfFam D} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ) (Ψ : Mx D m n → ℂ)
    (A B : PX m n) (r : ℂ) :
    tens θ τ fr (fP c (A + r • B)) Ψ = tens θ τ fr (fP c A) Ψ + r • tens θ τ fr (fP c B) Ψ := by
  funext x
  simp only [tens, fP, evX, map_add, MvPolynomial.smul_eval, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.Rg.Sw.Glob.IInvH

namespace PositivityTheory.Rg.Sw.Glob

open IInvH in
theorem gIinv_of (hT : TensMem) (hL : ThLin) (hC : LieComm) (hO : DerivOne) : GIinv := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hx Ψ hΨ g a b P
  have hmem := fun Q => hT D n V θ l s τ ε fr hx.hθ (lNZ D ψ θ l hx.hψ hx.hθ hx.hl) hx.hs hx.hfr Ψ hΨ Q
  have hstd : ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ :=
    fun Φ hΦ => ⟨hx.hψ, hx.hχ, hx.hη, hx.hθ, hx.hμ, hx.hω, hx.hH, hx.hl, hx.hs, hx.hν, hΦ⟩

  have h0 : ∀ X, IsUe ε X → ∀ Q, thF ω ν τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X Q) g = 0 := by
    intro X hX Q
    unfold thF
    rw [thetaInt_at]
    exact hO D n V ψ χ θ μ ω H l s ν τ ε fr ι hx X hX (ω g (phiS θ τ fr (cLoc l τ) Ψ Q))
      (ω g (phiS θ τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X Q))) (fun x => hC D n V ψ χ θ μ ω H l s ν τ ε fr ι hx Ψ hΨ X hX Q g x)
  rw [hOp_eq]
  set A := vfX (cLoc l τ) (zRe ε a b) P
  set B := vfX (cLoc l τ) (zIm ε a b) P
  have hA := phiS_of_mem τ fr (cLoc l τ) Ψ A (hmem A).1
  have hB := phiS_of_mem τ fr (cLoc l τ) Ψ B (hmem B).1
  have hAB := phiS_of_mem τ fr (cLoc l τ) Ψ (A + Complex.I • B) (hmem (A + Complex.I • B)).1
  have hsum : phiS θ τ fr (cLoc l τ) Ψ (A + Complex.I • B) =
      phiS θ τ fr (cLoc l τ) Ψ A + Complex.I • phiS θ τ fr (cLoc l τ) Ψ B := by
    rw [hA, hB, hAB]
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul]
    exact tens_add_smul τ fr (cLoc l τ) Ψ A B Complex.I
  have hfA : (phiS θ τ fr (cLoc l τ) Ψ A).1 ∈ fockA θ V n l s := by rw [hA]; exact (hmem A).2
  have hfB : (Complex.I • phiS θ τ fr (cLoc l τ) Ψ B).1 ∈ fockA θ V n l s := by
    rw [hB, Submodule.coe_smul]; exact (fockA θ V n l s).smul_mem _ (hmem B).2
  unfold thF
  rw [hsum, hL D n V ψ χ θ μ ω H l s ν _ _ (hstd _ hfA) (hstd _ hfB) hx.hr g, thetaInt_smul]
  have e1 := h0 _ (isUe_zRe ε a b) P
  have e2 := h0 _ (isUe_zIm ε a b) P
  unfold thF at e1 e2
  rw [e1, e2]
  ring

end PositivityTheory.Rg.Sw.Glob

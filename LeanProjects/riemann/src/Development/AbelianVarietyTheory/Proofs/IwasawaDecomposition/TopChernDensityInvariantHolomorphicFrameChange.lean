import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointChern

theorem charpolyRev_conj_of_mul_eq_one {R : Type*} [CommRing R] {r : Type*} [Fintype r] [DecidableEq r]
    (M P Q : Matrix r r R) (hQP : Q * P = 1) : (Q * M * P).charpolyRev = M.charpolyRev := by
  have hQP' : Q.map Polynomial.C * P.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  have e : (1 : Matrix r r (Polynomial R)) - (Polynomial.X : Polynomial R) • (Q * M * P).map Polynomial.C =
      Q.map Polynomial.C * (1 - (Polynomial.X : Polynomial R) • M.map Polynomial.C) * P.map Polynomial.C := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hQP',
      Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.charpolyRev, Matrix.charpolyRev, e, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
    ← Matrix.det_mul, hQP', Matrix.det_one, one_mul]

theorem curvPoly_eq_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) : curvPoly G v =
      ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) • (curv G v (coordVec a) (coordVec b)).map C := by
  ext i j
  simp [curvPoly, Matrix.sum_apply, mul_comm]

end GlobalTheory.PointChern

namespace GlobalTheory.PointChern

theorem gram_eq_changeFrame {r : Type} [Fintype r] (c : ℝ) (hc : 0 < c) (g K : Matrix r r ℂ) :
    (c : ℂ) • (g * K * gᴴ) = (((Real.sqrt c : ℝ) : ℂ) • gᵀ)ᵀ * K * (((Real.sqrt c : ℝ) : ℂ) • gᵀ)ᴴᵀ := by
  have h1 : ((((Real.sqrt c : ℝ) : ℂ) • gᵀ)ᴴᵀ) = ((Real.sqrt c : ℝ) : ℂ) • gᴴ := by
    ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have h2 : ((Real.sqrt c : ℝ) : ℂ) * ((Real.sqrt c : ℝ) : ℂ) = (c : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
  rw [h1, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, h2]

theorem chernTop_changeFrame : ∀ {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (G K g : ReciprocityTheory.L2DbarEstimates.V n → Mat m ℂ) (c : ι → ℝ) (v : ReciprocityTheory.L2DbarEstimates.V n), (∀ τ, 0 < c τ) → (∀ τ i j, AnalyticAt ℂ (fun w => g w τ i j) v) → (∀ τ, IsUnit (g v τ).det) → (∀ τ, MContDiffAt 2 (fun w => K w τ) v) → (∀ τ, IsUnit (K v τ).det) → (∀ᶠ w in 𝓝 v, ∀ τ, G w τ = (c τ : ℂ) • (g w τ * K w τ * (g w τ)ᴴ)) → chernTop R G v = chernTop R K v := by
  intro n ι m R G K g c v hc hg hgu hK hKu hG
  have key : ∀ τ, curvPoly (fun u => G u τ) v = ((((Real.sqrt (c τ) : ℝ) : ℂ) • (g v τ)ᵀ)⁻¹).map C *
      curvPoly (fun u => K u τ) v * ((((Real.sqrt (c τ) : ℝ) : ℂ) • (g v τ)ᵀ)).map C := by
    intro τ
    set A : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin (m τ)) (Fin (m τ)) ℂ :=
      fun u => ((Real.sqrt (c τ) : ℝ) : ℂ) • (g u τ)ᵀ with hAdef
    have hent : ∀ a b, (fun x => A x a b) = fun x => ((Real.sqrt (c τ) : ℝ) : ℂ) * g x τ b a := fun a b => rfl
    have hA : MContDiffAt 2 A v := fun a b => by
      rw [hent]
      exact contDiffAt_const.mul ((hg τ b a).contDiffAt.restrict_scalars ℝ)
    have hAu : IsUnit (A v).det := by
      simp only [hAdef, Matrix.det_smul, Matrix.det_transpose]
      refine IsUnit.mul (IsUnit.pow _ (Ne.isUnit ?_)) (hgu τ)
      exact_mod_cast (Real.sqrt_pos.2 (hc τ)).ne'
    have hA0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0 := by
      have hev : ∀ᶠ x in 𝓝 v, ∀ a b, AnalyticAt ℂ (fun w => g w τ b a) x :=
        eventually_all.2 fun a => eventually_all.2 fun b => (hg τ b a).eventually_analyticAt
      filter_upwards [hev] with x hx η
      ext a b
      rw [mdbar_apply, hent, GlobalTheory.dbar_eq_zero (((hx a b).differentiableAt).const_mul _)]
      rfl
    have hGe : (fun u => G u τ) =ᶠ[𝓝 v] fun u => (A u)ᵀ * K u τ * (A u)ᴴᵀ :=
      hG.mono fun u hu => by show G u τ = _; rw [hu τ]; exact gram_eq_changeFrame _ (hc τ) _ _
    have hcurv : ∀ ξ η, curv (fun u => G u τ) v ξ η = (A v)⁻¹ * curv (fun u => K u τ) v ξ η * A v :=
      fun ξ η => by rw [curv_congr hGe, curv_changeFrame (hK τ) (hKu τ) hA hAu hA0]
    clear_value A
    rw [curvPoly_eq_sum, curvPoly_eq_sum]
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul, hcurv]
    subst hAdef
    rfl
  have key2 : ∀ τ k, chernPoly (fun u => G u τ) v k = chernPoly (fun u => K u τ) v k := by
    intro τ k
    have hu : IsUnit (((Real.sqrt (c τ) : ℝ) : ℂ) • (g v τ)ᵀ).det := by
      simp only [Matrix.det_smul, Matrix.det_transpose]
      refine IsUnit.mul (IsUnit.pow _ (Ne.isUnit ?_)) (hgu τ)
      exact_mod_cast (Real.sqrt_pos.2 (hc τ)).ne'
    rw [chernPoly, chernPoly, key, show ∀ (Q M P : Matrix (Fin (m τ)) (Fin (m τ)) (MvPolynomial (Fin n × Fin n) ℂ)), -(Q * M * P) = Q * (-M) * P from fun Q M P => by rw [Matrix.mul_neg, Matrix.neg_mul], charpolyRev_conj_of_mul_eq_one]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  simp only [chernTop, key2]

end GlobalTheory.PointChern

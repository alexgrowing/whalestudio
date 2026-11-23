import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsHermitianDiagonalizationAtInfinitePlaceOfS
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.SpanRealMatrixMulVecInfinitePlaceEmbeddingEqTop
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.TraceConjDotProductEqSumInfinitePlaces
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ReMulSignatureIPosOfHermitianTraceFormula
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.FinrankArchimedeanEqTwoMulDim
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.archEx_of :
    UpperTheory.Gal.W2.FMat → UpperTheory.Gal.W2.FForm → UpperTheory.Gal.W2.SN → UpperTheory.Gal.W2.ArchSpan → UpperTheory.Gal.W2.ArchEx := by
  intro hFM hFF hSN hAS p _ D G L hm
  obtain ⟨kp, σ, hk⟩ := hFM p D G L hm
  obtain ⟨A, hdet, hskew, hform, hcomm⟩ := hFF p D G L kp σ hk
  choose S lam hS hpsi hconj hAv using fun v => UpperTheory.exists_hermitian_diagonalization_at_infinitePlace_of_skewHermitian p G σ A hSN hdet hskew hcomm v
  let th : VQ D →+ Arch G :=
    { toFun := fun w v => S v *ᵥ fun i => v.embedding (kp w i)
      map_zero' := by
        funext v
        simp
        exact Matrix.mulVec_zero _
      map_add' := fun x y => by
        funext v
        have : (fun i => v.embedding (kp (x + y) i)) = (fun i => v.embedding (kp x i)) + (fun i => v.embedding (kp y i)) := by
          funext i; simp
        simp only [this, Matrix.mulVec_add]
        rfl }
  have hth : ∀ w v, th w v = S v *ᵥ fun i => v.embedding (kp w i) := fun _ _ => rfl
  have hact : ∀ (c : G.C) w v, th (L.rep c w) v = G.psi v c *ᵥ th w v := by
    intro c w v
    rw [hth, hth, Matrix.mulVec_mulVec, hpsi, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    rw [hk c w]
    simp [Matrix.mulVec, dotProduct, map_sum]
  have hform' : ∀ u w, ((D.EF.baseChange ℚ u w : ℚ) : ℝ) = ∑ v, 2 * (lam v * hv (G.gram v) (th u v) (th w v)).re := by
    intro u w
    rw [hform u w]
    exact UpperTheory.trace_conj_dotProduct_eq_sum_infinitePlaces G.F G.n hAS A S G.gram lam hS hAv (kp u) (kp w)
  have hspan : Submodule.span ℝ (Set.range th) = ⊤ := by
    rw [← UpperTheory.span_real_matrix_mulVec_infinitePlace_embedding_eq_top G.F G.n hAS S hS]
    congr 1
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨kp w, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨kp.symm x, by funext v; simp [hth]⟩
  have hpos := UpperTheory.re_mul_signature_I_pos_of_hermitian_trace_formula p D G L th lam hact hform' hspan hconj
  obtain ⟨hd1, hd2⟩ := UpperTheory.finrank_archimedean_eq_two_mul_dim p D G L hm hAS
  have hs2 : ∀ v, sgnV L v * sgnV L v = 1 := by
    intro v
    unfold sgnV
    split_ifs <;> simp
  have hlamim : ∀ v, lam v = ((lam v * sgnV L v * Complex.I).re : ℂ) * (-(sgnV L v) * Complex.I) := by
    intro v
    have hre : (lam v).re = 0 := by
      have := congrArg Complex.re (hconj v)
      simp at this
      linarith
    have hreal : (lam v * sgnV L v * Complex.I).im = 0 := by
      unfold sgnV
      split_ifs <;> simp [hre]
    have hc : ((lam v * sgnV L v * Complex.I).re : ℂ) = lam v * sgnV L v * Complex.I := by
      apply Complex.ext <;> simp [hreal]
    rw [hc]
    have := hs2 v
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (lam v * Complex.I * Complex.I) * this + lam v * hI
  exact ⟨{
    th := th
    r := fun v => 2 * (lam v * sgnV L v * Complex.I).re
    r_pos := fun v => by have := hpos v; linarith
    act := hact
    form := by
      intro u w
      rw [hform' u w]
      refine Finset.sum_congr rfl fun v _ => ?_
      show 2 * (lam v * hv (G.gram v) (th u v) (th w v)).re = 2 * (lam v * sgnV L v * Complex.I).re * (-(sgnV L v) * Complex.I * hv (G.gram v) (th u v) (th w v)).re
      conv_lhs => rw [hlamim v, mul_assoc ((lam v * sgnV L v * Complex.I).re : ℂ), Complex.re_ofReal_mul]
      ring
    span := hspan
    dim := hd1
    dimg := hd2 }⟩

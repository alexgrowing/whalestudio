import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

private theorem off_diag_zero {E : Type} [NormedField E] {n : ℕ} (k : Matrix (Fin n) (Fin n) E)
    (hk : ∀ y : Fin n → E, euclidNorm (y ᵥ* k) = euclidNorm y) {i j : Fin n} (hii : k i i = 1) (hij : i ≠ j) :
    k i j = 0 := by
  have hrow : (Pi.single i 1 : Fin n → E) ᵥ* k = k i := by
    funext l
    simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  have h1 := hk (Pi.single i 1)
  rw [hrow] at h1
  have hs : ∑ l, ‖(Pi.single i 1 : Fin n → E) l‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · simp
  have h2 : ∑ l, ‖k i l‖ ^ 2 = 1 := by
    have := congrArg (· ^ 2) h1
    simp only [euclidNorm] at this
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), hs] at this
    exact this
  have h3 : ‖k i i‖ ^ 2 + ‖k i j‖ ^ 2 ≤ ∑ l, ‖k i l‖ ^ 2 := by
    rw [← Finset.sum_pair (f := fun l => ‖k i l‖ ^ 2) hij]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  rw [h2, hii, norm_one] at h3
  have h4 : ‖k i j‖ ^ 2 ≤ 0 := by linarith
  have h5 : ‖k i j‖ = 0 := by
    have := sq_nonneg ‖k i j‖
    exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h4 this)
  exact norm_eq_zero.1 h5

theorem UpperTheory.unipotent_mem_maximalCompact_finite_integral :
    ∀ {K : Type} [Field K] [NumberField K] (X : UPos (2 + 2) 2 → NumberField.AdeleRing (𝓞 K) K), nn X ∈ KG K (2 + 2) → ∃ h : AdelicGLn.integralFiniteGL K (2 + 2), nn X = fin1 (h : FA K (2 + 2)) := by
  intro K _ _ X hX
  have hK : ((nn X : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ∈
      (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))) := hX
  obtain ⟨hinf, hfin⟩ := hK
  have hent : ∀ a b, ((nn X : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) a b = unipMatrix X a b := fun _ _ => rfl
  have hz : ∀ (p : UPos (2 + 2) 2) (w : InfinitePlace K), (X p).1 w = 0 := by
    intro p w
    have hne : p.1.1 ≠ p.1.2 := by
      intro h
      have := p.2
      rw [h] at this
      omega
    have hii : ((infAt w ((nn X : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) : GL (Fin (2 + 2)) w.Completion) :
        Matrix (Fin (2 + 2)) (Fin (2 + 2)) w.Completion) p.1.1 p.1.1 = 1 := by
      have hp := p.2.1
      change (((nn X : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) p.1.1 p.1.1).1 w = 1
      rw [hent, unipMatrix, Matrix.add_apply, blockEntry_apply, dif_neg (by omega)]
      simp
    have h0 := off_diag_zero _ (hinf w) hii hne
    change (((nn X : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) p.1.1 p.1.2).1 w = 0 at h0
    rw [hent, unipMatrix, Matrix.add_apply, blockEntry_apply, dif_pos p.2, Matrix.one_apply_ne hne, zero_add] at h0
    exact h0
  set g : AdelicGLn.AdelicGL K (2 + 2) := ((nn X : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) with hg
  have h1 : (AdelicGLn.prodEquiv K (2 + 2) g).1 = 1 := by
    apply Units.ext
    refine Matrix.ext fun a b => ?_
    change (g a b).1 = (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) (InfiniteAdeleRing K)) a b
    rw [hent, unipMatrix, Matrix.add_apply, blockEntry_apply]
    by_cases hab : a = b
    · subst hab
      rw [dif_neg (by omega), Matrix.one_apply_eq, Matrix.one_apply_eq, add_zero]
      rfl
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab]
      split_ifs with h
      · have hw : (X ⟨(a, b), h⟩).1 = 0 := funext fun w => hz _ w
        simp [hw]
      · simp
  have hint : (AdelicGLn.prodEquiv K (2 + 2) g).2 ∈ AdelicGLn.integralFiniteGL K (2 + 2) :=
    (AdelicGLn.mem_integralFiniteGL_iff_forall K (2 + 2)).2 hfin
  have hgf : finEmb K (2 + 2) (AdelicGLn.prodEquiv K (2 + 2) g).2 = g := by
    have := infEmb_mul_finEmb g
    rwa [h1, map_one, map_one, one_mul] at this
  refine ⟨⟨_, hint⟩, ?_⟩
  have hmem : finEmb K (2 + 2) (AdelicGLn.prodEquiv K (2 + 2) g).2 ∈ normOneGL K (2 + 2) := by
    rw [hgf]
    exact (nn X).2
  apply Subtype.ext
  change g = ((MultiplicityOne.finProj K (2 + 2) (AdelicGLn.prodEquiv K (2 + 2) g).2 : normOneGL K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2))
  rw [MultiplicityOne.finProj_of_mem hmem]
  exact hgf.symm

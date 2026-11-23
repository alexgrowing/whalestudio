import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PnormInvStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst

open NumberField ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem normFactor_rightBorel_holds : NfacRmulStatement (E := E) := by
  unfold NfacRmulStatement
  intro r X la x hx b hb
  have key : ∀ (τ : X.Ψ) (i : Fin r),
      ‖dmin X.Gm (rmul x b) τ i.succ / dmin X.Gm (rmul x b) τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)
        = (‖b τ i i‖ ^ la τ i)⁻¹ *
          ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := by
    intro τ i
    have ht : 0 < ‖b τ i i‖ := norm_pos_iff.mpr (FrameDegreeData.bdiag_ne (X := X) hb τ i)
    rw [FrameDegreeData.ratio_rmul (X := X) x hx hb τ i, eq_inv_mul_iff_mul_eq₀ (zpow_ne_zero _ ht.ne')]
    exact FrameDegreeData.factor_eq _ _ ht (norm_nonneg _) (la τ i)
  have hbc : ‖bchar la b‖ = ∏ τ, ∏ i, ‖b τ i i‖ ^ la τ i := by
    simp only [bchar, norm_prod, norm_zpow]
  simp only [Data.nfac, key, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hbc]

private theorem ringHom_cc_eq_conj (τ : E →+* ℂ) (y : E) : τ (cc y) = starRingEnd ℂ (τ y) :=
  NumberField.IsCMField.complexEmbedding_complexConj E τ y

private theorem sum_mul_gram_mul_cc_of_isUStab {r : ℕ} (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E) (hγ : IsUStab G Λ γ) (j l : Fin r) :
    ∑ a, ∑ b, (γ : Matrix (Fin r) (Fin r) E) a j * G a b * cc ((γ : Matrix (Fin r) (Fin r) E) b l)
      = G j l := by
  have hs : ∀ k : Fin r, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (Pi.single k 1)
      = fun a => (γ : Matrix (Fin r) (Fin r) E) a k := by
    intro k
    funext a
    change ∑ c, (γ : Matrix (Fin r) (Fin r) E) a c * (Pi.single k (1 : E) : Fin r → E) c = _
    simp [Pi.single_apply]
  have h := hγ.1 (Pi.single j 1) (Pi.single l 1)
  rw [hs j, hs l] at h
  have hc : ∀ c : Fin r, cc ((Pi.single l (1 : E) : Fin r → E) c) = (Pi.single l (1 : E) : Fin r → E) c := by
    intro c
    by_cases hcl : c = l
    · subst hcl
      simp [cc]
    · simp [cc, hcl]
  change herm G (fun a => (γ : Matrix (Fin r) (Fin r) E) a j)
    (fun a => (γ : Matrix (Fin r) (Fin r) E) a l) = G j l
  rw [h]
  simp only [herm, hc]
  simp [Pi.single_apply]

private theorem sum_four_comm_arakelov_instances {ι : Type*} [Fintype ι] (F : ι → ι → ι → ι → ℂ) :
    ∑ a, ∑ b, ∑ j, ∑ l, F a b j l = ∑ j, ∑ l, ∑ a, ∑ b, F a b j l := by
  calc ∑ a, ∑ b, ∑ j, ∑ l, F a b j l = ∑ a, ∑ j, ∑ b, ∑ l, F a b j l :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ l, ∑ b, F a b j l :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ l, ∑ b, F a b j l := Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ a, ∑ b, F a b j l := Finset.sum_congr rfl fun j _ => Finset.sum_comm

private theorem hermC_mulVec_map_of_isUStab {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E) (hγ : IsUStab G Λ γ)
    (u v : Fin r → ℂ) :
    hermC τ G (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ) u)
        (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ) v) = hermC τ G u v := by
  have key : ∀ j l : Fin r, ∑ a, ∑ b, τ ((γ : Matrix (Fin r) (Fin r) E) a j) * τ (G a b) *
      starRingEnd ℂ (τ ((γ : Matrix (Fin r) (Fin r) E) b l)) = τ (G j l) := by
    intro j l
    rw [← sum_mul_gram_mul_cc_of_isUStab G Λ γ hγ j l]
    simp only [map_sum, map_mul, ringHom_cc_eq_conj]
  have hmv : ∀ (M : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) (i : Fin r),
      Matrix.mulVec M w i = ∑ j, M i j * w j := fun _ _ _ => rfl
  have lhs : hermC τ G (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ) u)
        (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ) v)
      = ∑ a, ∑ b, ∑ j, ∑ l, u j * (τ ((γ : Matrix (Fin r) (Fin r) E) a j) * τ (G a b) *
          starRingEnd ℂ (τ ((γ : Matrix (Fin r) (Fin r) E) b l))) * starRingEnd ℂ (v l) := by
    simp only [hermC, hmv, Matrix.map_apply, map_sum, map_mul]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have rhs : hermC τ G u v = ∑ j, ∑ l, ∑ a, ∑ b, u j * (τ ((γ : Matrix (Fin r) (Fin r) E) a j) *
      τ (G a b) * starRingEnd ℂ (τ ((γ : Matrix (Fin r) (Fin r) E) b l))) * starRingEnd ℂ (v l) := by
    simp only [hermC]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← key j l]
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [lhs, rhs]
  exact sum_four_comm_arakelov_instances (fun a b j l => u j * (τ ((γ : Matrix (Fin r) (Fin r) E) a j) * τ (G a b) *
      starRingEnd ℂ (τ ((γ : Matrix (Fin r) (Fin r) E) b l))) * starRingEnd ℂ (v l))

private theorem gram_map_mul_of_isUStab' {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E) (hγ : IsUStab G Λ γ)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G ((γ : Matrix (Fin r) (Fin r) E).map τ * M) = gram τ G M := by
  have hcol : ∀ a, col ((γ : Matrix (Fin r) (Fin r) E).map τ * M) a
      = Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ) (col M a) := fun _ => rfl
  ext a b
  simp only [gram, Matrix.of_apply, hcol, hermC_mulVec_map_of_isUStab τ G Λ γ hγ]

private theorem dmin_lact_of_mem_Γ {r : ℕ} (X : Data E r) (γ : GL (Fin r) E) (hγ : γ ∈ X.Γ)
    (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (lact γ x) τ i = dmin X.Gm x τ i := by
  have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  simp only [dmin, hm, gram_map_mul_of_isUStab' τ.1 X.Gm X.Λ γ (X.Γ_stab γ hγ)]

theorem normFactor_leftAction_holds : NfacLactStatement (E := E) := by
  unfold NfacLactStatement
  intro r X la γ hγ x hx
  simp only [Data.nfac, dmin_lact_of_mem_Γ X γ hγ]

theorem pointwiseNorm_invariance_holds : PnormInvStatement (E := E) := by
  unfold PnormInvStatement
  intro r X la P hP γ hγ x hx b hb
  obtain ⟨-, hPr, hPl⟩ := hP
  have hlx : lact γ x ∈ X.dom := by
    refine fun τ => ⟨?_, fun i => ?_⟩
    · have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
      have hd : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det :=
        (RingHom.map_det τ.1 _).symm
      rw [hm, Matrix.det_mul, hd]
      exact mul_ne_zero ((map_ne_zero τ.1).mpr
        ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit γ)).ne_zero) (hx τ).1
    · rw [dmin_lact_of_mem_Γ X γ hγ]
      exact (hx τ).2 i
  have hcomm : lact γ (rmul x b) = rmul (lact γ x) b := by
    funext τ
    show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) : Matrix (Fin r) (Fin r) ℂ)
      = ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) * mat b τ
    exact (Matrix.mul_assoc _ _ _).symm
  have hN : ∀ y : Frame X.Ψ r, X.pnorm la P y = ‖P y‖ * X.nfac la y := fun _ => rfl
  obtain ⟨n, hn, hpow⟩ := X.χ_fin la
  have h1 : ‖X.χ la γ‖ ^ n = 1 := by rw [← norm_pow, hpow γ hγ, norm_one]
  have hχ : ‖X.χ la γ‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h1
  rw [hcomm, FrameDegreeData.pnorm_rmul (X := X) la P hPr (lact γ x) hlx b hb, hN, hN, hPl γ hγ x hx,
    normFactor_leftAction_holds r X la γ hγ x hx, norm_mul, hχ, one_mul]

end

end ReciprocityTheory.ChartRestriction.G.AR.Inst

import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.AbsTaylor
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.LiftSingle
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.SubEqZeroIff

open NumberField MvPolynomial PositivityTheory.Rg.Fx

private theorem vars_pieceK {ι κ : Type} [Fintype ι] (k : ℕ) (F : KF ι κ) : ∀ j ∈ (pieceK k F).vars, j ∈ F.vars := by
  classical
  intro j hj
  rw [mem_vars_iff_mem_support] at hj ⊢
  obtain ⟨d, hd, hjd⟩ := hj
  refine ⟨d, ?_, hjd⟩
  by_contra hn
  apply mem_support_iff.mp hd
  unfold pieceK
  rw [coeff_sum]
  refine Finset.sum_eq_zero fun β hβ => ?_
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact hn hβ

private theorem congr_mod {σ κ A : Type} [CommRing A] [Algebra ℂ A] (J : Ideal A) (Z X : σ → A) (e : σ → MvPolynomial σ ℂ)
    (H H' : κ → A) (G P : MvPolynomial κ (MvPolynomial σ ℂ)) (hZ : ∀ p, Z p - aeval X (e p) ∈ J)
    (hH : ∀ k ∈ P.vars, H k - H' k ∈ J)
    (hG : map (aeval e : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ).toRingHom G = P) :
    eval₂ (aeval Z).toRingHom H G - eval₂ (aeval X).toRingHom H' P ∈ J := by
  rw [← Ideal.Quotient.eq]
  have h1 : (Ideal.Quotient.mkₐ ℂ J).comp (aeval Z) = ((Ideal.Quotient.mkₐ ℂ J).comp (aeval X)).comp (aeval e) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq.mpr (hZ p)
  have h2 : (Ideal.Quotient.mk J).comp (aeval Z).toRingHom =
      ((Ideal.Quotient.mk J).comp (aeval X).toRingHom).comp
        (aeval e : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ).toRingHom :=
    RingHom.ext fun p => DFunLike.congr_fun h1 p
  rw [eval₂_comp_left, eval₂_comp_left, h2, ← eval₂_map, hG]
  refine eval₂Hom_congr' rfl (fun j hj _ => ?_) rfl
  exact Ideal.Quotient.eq.mpr (hH j hj)

theorem UpperTheory.ConvolutionTheory.BW.absKill :
    UpperTheory.ConvolutionTheory.BW.AbsKill := by
  intro τ κ A V _ _ n r _ _ _ _ _ _ Z H I t c idx Λ h good C hS F G hgood hev hG φ x
  classical
  obtain ⟨τ₀⟩ := ‹Nonempty τ›
  choose s hs using hS.surj
  let b : Fam (τ × Fin n) κ :=
    { r := r
      Λ := Λ
      emb := Matrix.of fun p j => if idx p.2 = j then 1 else 0
      pr := Matrix.of fun j p => if p = (τ₀, s j) then 1 else 0
      pr_emb := by
        ext i j
        rw [Matrix.mul_apply, Finset.sum_eq_single (τ₀, s i) (fun p _ hp => by simp [hp]) (by simp)]
        simp [hs, Matrix.one_apply]
      h := h }
  have hsub : b.sub F = 0 := by
    rw [UpperTheory.ConvolutionTheory.FX.sub_eq_zero_iff]
    rintro Λ' h' ⟨z, h1, h2⟩
    have e1 : Λ' = fun p => Λ p + z (idx p.2) := by
      funext p
      rw [h1]
      simp [b, apply_ite ((↑) : ℝ → ℂ)]
    have e2 : h' = fun k => ev z (h k) := funext h2
    rw [e1, e2]
    exact hev z
  have key := UpperTheory.ConvolutionTheory.FX.rearrange (τ × Fin n) κ b A V I t ((LinearMap.proj x).comp c)
    (fun v m => UpperTheory.ConvolutionTheory.FX.abs_taylor τ κ A V n r Z H I t c idx Λ h good C hS v x m) F φ
  rw [hsub, map_zero, zero_smul, map_zero] at key
  let J : Ideal A :=
    { carrier := {a | ∀ ψ, c (a • ψ) = 0}
      add_mem' := fun {a a'} ha ha' ψ => by rw [add_smul, map_add, ha, ha', add_zero]
      zero_mem' := fun ψ => by rw [zero_smul, map_zero]
      smul_mem' := fun a a' ha ψ => by rw [smul_eq_mul, mul_comm, mul_smul]; exact ha _ }
  have hJ : ∀ a a' : A, a - a' ∈ J ↔ ∀ ψ, c (a • ψ) = c (a' • ψ) := fun a a' =>
    forall_congr' fun ψ => by rw [sub_smul, map_sub, sub_eq_zero]
  have hX : (fun i : τ × Fin n => algebraMap ℂ A (b.Λ i) + ∑ j, (b.emb i j : ℂ) • I j) =
      fun q => algebraMap ℂ A (Λ q) + I (idx q.2) := by
    funext p
    simp [b, apply_ite ((↑) : ℝ → ℂ)]
  rw [hX] at key
  convert key using 2 with k
  have := congr_mod J Z (fun q => algebraMap ℂ A (Λ q) + I (idx q.2)) blockE H (fun k' => lift I t (h k')) (G k)
    (pieceK k F) (fun p => (hJ _ _).mpr (hS.cen p))
    (fun j hj => (hJ _ _).mpr (hS.hecke j (hgood j (vars_pieceK k F j hj)))) (hG k)
  exact congrFun ((hJ _ _).mp this φ) x

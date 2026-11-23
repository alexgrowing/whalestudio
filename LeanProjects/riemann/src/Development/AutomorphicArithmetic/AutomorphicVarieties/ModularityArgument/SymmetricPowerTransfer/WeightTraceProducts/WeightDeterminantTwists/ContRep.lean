import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.FinMH

open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem cont_m {K T : Type} [Fintype K] [TopologicalSpace T] {d : ℕ} (n : K → ℕ) (γ : T → K → GL (Fin d) ℂ)
    (hγ : ∀ k i j, Continuous fun t => (γ t k : Matrix (Fin d) (Fin d) ℂ) i j) (x : MH d n) (f : MH d n →ₗ[ℂ] ℂ) :
    Continuous fun t => f (mRep d n (γ t) x) := by
  haveI : FiniteDimensional ℂ (MH d n) := finMH K d n
  let W : Submodule ℂ (Module.Dual ℂ (MH d n)) :=
    { carrier := {φ | Continuous fun t => φ (mRep d n (γ t) x)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, LinearMap.add_apply] at *
        exact ha.add hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, LinearMap.zero_apply]
        exact continuous_const
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq, LinearMap.smul_apply, smul_eq_mul] at *
        exact continuous_const.mul ha }
  have hev : ∀ y : K × Fin d → ℂ,
      (MvPolynomial.aeval y : MvPolynomial (K × Fin d) ℂ →ₐ[ℂ] ℂ).toLinearMap.comp (MH d n).subtype ∈ W := by
    intro y
    have hc : Continuous fun t => MvPolynomial.eval y ((mRep d n (γ t) x : MH d n) : MvPolynomial (K × Fin d) ℂ) := by
      simp only [eval_mRep]
      refine (MvPolynomial.continuous_eval (x : MvPolynomial (K × Fin d) ℂ)).comp ?_
      refine continuous_pi fun p => ?_
      exact continuous_finset_sum _ fun j _ => continuous_const.mul (hγ p.1 j p.2)
    show Continuous fun t => (MvPolynomial.aeval y) ((mRep d n (γ t) x : MH d n) : MvPolynomial (K × Fin d) ℂ)
    convert hc using 2 with t
    exact DFunLike.congr_fun (MvPolynomial.coe_aeval_eq_eval y) _
  have hb : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    rw [Submodule.mem_bot]
    apply Subtype.ext
    apply MvPolynomial.funext
    intro y
    have := hv _ (hev y)
    have e : (MvPolynomial.aeval y) (v : MvPolynomial (K × Fin d) ℂ) = MvPolynomial.eval y (v : MvPolynomial (K × Fin d) ℂ) :=
      DFunLike.congr_fun (MvPolynomial.coe_aeval_eq_eval y) _
    rw [Submodule.coe_zero, map_zero, ← e]
    exact this
  have htop : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hb, Submodule.dualAnnihilator_bot]
  have hf : f ∈ W := htop ▸ Submodule.mem_top
  exact hf

theorem UpperTheory.V.Z.Sym.Wt.contRep :
    UpperTheory.V.Z.Sym.Wt.ContRep := by
  intro I _
  classical
  have entc : ∀ (d : ℕ) (k : I) (i j : Fin d),
      Continuous fun g : I → GL (Fin d) ℂ => ((g k : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) i j := by
    intro d k i j
    exact ((Units.continuous_val (M := Matrix (Fin d) (Fin d) ℂ)).comp (continuous_apply k)).matrix_elem i j
  have entci : ∀ (d : ℕ) (k : I) (i j : Fin d),
      Continuous fun g : I → GL (Fin d) ℂ => (((g k)⁻¹ : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) i j := by
    intro d k i j
    exact ((Units.continuous_coe_inv (M := Matrix (Fin d) (Fin d) ℂ)).comp (continuous_apply k)).matrix_elem i j
  refine ⟨fun j x f => ?_, fun n e x f => ?_⟩
  · have hsplit : (fun g => f (repG I j g x)) = fun g => ∑ S, f (Pi.single S (repG I j g x S)) := by
      funext g
      rw [← map_sum, Finset.univ_sum_single]
    rw [hsplit]
    refine continuous_finset_sum _ fun S _ => ?_
    have hent : ∀ (k : I × Bool) (i i' : Fin 3),
        Continuous fun g : I → GL (Fin 3) ℂ => ((dbl 3 g k : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i i' := by
      intro k i i'
      have hfun : (fun g : I → GL (Fin 3) ℂ => ((dbl 3 g k : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i i') =
          fun g => if k.2 = true then (((g k.1)⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i' i
            else ((g k.1 : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i i' := by
        funext g
        simp only [dbl, MonoidHom.coe_mk, OneHom.coe_mk]
        split_ifs <;> rfl
      rw [hfun]
      by_cases hk : k.2 = true
      · simp only [hk, if_true]
        exact entci 3 k.1 i' i
      · simp only [if_neg hk]
        exact entc 3 k.1 i i'
    exact cont_m (fun k : I × Bool => dg j S k.1) (fun g : I → GL (Fin 3) ℂ => dbl 3 g) hent (x S)
      (f ∘ₗ LinearMap.single ℂ (fun S => ↥(Bi 3 (dg j S))) S)
  · have hdet : ∀ v : I, Continuous fun g : I → GL (Fin 2) ℂ => Matrix.GeneralLinearGroup.det (g v) := by
      intro v
      refine Units.continuous_iff.mpr ⟨?_, ?_⟩
      · show Continuous fun g : I → GL (Fin 2) ℂ => ((Matrix.GeneralLinearGroup.det (g v) : ℂˣ) : ℂ)
        simp only [Matrix.GeneralLinearGroup.val_det_apply]
        exact ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℂ)).comp (continuous_apply v)).matrix_det
      · have h : ∀ g : I → GL (Fin 2) ℂ,
            (((Matrix.GeneralLinearGroup.det (g v))⁻¹ : ℂˣ) : ℂ) = (((g v)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det := by
          intro g
          rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
        simp only [h]
        exact ((Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) ℂ)).comp (continuous_apply v)).matrix_det
    have hd : Continuous fun g : I → GL (Fin 2) ℂ => detE 2 e g := by
      show Continuous fun g : I → GL (Fin 2) ℂ => ∏ v, Matrix.GeneralLinearGroup.det (g v) ^ e
      exact continuous_finset_prod _ fun v _ => (hdet v).zpow e
    simp only [repD_apply, LinearMap.smul_apply, map_smul, smul_eq_mul]
    exact (Units.continuous_val.comp hd).mul
      (cont_m (fun _ : I => n) (fun g : I → GL (Fin 2) ℂ => g) (fun k i j => entc 2 k i j) x f)

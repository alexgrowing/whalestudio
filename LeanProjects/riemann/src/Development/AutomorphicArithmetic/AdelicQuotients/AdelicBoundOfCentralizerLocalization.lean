import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal Topology
open scoped NumberField.AdeleRing

noncomputable section

namespace UpperTheory.Bnd

variable (E : Type) [Field E] [NumberField E] (n : ℕ)

private def emb : GL (Fin n) (InfiniteAdeleRing E) →* GA E n where
  toFun x := (AdelicGLn.prodEquiv E n).symm (x, 1)
  map_one' := map_one (AdelicGLn.prodEquiv E n).symm
  map_mul' x y := by
    rw [← map_mul (AdelicGLn.prodEquiv E n).symm]
    simp

private theorem emb_apply (x : GL (Fin n) (InfiniteAdeleRing E)) :
    emb E n x = (AdelicGLn.prodEquiv E n).symm (x, 1) := rfl

private theorem continuous_emb : Continuous (emb E n) :=
  (AdelicGLn.prodEquiv E n).symm.continuous.comp (continuous_id.prodMk continuous_const)

private theorem prod_emb (x : GL (Fin n) (InfiniteAdeleRing E)) :
    AdelicGLn.prodEquiv E n (emb E n x) = (x, 1) := by
  rw [emb_apply]; exact (AdelicGLn.prodEquiv E n).apply_symm_apply _

private theorem pI_emb (x : GL (Fin n) (InfiniteAdeleRing E)) : pI E n (emb E n x) = x := by
  refine Units.ext ?_
  ext a b
  have h := AdelicGLn.prodEquiv_apply_fst E n (emb E n x) a b
  rw [prod_emb] at h
  exact h.symm

private theorem pE_emb {F : Type} [Field F] [NumberField F] [Algebra F E] (v : Pl F)
    (x : GL (Fin n) (InfiniteAdeleRing E)) : pE E n v (emb E n x) = 1 := by
  refine Units.ext (Matrix.ext fun a b => funext fun w => ?_)
  have h := AdelicGLn.prodEquiv_apply_snd E n (emb E n x) a b
  rw [prod_emb] at h
  change (((emb E n x : GL _ _) a b).2 : FiniteAdeleRing (𝓞 E) E) w.1 = _
  rw [← h]
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> rfl

end UpperTheory.Bnd

open UpperTheory.Bnd in
theorem UpperTheory.adelicBound_of_centralizer_localization :
    N5 → Compat → CentLoc → RPE → BoundE := by
  intro hN hC hCL hR F E _ _ _ _ _ _ σ hσ n hn δ D hD
  have hRP := hR F E n
  obtain ⟨hC1, hC2, -⟩ := hC F E σ n

  have hz : ∀ s : ℝ, emb E n (pI E n (zA E n s)) = zA E n s := fun s =>
    hRP.ext _ _ (pI_emb E n _) fun v => by
      rw [pE_emb E n v]
      exact ((hCL E n ⟨Real.exp s, Real.exp_pos s⟩).2.2.2 F v).symm

  have hg : ∀ x, emb E n (mapGL n (galInf σ) x) = mapGL n (galAd σ) (emb E n x) := fun x =>
    hRP.ext _ _ (by rw [pI_emb, hC1, pI_emb]) fun v => by
      rw [pE_emb E n v, hC2, pE_emb E n v, map_one]
  have hm := (hN F E σ hσ n hn).2.2
  set d : GL (Fin n) (InfiniteAdeleRing E) →* {r : ℝ // 0 < r} := (detModule E n).comp (emb E n) with hd
  have hdc : Continuous fun y => (d y : ℝ) :=
    continuous_subtype_val.comp (continuous_detModule.comp (continuous_emb E n))
  have hdz : ∀ s : ℝ, (d (pI E n (zA E n s)) : ℝ) = Real.exp s := fun s => by
    simp only [hd, MonoidHom.comp_apply, hz]
    rw [zA, detModule_centralSection hn]
  have hds : ∀ x, d (mapGL n (galInf σ) x) = d x := fun x => by
    simp only [hd, MonoidHom.comp_apply, hg, hm]
  have hp : ∀ y, (d y : ℝ) ≠ 0 := fun y => (d y).2.ne'
  have hcont : Continuous fun y => Real.log ((d y : ℝ) / (d δ : ℝ)) :=
    (hdc.div_const _).log fun y => div_ne_zero (hp y) (hp δ)
  refine ⟨(fun y => Real.log ((d y : ℝ) / (d δ : ℝ))) '' D, hD.image hcont, fun s x hx => ⟨_, hx, ?_⟩⟩
  have e : d (pI E n (zA E n s) * (x⁻¹ * δ * mapGL n (galInf σ) x)) = d (pI E n (zA E n s)) * d δ := by
    rw [map_mul, map_mul, map_mul, hds, map_inv]
    congr 1
    rw [mul_comm (d x)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  change Real.log ((d _ : ℝ) / (d δ : ℝ)) = s
  rw [e, Positive.val_mul, hdz, mul_div_cancel_right₀ _ (hp δ), Real.log_exp]

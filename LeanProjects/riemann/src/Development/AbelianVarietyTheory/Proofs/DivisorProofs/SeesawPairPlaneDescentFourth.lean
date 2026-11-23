import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedEvaluationNonvanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpSumCoeffEqZeroOfVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewSpaceRealEmbeddingStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKReindex

open GlobalTheory.ThK.UnipDom.Inverse GlobalTheory.ThK.IsoZero

theorem rho_comm {R : Type} [CommRing R] [Invertible (2 : R)] {V : Type} [AddCommGroup V] [Module R V]
    {Bf : V → V → R} {κ : Type} [Fintype κ] (d : Darboux Bf κ) (ψ : AddChar R ℂ) (u v : V)
    (φ : (κ → R) → ℂ) :
    d.rho ψ u (d.rho ψ v φ) = ψ (Bf u v) • d.rho ψ v (d.rho ψ u φ) := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, d.form]
  set a := (d.e u).1
  set b := (d.e u).2
  set a' := (d.e v).1
  set b' := (d.e v).2
  have h1 : x + a + a' = x + a' + a := by abel
  rw [h1, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
    ← AddChar.map_add_eq_mul]
  congr 2
  simp only [add_dotProduct]
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem thetaSum_smul {κ : Type} (c : ℂ) (Φ : (κ → AF F) → ℂ) : thetaSum F (c • Φ) = c * thetaSum F Φ := by
  unfold thetaSum
  simp only [Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

theorem thetaSum_om_rat (hKP : KP) {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s')
    (γ : UA σ W.J) (hγ : γ ∈ ratU σ W.J) (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    thetaSum F (om (1, γ) Φ) = thetaSum F Φ := by
  have h := ((GlobalTheory.ThKBasic.thetaBasic hKP.base F E σ B n d X W M χX χW om r s r' s' hP).1 Φ hΦ).2.1
    1 (one_mem _) γ hγ 1 1
  simp only [mul_one, theta] at h
  rw [h]
  have h1 : ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 := rfl
  rw [h1, map_one]
  rfl

theorem term_rho {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (hstd : IsStd B.ψ) (ι : Matrix (Fin n) (Fin n₁) E)
    (ι' : Matrix (Fin d) (Fin d₁) E) (x y : Fin n → E) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (he : IsEv B M M₁ ι ι' {u | ∃ z, u = Matrix.vecMulVec (incV F x) z} e)
    (a z : Fin d → AE F E) (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F y) a) (M.co.rho B.ψ (Matrix.vecMulVec (incV F x) z) Φ))) =
      B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (Matrix.vecMulVec (incV F y) a)
        (Matrix.vecMulVec (incV F x) z)) *
      thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F y) a) Φ)) := by
  rw [rho_comm M.co B.ψ, map_smul, he.inv _ ⟨z, rfl⟩ _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd _ Φ hΦ),
    thetaSum_smul]

theorem mat_mulVec_incV {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (γ : UA σ J) (g : GL (Fin d) E)
    (hg : Matrix.GeneralLinearGroup.map (n := Fin d) (inclR (F := F) (E := E) (AF F)) g = (γ : GL (Fin d) (AE F E)))
    (w : Fin d → E) : mat γ *ᵥ incV F w = incV F ((g : Matrix (Fin d) (Fin d) E) *ᵥ w) := by
  have hm : mat γ = (g : Matrix (Fin d) (Fin d) E).map (inclR (F := F) (AF F)) := by
    show (γ : GL (Fin d) (AE F E)).1 = _
    rw [← hg]; rfl
  rw [hm]
  funext i
  simp only [incV]
  exact ((inclR (F := F) (AF F)).map_mulVec (g : Matrix (Fin d) (Fin d) E) w i).symm

theorem term_reindex : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ γ ∈ ratU σ W.J, ∀ w w' : Fin d → E, mat γ *ᵥ incV F w = incV F w' → ∀ Ψ ∈ schA F (Fin n × Fin d),
      thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w')) (om (1, γ) Ψ))) = thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (Ψ))) := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he
    γ hγ w w' hww' Ψ hΨ
  obtain ⟨C₀, hC₀, hexp⟩ := GlobalTheory.T.seesaw_pair_plane_dimension hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH
    V₁ M₁ e hV₁ hM₁ he
  obtain ⟨N, emb, lam, hinj, hfreq⟩ :=
    GlobalTheory.T.skew_space_real_embedding F E σ B n d X W r s r' s' hP.base hP.herm hP.skew H.x H.y hH.2.2.2.1
  have hstd : IsStd B.ψ := hP.base.std
  have hsch : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ u Φ ∈ schA F (Fin n × Fin d) :=
    fun u Φ hΦ => GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd u Φ hΦ
  have hS := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.mp hγ
  have hmv : ∀ v : Fin d → E, mat γ *ᵥ incV F v = incV F ((g : Matrix (Fin d) (Fin d) E) *ᵥ v) :=
    mat_mulVec_incV γ g hg
  let eg : (Fin d → E) ≃ (Fin d → E) :=
    { toFun := fun v => (g : Matrix (Fin d) (Fin d) E) *ᵥ v
      invFun := fun v => ((g⁻¹ : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v
      left_inv := fun v => by
        simp only [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
      right_inv := fun v => by
        simp only [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] }
  have heg : ∀ v, eg v = (g : Matrix (Fin d) (Fin d) E) *ᵥ v := fun v => rfl
  let ℓ : (Fin d → E) → Fn F n d → ℂ := fun v Φ =>
    thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F v)) Φ))
  have hΨ₁ : om (1, γ) Ψ ∈ schA F (Fin n × Fin d) := hS.pres _ Ψ hΨ
  have hc : ∀ v t, B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
      (Matrix.vecMulVec (incV F H.y) (incV F v)) (Matrix.vecMulVec (incV F H.x) (emb t))) =
      GlobalTheory.ExpSumUniq.chr (lam v) t := hfreq
  have hcn : ∀ v t, ‖GlobalTheory.ExpSumUniq.chr (lam v) t‖ = 1 := fun v t => GlobalTheory.ExpSumUniq.norm_chr _ _
  have hexpz : ∀ Φ ∈ schA F (Fin n × Fin d), ∀ t,
      thetaSum F (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (emb t)) Φ) =
        C₀ * ∑' v, GlobalTheory.ExpSumUniq.chr (lam v) t * ℓ v Φ := by
    intro Φ hΦ t
    rw [(hexp _ (hsch _ Φ hΦ)).2]
    congr 1
    refine tsum_congr fun v => ?_
    rw [term_rho M M₁ hstd H.ι 1 H.x H.y e he (incV F v) (emb t) Φ hΦ, hc]
  have hinvz : ∀ t, thetaSum F (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (emb t)) (om (1, γ) Ψ)) =
      thetaSum F (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (mat γ⁻¹ *ᵥ emb t)) Ψ) := by
    intro t
    have himpl := hS.impl ((1 : UA σ X.J), γ) (Matrix.vecMulVec (incV F H.x) (mat γ⁻¹ *ᵥ emb t)) Ψ hΨ
    have hact : actAB (cA σ) ((1 : UA σ X.J), γ) (Matrix.vecMulVec (incV F H.x) (mat γ⁻¹ *ᵥ emb t)) =
        Matrix.vecMulVec (incV F H.x) (emb t) := by
      show (1 : Matrix (Fin n) (Fin n) (AE F E)) * _ * (mat γ)ᵀ = _
      rw [Matrix.one_mul, vmv_mul_transpose, Matrix.mulVec_mulVec, ← GlobalTheory.ThK.UnipDom.Inverse.mat_mul,
        mul_inv_cancel, GlobalTheory.ThK.UnipDom.Inverse.mat_one, Matrix.one_mulVec]
    rw [hact] at himpl
    rw [← himpl, thetaSum_om_rat hKP hP γ hγ _ (hsch _ Ψ hΨ)]
  have hphase : ∀ v t, B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
      (Matrix.vecMulVec (incV F H.y) (incV F v)) (Matrix.vecMulVec (incV F H.x) (mat γ⁻¹ *ᵥ emb t))) =
      GlobalTheory.ExpSumUniq.chr (lam (eg v)) t := by
    intro v t
    have e1 : mat (1 : UA σ X.J) * Matrix.vecMulVec (incV F H.y) (incV F v) * (mat γ)ᵀ =
        Matrix.vecMulVec (incV F H.y) (incV F (eg v)) := by
      rw [GlobalTheory.ThK.UnipDom.Inverse.mat_one, Matrix.one_mul, vmv_mul_transpose, hmv, heg]
    have e2 : mat (1 : UA σ X.J) * Matrix.vecMulVec (incV F H.x) (mat γ⁻¹ *ᵥ emb t) * (mat γ)ᵀ =
        Matrix.vecMulVec (incV F H.x) (emb t) := by
      rw [GlobalTheory.ThK.UnipDom.Inverse.mat_one, Matrix.one_mul, vmv_mul_transpose, Matrix.mulVec_mulVec,
        ← GlobalTheory.ThK.UnipDom.Inverse.mat_mul, mul_inv_cancel, GlobalTheory.ThK.UnipDom.Inverse.mat_one, Matrix.one_mulVec]
    rw [← hc, ← GlobalTheory.SympInv.symp_act F E σ n d X W 1 γ, e1, e2]
  have hsum1 : Summable fun v => ℓ v (om (1, γ) Ψ) := (hexp _ hΨ₁).1
  have hsum0 : Summable fun v => ℓ (eg.symm v) Ψ := (Equiv.summable_iff eg.symm).mpr (hexp Ψ hΨ).1
  have hkey : ∀ t : Fin N → ℝ, ∑' v, (ℓ v (om (1, γ) Ψ) - ℓ (eg.symm v) Ψ) *
      Complex.exp (2 * Real.pi * Complex.I * ∑ j, (lam v j : ℂ) * (t j : ℂ)) = 0 := by
    intro t
    have hA : C₀ * ∑' v, GlobalTheory.ExpSumUniq.chr (lam v) t * ℓ v (om (1, γ) Ψ) =
        C₀ * ∑' v, GlobalTheory.ExpSumUniq.chr (lam v) t * ℓ (eg.symm v) Ψ := by
      rw [← hexpz _ hΨ₁ t, hinvz t, (hexp _ (hsch _ Ψ hΨ)).2]
      congr 1
      rw [← Equiv.tsum_eq eg (fun v => GlobalTheory.ExpSumUniq.chr (lam v) t * ℓ (eg.symm v) Ψ)]
      refine tsum_congr fun v => ?_
      rw [Equiv.symm_apply_apply, term_rho M M₁ hstd H.ι 1 H.x H.y e he (incV F v) _ Ψ hΨ, hphase]
    have hB := mul_left_cancel₀ hC₀ hA
    have hs1 : Summable fun v => GlobalTheory.ExpSumUniq.chr (lam v) t * ℓ v (om (1, γ) Ψ) :=
      Summable.of_norm (by simpa [norm_mul, hcn] using summable_norm_iff.mpr hsum1)
    have hs2 : Summable fun v => GlobalTheory.ExpSumUniq.chr (lam v) t * ℓ (eg.symm v) Ψ :=
      Summable.of_norm (by simpa [norm_mul, hcn] using summable_norm_iff.mpr hsum0)
    rw [← sub_eq_zero, ← hs1.tsum_sub hs2] at hB
    rw [← hB]
    refine tsum_congr fun v => ?_
    simp only [GlobalTheory.ExpSumUniq.chr]
    ring
  have hzero := GlobalTheory.ExpSumUniq.coeff_eq_zero N (Fin d → E) lam (fun v => ℓ v (om (1, γ) Ψ) - ℓ (eg.symm v) Ψ)
    hinj (hsum1.sub hsum0) hkey (eg w)
  simp only [Equiv.symm_apply_apply] at hzero
  rw [← hww', hmv]
  exact sub_eq_zero.mp hzero

end GlobalTheory.ThKReindex

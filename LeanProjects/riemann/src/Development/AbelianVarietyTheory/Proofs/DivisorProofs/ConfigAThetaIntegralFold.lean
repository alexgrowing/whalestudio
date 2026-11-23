import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartUnfoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartFoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartCompareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSectionArchimedeanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicFixedVectorDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEigenvectorIdeleAbsoluteStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open Classical

namespace GlobalTheory.ThK.SigmaVal

theorem coneInfInt_sigma : ∀ (hKP : GlobalTheory.ThK.KP) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W)
    (hCfg : CfgA B G G₁ H H') (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁')
    (e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')) (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e)
    (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
    (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ)
    (hei : ei ≠ 0) (hev : ∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _)
    (hpure : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v))
    (K : Subgroup (UA σ G.V.J)) (hK : IsStab B K) (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F)))
    (hμK : IsNormK K (evI F) μK) (hμ : μ.IsHaarMeasure)
    (l : SInf F (Fin b × Fin (b + a')) →L[ℂ] ℂ) (hl : l ≠ 0)
    (hinv : ∀ g ∈ UAt σ G₁.V (evI F), ∀ f f₁ : SInf F (Fin b × Fin (b + a')), Acts (evI F) (om₁ (g, 1)) f f₁ → l f₁ = l f) (f : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (k : KAt K (evI F)) (t : idelesAt E (evI F))
    (h : mat k.1⁻¹ *ᵥ ((t.1 : AE F E) • incV F H.x) = incV F H.x),
    l (coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f k.1 t.1) = l (coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f 1 1) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e he ei ev hei hev hpure K hK μK μ hμK hμ l hl hinv f k t h
  have hP := hKP.base
  have hle : IsLocPart G.M G₁.M e ei ev := ⟨hei, hev, hpure⟩
  have t1 := GlobalTheory.T.config_A_local_part_theta hP F E σ B b a' G G₁ H H' hC e he ei ev hle X om om' om₁ om₁' hT hT₁
  have t2 := GlobalTheory.T.config_A_local_part_integral hP F E σ B b a' G G₁ H H' hC e he ei ev hle X om om' om₁ om₁' hT hT₁
  have t3 := GlobalTheory.T.config_A_local_part_unfold hP F E σ B b a' G G₁ H H' hC e he ei ev hle X om om' om₁ om₁' hT hT₁
  have t4 := GlobalTheory.T.config_A_local_part_fold hP F E σ B b a' G G₁ H H' hC e he ei ev hle X om om' om₁ om₁' hT hT₁
  have t5 := GlobalTheory.T.config_A_local_part_compare hP F E σ B b a' G G₁ H H' hC e he ei ev hle X om om' om₁ om₁' hT hT₁
  obtain ⟨m, hm⟩ := GlobalTheory.T.levi_section_archimedean F E σ B b a' G G₁ H H' hC hT.base hT.geo hT₁.geo
  have hl₀ : ∀ g₀ ∈ UAt σ G₁.V (evI F), ∀ f₀ : SInf F (Fin b × Fin (b + a')), l (locOpInf (om₁ (g₀, 1)) f₀) = l f₀ :=
    fun g₀ hg₀ f₀ => hinv g₀ hg₀ f₀ _ (acts_locOpInf (GlobalTheory.ThK.ArchActs.acts_inf hKP F E σ B b a' G₁ X om₁ om₁' hT₁ g₀ hg₀ f₀))
  have hfix : ∀ x : UA σ G.V.J, mat x *ᵥ incV F H.x = incV F H.x →
      actAB (cA σ) ((x, 1) : UA σ G.V.J × UA σ G.W.J) (shiftA H H' 1) = shiftA H H' 1 := by
    intro x hx
    have h : mat x * Matrix.vecMulVec (incV F H.x) (incV F H'.y) = Matrix.vecMulVec (incV F H.x) (incV F H'.y) :=
      (Matrix.mul_vecMulVec _ _ _).trans (by rw [hx])
    simp only [actAB, shiftA, Units.val_one, one_smul, Prod.snd_one, Prod.fst]
    simpa [mat] using h
  have hunipfix : ∀ n ∈ unip σ G.V H, mat n *ᵥ incV F H.x = incV F H.x := by
    intro n hn
    induction hn using Subgroup.closure_induction with
    | mem x hx => exact hx.1
    | one => rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]
    | mul x y _ _ hx hy => rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hy, hx]
    | inv x _ hx =>
      conv_lhs => rw [← hx]
      rw [Matrix.mulVec_mulVec, ← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]
  obtain ⟨j, hj⟩ := hT.geo.even
  have hlt := hT.geo.lt
  have hzr : (((b + 2 - a') / 2 : ℕ) : ℝ) = ((b + 1 : ℕ) : ℝ) - ((b + a' : ℕ) : ℝ) / 2 := by
    have h2 : 2 * ((b + 2 - a') / 2) + a' = b + 2 := by omega
    have h2' : (2 : ℝ) * (((b + 2 - a') / 2 : ℕ) : ℝ) + (a' : ℝ) = (b : ℝ) + 2 := by exact_mod_cast h2
    push_cast
    linarith
  have key : ∀ (k : UA σ G.V.J), k ∈ UAt σ G.V (evI F) →
      ∀ y : (AE F E)ˣ, y ∈ idelesAt E (evI F) →
      l (coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f k y) =
        l (ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' 1))) (locOpInf (om (m y⁻¹ * k, 1)) f))) *
          (((absE F E y : ℝ) ^ ((b + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
    intro k hk y hy
    obtain ⟨hL, hmU⟩ := hm y⁻¹ (inv_mem hy)
    have h5 := t5 y⁻¹ (m y⁻¹) (inv_mem hy) hL hmU (locOpInf (om (k, 1)) f)
    rw [t3 (m y⁻¹) hmU k hk f, inv_inv] at h5
    rw [h5, coneInfInt]
    simp only [map_smul, smul_eq_mul]
    have hν : ((X.ν y⁻¹ : Circle) : ℂ)⁻¹ = (X.ν y : ℂ) := by simp
    have habs : absE F E y⁻¹ = (absE F E y)⁻¹ := map_inv _ _
    have hr : (0 : ℝ) < (absE F E y : ℝ) := by
      have h1 : absE F E y * absE F E y⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      have h0 : absE F E y ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact zero_ne_one h1
      exact_mod_cast pos_iff_ne_zero.2 h0
    rw [hν, habs]
    have hreal : ((absE F E y : ℝ)) ^ ((b + 2 - a') / 2) =
        ((absE F E y : ℝ))⁻¹ ^ (((b + a' : ℕ) : ℝ) / 2) * (absE F E y : ℝ) ^ ((b + 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast, hzr, Real.inv_rpow hr.le, Real.rpow_sub hr]
      field_simp
    have hc : ((absE F E y : ℝ) : ℂ) ^ ((b + 2 - a') / 2) =
        ((((absE F E y : ℝ))⁻¹ ^ (((b + a' : ℕ) : ℝ) / 2) : ℝ) : ℂ) * (((absE F E y : ℝ) ^ ((b + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, hreal, Complex.ofReal_mul]
    rw [hc]
    push_cast
    ring
  set L : UA σ G.V.J → ℂ := fun x => l (ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' 1))) (locOpInf (om (x, 1)) f))) with hLdef
  have hLunip : ∀ n ∈ unip σ G.V H, n ∈ UAt σ G.V (evI F) → ∀ x ∈ UAt σ G.V (evI F), L (n * x) = L x := by
    intro n hn hnI x hx
    simp only [hLdef]
    rw [← t3 n hnI x hx f]
    have h4 := t4 n hnI (shiftA H H' 1) (locOpInf (om (x, 1)) f)
    rw [hfix n (hunipfix n hn)] at h4
    rw [← h4, t1 n hn hnI]
  have hLlevi : ∀ (g₀ : UA σ G₁.V.J) (g' : UA σ G.V.J), IsLevi H 1 g₀ g' → g' ∈ UAt σ G.V (evI F) →
      g₀ ∈ UAt σ G₁.V (evI F) → ∀ x ∈ UAt σ G.V (evI F), L (g' * x) = L x := by
    intro g₀ g' hL hg' hg₀ x hx
    simp only [hLdef]
    rw [← t3 g' hg' x hx f]
    have h4 := t4 g' hg' (shiftA H H' 1) (locOpInf (om (x, 1)) f)
    rw [hfix g' (by simpa using hL.1)] at h4
    rw [← h4, t2 g₀ g' hL hg' hg₀, hl₀ g₀ hg₀]
  have h1U : (1 : UA σ G.V.J) ∈ UAt σ G.V (evI F) := (UAtSub σ G.V (evI F)).one_mem
  have h1U₁ : (1 : UA σ G₁.V.J) ∈ UAt σ G₁.V (evI F) := (UAtSub σ G₁.V (evI F)).one_mem
  have hkU : k.1 ∈ UAt σ G.V (evI F) := k.2.2
  have hkx : mat k.1 *ᵥ incV F H.x = (t.1 : AE F E) • incV F H.x := by
    calc mat k.1 *ᵥ incV F H.x = mat k.1 *ᵥ (mat k.1⁻¹ *ᵥ ((t.1 : AE F E) • incV F H.x)) := by rw [h]
      _ = (t.1 : AE F E) • incV F H.x := by
        rw [Matrix.mulVec_mulVec, ← GlobalTheory.StabHaar.mat_mul, mul_inv_cancel, GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]
  have habs1 : absE F E t.1 = 1 := GlobalTheory.T.stabilizer_eigenvector_idele_absolute F E σ B b a' G G₁ H H' hC hT.base hT.geo K hK k.1 k.2 t.1 t.2 hkx
  obtain ⟨hLt, hmtU⟩ := hm t.1⁻¹ (inv_mem t.2)
  have hpU : m t.1⁻¹ * k.1 ∈ UAt σ G.V (evI F) := (UAtSub σ G.V (evI F)).mul_mem hmtU hkU
  have hpx : mat (m t.1⁻¹ * k.1) *ᵥ incV F H.x = incV F H.x := by
    rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hkx, Matrix.mulVec_smul, hLt.1, smul_smul, Units.mul_inv, one_smul]
  obtain ⟨n, m', g₀, hn, hnU, hlev, hm'U, hg₀U, hpeq⟩ :=
    GlobalTheory.T.parabolic_fixed_vector_decomposition F E σ B b a' G G₁ H H' hC hT.base hT.geo hT₁.geo _ hpU hpx
  obtain ⟨hL1, hm1U⟩ := hm 1 (one_mem _)
  have e1 : L (m t.1⁻¹ * k.1) = L 1 := by
    rw [hpeq, ← mul_one m', hLunip n hn hnU _ ((UAtSub σ G.V (evI F)).mul_mem hm'U h1U),
      hLlevi g₀ m' hlev hm'U hg₀U 1 h1U]
  have e2 : L (m 1⁻¹ * 1) = L 1 := by
    rw [inv_one, hLlevi 1 (m 1) hL1 hm1U h1U₁ 1 h1U]
  rw [key k.1 hkU t.1 t.2, key 1 h1U 1 (one_mem _)]
  change L (m t.1⁻¹ * k.1) * _ = L (m 1⁻¹ * 1) * _
  rw [e1, e2, habs1, map_one]

end GlobalTheory.ThK.SigmaVal

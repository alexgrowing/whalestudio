import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescentModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSignatureDropsByPlaneStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EvFactor

open GlobalTheory.ThKMixXEx

theorem exists_isEv_plane (hPr : GlobalTheory.FunPr.Hypotheses₂) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {r s r' s' : ℕ}
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ)
    {n₁ : ℕ} {X₁ : Spc F E n₁} (H : Plane E n n₁) {j₀ j₁ : ℕ} (M₁ : Model σ X₁ W) {r₁ s₁ : ℕ}
    (hX₁ : X₁.IsHerm σ B r₁ s₁) (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hM₁ : M₁.IsGood B.ψ) :
    ∃ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e := by
  classical
  obtain ⟨j, co, hj, hrat, hι, hx, hy⟩ :=
    GlobalTheory.T.exists_adapted_basis_hermitian F E σ B n d X W r s r' s' hB hX hW n₁ X₁ H j₀ j₁ M₁ r₁ s₁ hX₁ hH hM₁
  obtain ⟨e₁, ei₁, ev₁, hsurj, hmaps, hheis, hSB, hvac, hstd, hpure⟩ :=
    GlobalTheory.T.darboux_coordinates_good_model F E σ B n d X W M r s r' s' hB hX hW hM co hrat
  have hres := fun v => GlobalTheory.T.adapted_basis_hermitian_unique F E σ B n d X W r s r' s' hB hX hW n₁ X₁ H j₀ j₁ M₁ r₁ s₁ hX₁ hH
    hM₁ j co hj hι hx hy v _ (hvac v)
  choose c hc0 hc using hres
  have hc1 : ∀ᶠ v in cofinite, c v = 1 := by
    filter_upwards [hstd, hM₁.std] with v h1 h2
    have h' := hc v
    rw [h1, h2, std_extend hj v] at h'
    have h := congrFun h' 0
    have hm : (0 : Fin n₁ × Fin d → Fv F v) ∈ {x : Fin n₁ × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} :=
      fun i => zero_mem _
    rw [Pi.smul_apply, Set.indicator_of_mem hm, smul_eq_mul] at h
    simpa using h.symm
  obtain ⟨R, hR⟩ := GlobalTheory.T.exists_restriction_extend_by_zero F j hj
  refine ⟨(∏ᶠ v, c v)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → AF F => Function.extend j y 0) ∘ₗ e₁),
    ⟨?_, ?_, ?_, ?_⟩⟩
  · intro Φ hΦ
    exact Submodule.smul_mem _ _ (GlobalTheory.T.extend_by_zero_mem_schA F j hj _ (hmaps Φ hΦ))
  · intro z Φ hΦ
    have h1 : incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ = incM F H.ι * z := by
      rw [show incM F (1 : Matrix (Fin d) (Fin d) E) = 1 from Matrix.map_one _ (map_zero _) (map_one _)]
      simp
    rw [h1]
    funext y
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [hheis _ Φ hΦ]
    simp only [Darboux.rho, schr, hι, extend_dot hj, ← extend_add hj, Pi.smul_apply, smul_eq_mul,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply]
    ring
  · intro u hu Φ hΦ
    obtain ⟨z, rfl⟩ := hu
    funext y
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [hheis _ Φ hΦ]
    obtain ⟨h1, h2⟩ := hx z
    simp only [Darboux.rho, schr, h1, extend_dot_zero _ _ h2, zero_dotProduct, mul_zero, add_zero,
      AddChar.map_zero_eq_one, one_mul]
  · obtain ⟨b, hb0⟩ : ∃ b : SInf F (Fin n × Fin d), b 0 ≠ 0 := by
      let bb : ContDiffBump (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
      have hs : HasCompactSupport (fun x => ((bb x : ℝ) : ℂ)) :=
        bb.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
      have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((bb x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp bb.contDiff
      refine ⟨hs.toSchwartzMap hcd, ?_⟩
      have h2 : bb 0 = 1 := bb.one_of_mem_closedBall (by simp [bb])
      simp [h2]
    obtain ⟨f₀, hf₀⟩ := hsurj b
    refine ⟨R.comp ei₁, fun v => (c v)⁻¹ •
      (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → Fv F v => Function.extend j y 0) ∘ₗ ev₁ v), ?_, ?_, ?_⟩
    · intro h
      have := congrArg (fun T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d) => T f₀ 0) h
      simp only [ContinuousLinearMap.comp_apply, hR, hf₀, extend_zero' hj, ContinuousLinearMap.zero_apply,
        SchwartzMap.zero_apply] at this
      exact hb0 this
    · intro v
      refine ⟨?_, ?_⟩
      · rw [LinearMap.smul_apply, LinearMap.comp_apply]
        rw [show LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → Fv F v => Function.extend j y 0) (ev₁ v (M.vac v)) =
          c v • M₁.vac v from hc v, smul_smul, inv_mul_cancel₀ (hc0 v), one_smul]
      · rw [Submodule.map_smul _ _ _ (inv_ne_zero (hc0 v)), Submodule.map_comp, hSB v, GlobalTheory.T.extend_by_zero_schwartzBruhat_map F j hj v]
    · intro f φ hφ hφv
      funext y
      rw [LinearMap.smul_apply, LinearMap.comp_apply, hpure f φ hφ hφv]
      simp only [LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure,
        ContinuousLinearMap.comp_apply, hR, LinearMap.smul_apply, LinearMap.comp_apply]
      have hI : (fun i => evI F (Function.extend j y 0 i)) = Function.extend j (fun i => evI F (y i)) 0 :=
        extend_map hj (evI F) (by unfold evI; exact map_zero _) y
      have hF : ∀ v : Pl F, (fun i => evFin F v (Function.extend j y 0 i)) =
          Function.extend j (fun i => evFin F v (y i)) 0 := fun v => extend_map hj _ (map_zero _) y
      simp only [hI, hF]
      have hfin1 : (Function.mulSupport fun v : Pl F => (c v)⁻¹).Finite := by
        refine (Filter.eventually_cofinite.1 hc1).subset fun v hv h => hv ?_
        simp [h]
      have hfin2 : (Function.mulSupport fun v : Pl F =>
          ev₁ v (φ v) (Function.extend j (fun i => evFin F v (y i)) 0)).Finite := by
        have := GlobalTheory.PureFactor.mulSupport_finite (κ := Fin n₁ × Fin d)
          (fun v x => ev₁ v (φ v) (Function.extend j x 0)) (by
            filter_upwards [hφv, hstd] with v h1 h2
            rw [h1, h2]
            exact std_extend hj v) y
        exact this
      rw [finprod_mul_distrib hfin1 hfin2, finprod_inv_distrib]
      ring

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] [Invertible (2 : R)] {K : Subgroup Rˣ}
    {χ₁ χ₂ : Eˣ →* Circle} {m n : ℕ} (h₁ : ResEtaPow K χ₁ m) (h₂ : ResEtaPow K χ₂ n) :
    ResEtaPow K (χ₁ / χ₂) (m + n) := by
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h₁ x, h₂ x]
  split_ifs
  · simp
  · have h : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [div_eq_iff (pow_ne_zero _ (by norm_num)), pow_add, mul_assoc, h, mul_one]

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {χ₁ χ₂ : Chr F E}
    (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) :=
  ⟨h₁.1.div' h₂.1, fun x => by rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x]; exact div_self' 1⟩

theorem incM_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) :
    incM F (1 : Matrix (Fin k) (Fin k) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem vecMulVec_mulVec_eq {R : Type} [CommRing R] {m k l : ℕ} (x : Fin m → R) (A : Matrix (Fin k) (Fin l) R) (z : Fin l → R) :
    Matrix.vecMulVec x (A *ᵥ z) = Matrix.vecMulVec x z * Aᵀ := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

end GlobalTheory.EvFactor

open GlobalTheory.EvFactor in

theorem GlobalTheory.EvFactor.evalA_factor : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ → ∀ ea : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F a (a + b), IsEv B G.M G₁.M 1 H'.ι (iso0 a H') ea → ∃ (eb : Fn F a (a + b) →ₗ[ℂ] Fn F n₁ (a + b)) (c : ℂ), IsEv B G₁.M M₂ H₀.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H₀.x) z} eb ∧ ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ Ψ = c • eb (ea Ψ) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev ea hea
  obtain ⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩ := G₁
  have eV : V₁ = G.V := cfg.eV
  subst eV
  let M₀ : Model σ (reS G.V V₂) G.W := ⟨G.M.co, G.M.vac, G.M.μ, G.M.dom⟩
  let Ma : Model σ (reS G.V V₂) W₁ := ⟨M₁.co, M₁.vac, M₁.μ, M₁.dom⟩
  have hM₀ : M₀.IsGood B.ψ := ⟨T.geo.hM.rat, T.geo.hM.vac, T.geo.hM.std, T.geo.hM.haar, T.geo.hM.dom⟩
  have hMa : Ma.IsGood B.ψ := ⟨T₁.geo.hM.rat, T₁.geo.hM.vac, T₁.geo.hM.std, T₁.geo.hM.haar, T₁.geo.hM.dom⟩
  have hX₁ := GlobalTheory.T.hermitian_signature_drops_by_plane F E σ B T.base a n₁ (reS G.V V₂) X₁ H₀ j₀ j₁ _ _ hV₂ hH₀
  obtain ⟨eb, heb⟩ := exists_isEv_plane hKP.base Ma T.base hV₂ T₁.geo.hW hMa H₀ M₂ hX₁ hH₀ hM₂
  have heb' : IsEv B M₁ M₂ H₀.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H₀.x) z} eb :=
    ⟨heb.1, heb.2, heb.3, heb.4⟩
  have hev₀ : IsEv B M₀ M₂ H₀.ι H'.ι (isoA H₀ H') e₂ := ⟨hev.1, hev.2, hev.3, hev.4⟩
  have hea₀ : IsEv B M₀ Ma 1 H'.ι (iso0 a H') ea := ⟨hea.1, hea.2, hea.3, hea.4⟩
  have P : IsPair B M₀ X.β (X.β / X.α) om (a - G.p) G.p _ _ :=
    ⟨T.base, hV₂, T.geo.hW, hM₀, T.chars.heckeβ, isHecke_div T.chars.heckeβ T.chars.heckeα,
      T.chars.resβ, resEtaPow_div T.chars.resβ T.chars.resα, T.weil⟩
  have Pa : IsPair B Ma X.β (X.β / X.α) om₁ (a - G.p) G.p _ _ :=
    ⟨T₁.base, hV₂, T₁.geo.hW, hMa, T₁.chars.heckeβ, isHecke_div T₁.chars.heckeβ T₁.chars.heckeα,
      T₁.chars.resβ, resEtaPow_div T₁.chars.resβ T₁.chars.resα, T₁.weil⟩
  have hheis : ∀ (z : Matrix (Fin n₁) (Fin (a + b)) (AE F E)), ∀ Φ ∈ schA F (Fin a × Fin (a + (b + 2))),
      (eb ∘ₗ ea) (M₀.co.rho B.ψ (incM F H₀.ι * z * (incM F H'.ι)ᵀ) Φ) = M₂.co.rho B.ψ z ((eb ∘ₗ ea) Φ) := by
    intro z Φ hΦ
    show eb (ea (G.M.co.rho B.ψ (incM F H₀.ι * z * (incM F H'.ι)ᵀ) Φ)) = M₂.co.rho B.ψ z (eb (ea Φ))
    have h1 : incM F H₀.ι * z * (incM F H'.ι)ᵀ = incM F (1 : Matrix (Fin a) (Fin a) E) * (incM F H₀.ι * z) * (incM F H'.ι)ᵀ := by
      rw [incM_one', Matrix.one_mul]
    have h2 : incM F H₀.ι * z = incM F H₀.ι * z * (incM F (1 : Matrix (Fin (a + b)) (Fin (a + b)) E))ᵀ := by
      rw [incM_one', Matrix.transpose_one, Matrix.mul_one]
    rw [h1, hea.Heisenberg₂ _ Φ hΦ, h2, heb'.Heisenberg₂ z _ (hea.maps Φ hΦ)]
  have hinv : ∀ u ∈ isoA H₀ H', ∀ Φ ∈ schA F (Fin a × Fin (a + (b + 2))),
      (eb ∘ₗ ea) (M₀.co.rho B.ψ u Φ) = (eb ∘ₗ ea) Φ := by
    rintro u (hu | ⟨z, rfl⟩) Φ hΦ
    · show eb (ea (G.M.co.rho B.ψ u Φ)) = eb (ea Φ)
      rw [hea.inv u hu Φ hΦ]
    · show eb (ea (G.M.co.rho B.ψ _ Φ)) = eb (ea Φ)
      have h1 : Matrix.vecMulVec (incV F H₀.x) (incM F H'.ι *ᵥ z) =
          incM F (1 : Matrix (Fin a) (Fin a) E) * Matrix.vecMulVec (incV F H₀.x) z * (incM F H'.ι)ᵀ := by
        rw [incM_one', Matrix.one_mul, vecMulVec_mulVec_eq]
      rw [h1, hea.Heisenberg₂ _ Φ hΦ, heb'.inv _ ⟨z, rfl⟩ _ (hea.maps Φ hΦ)]
  obtain ⟨c, hc⟩ := GlobalTheory.T.pair_double_descent hKP.base F E σ B a (a + (b + 2)) n₁ (a + b) (reS G.V V₂) G.W X₁ W₁ M₀ X.β (X.β / X.α) om
    _ _ _ _ P H₀ H' j₀ j₁ a (a + b + 1) M₂ hH₀ cfg.hH' hM₂ e₂ hev₀ (eb ∘ₗ ea) hheis hinv
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.T.pair_double_descent_models hKP.base F E σ B a (a + (b + 2)) n₁ (a + b) (reS G.V V₂) G.W X₁ W₁ M₀ X.β (X.β / X.α) om
    _ _ _ _ P H₀ H' j₀ j₁ a (a + b + 1) Ma om₁ _ _ M₂ hH₀ cfg.hH' Pa hM₂ ea eb hea₀ heb
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hne
    have := hc Φ₀ hΦ₀
    rw [zero_smul] at this
    exact this
  refine ⟨eb, c⁻¹, heb', fun Ψ hΨ => ?_⟩
  have h := hc Ψ hΨ
  rw [LinearMap.comp_apply] at h
  rw [h, smul_smul, inv_mul_cancel₀ hc0, one_smul]

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteAndIsInvInvariantOfContinuousIntegrab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarIntegralFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarUnfoldingAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarStabilizerStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.XTermExch

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ideleTop' (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsTopologicalGroup (AE F E)ˣ ∧ LocallyCompactSpace (AE F E)ˣ ∧ SecondCountableTopology (AE F E)ˣ ∧
    T2Space (AE F E)ˣ := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact ⟨inferInstance, Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology, inferInstance⟩

theorem integral_inv_idele (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (μ : Measure (AE F E)ˣ) [μ.IsHaarMeasure] (f : (AE F E)ˣ → ℂ) : ∫ l, f l⁻¹ ∂μ = ∫ l, f l ∂μ := by
  obtain ⟨v1, v2, v3, v4⟩ := ideleTop' F E
  haveI := v1; haveI := v2; haveI := v3; haveI := v4
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  obtain ⟨g, hg1, -, hgc, -⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := (1 : (AE F E)ˣ)))
    isClosed_empty (Set.disjoint_empty _)
  have hcont : Continuous fun x => ((g x : ℝ) : ℂ) := Complex.continuous_ofReal.comp g.continuous
  have hint : Integrable (fun x => ((g x : ℝ) : ℂ)) μ :=
    hcont.integrable_of_hasCompactSupport (hgc.comp_left Complex.ofReal_zero)
  have h1 : ((g 1 : ℝ) : ℂ) ≠ 0 := by rw [hg1 rfl]; simp
  obtain ⟨-, hinv⟩ := GlobalTheory.sigmaFinite_and_isInvInvariant_of_continuous_integrable _ μ _ hcont h1 hint
  exact integral_inv_eq_self f μ

theorem polData_le_schA' {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W)
    (hM : M.IsGood B.ψ) : PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro Φ ⟨f, -, φ, hSB, hvac, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hvac.and hM.std).mono fun v hv => hv.1.trans hv.2)

theorem weight_inv {b a' : ℕ} (hlt : a' < b) (hev : Even (b + a')) {t : ℝ} (ht : 0 < t) :
    t ^ (((b + a' : ℕ) : ℝ) / 2) * t ^ (1 - ((b + 2 : ℕ) : ℝ)) = t⁻¹ ^ ((b + 2 - a') / 2) := by
  obtain ⟨r, hr⟩ := hev
  have hz : (((b + 2 - a') / 2 : ℕ) : ℝ) = -(((b + a' : ℕ) : ℝ) / 2 + (1 - ((b + 2 : ℕ) : ℝ))) := by
    have h2 : (b + 2 - a') / 2 = b + 1 - r := by omega
    rw [h2, Nat.cast_sub (by omega)]; push_cast
    have : (b : ℝ) + a' = r + r := by exact_mod_cast hr
    linarith
  rw [← Real.rpow_add ht, inv_pow, ← Real.rpow_natCast, hz, Real.rpow_neg ht.le, inv_inv]

variable (F E) in
theorem absE_inv (l : (AE F E)ˣ) : (absE F E l⁻¹ : ℝ) = (absE F E l : ℝ)⁻¹ := by
  rw [map_inv, NNReal.coe_inv]

variable (F E) in
theorem absE_pos (l : (AE F E)ˣ) : 0 < (absE F E l : ℝ) := by
  have h1 : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one h1))

theorem iterated_eq_cone : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ ∈ PolData B G.M, ∀ h,
      ∫ k, ∫ l, ∫ g₀ in G₁.M.dom, (X.ν l : ℂ)⁻¹ * (((absE F E l : ℝ) ^ (((b + a' : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
          thetaSum F (om₁ (g₀, 1) (e (G.M.co.rho B.ψ (shiftA H H' l⁻¹) (om (k.1, h) Φ)))) *
          (((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ)) : ℝ) : ℂ) ∂G₁.M.μ ∂μ ∂μK =
        G₁.M.I om₁ (cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (om (1, h) Φ)) 1 := by

  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Φ hΦ h
  have hΨ : om (1, h) Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) :=
    (IsUWeilPair.isUSplitting hT.weil).pres (1, h) Φ (polData_le_schA' B G.M hT.geo.hM hΦ)
  have hk : ∀ k : UA σ G.V.J, om (k, 1) (om (1, h) Φ) = om (k, h) Φ := by
    intro k; rw [← Module.End.mul_apply, ← map_mul]; simp
  have hA : ∀ k : K, ∫ l, ∫ g₀ in G₁.M.dom, (X.ν l : ℂ)⁻¹ * (((absE F E l : ℝ) ^ (((b + a' : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
          thetaSum F (om₁ (g₀, 1) (e (G.M.co.rho B.ψ (shiftA H H' l⁻¹) (om (k.1, h) Φ)))) *
          (((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ)) : ℝ) : ℂ) ∂G₁.M.μ ∂μ =
      ∫ l, ∫ g₀ in G₁.M.dom, (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) *
          thetaSum F (om₁ (g₀, 1) (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, h) Φ)))) ∂G₁.M.μ ∂μ := by
    intro k
    rw [← integral_inv_idele F E μ (fun l => ∫ g₀ in G₁.M.dom, (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) *
          thetaSum F (om₁ (g₀, 1) (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, h) Φ)))) ∂G₁.M.μ)]
    congr 1; funext l; congr 1; funext g₀
    have hw := weight_inv hT₁.geo.lt hT₁.geo.even (absE_pos F E l)
    rw [absE_inv, ← Complex.ofReal_pow, ← hw, map_inv, Circle.coe_inv]
    push_cast; ring
  calc _ = ∫ k, ∫ l, ∫ g₀ in G₁.M.dom, (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) *
          thetaSum F (om₁ (g₀, 1) (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, h) Φ)))) ∂G₁.M.μ ∂μ ∂μK := by
        congr 1; funext k; exact hA k
    _ = ∫ g₀ in G₁.M.dom, ∫ k, ∫ l, (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) *
          thetaSum F (om₁ (g₀, 1) (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, h) Φ)))) ∂μ ∂μK ∂G₁.M.μ :=
        GlobalTheory.T.config_a_haar_integral_formula hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Φ hΦ h
    _ = _ := by
        show _ = ∫ g in G₁.M.dom, thetaSum F (om₁ (g, 1) _) ∂G₁.M.μ
        congr 1; funext g₀
        rw [GlobalTheory.T.config_a_haar_unfolding_alt hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ _ hΨ (g₀, 1),
          GlobalTheory.T.config_a_haar_stabilizer hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ _ hΨ (g₀, 1)]
        simp only [hk]

end GlobalTheory.XTermExch

end

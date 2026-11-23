import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEigenIntertwinerTripleFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleConfigBThetaIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentHaarDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerDoubleRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationUnramifiedIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationArchimedeanIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatibleStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.ConeUnfold

theorem coneTerm_left_inv_val (hKP : GlobalTheory.ThK.KP) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)) (hC : CfgB B G G₁ H H') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁') (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)) (hV₂ : (reS G.V V₂).IsHerm σ B (a - G.p) G.p) (hH₀ : H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁) (hM₂ : M₂.IsGood B.ψ) (hev : IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂) (Φ : Fn F a (a + (b + 2))) (hΦ : Φ ∈ PolData B G.M) (h : UA σ G.W.J)
    (Q : Subgroup (UA σ G.V.J)) (hQ : ∀ q, q ∈ Q ↔ q ∈ ratU σ G.V.J ∧ mat q *ᵥ incV F H₀.x = incV F H₀.x)
    (q : UA σ G.V.J) (hqQ : q ∈ Q) (g : UA σ G.V.J) :
    thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (q * g, h) Φ))) =
      thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (g, h) Φ))) := by
  have hq := (hQ q).1 hqQ
  have hP0 := Inhab.pairV hT
  have hP : IsPair B (StabInvB.reM G.M V₂) X.β (X.β / X.α) om (a - G.p) G.p (a + (b + 2) - (G.p + G.q)) (G.p + G.q) :=
    ⟨hP0.base, hV₂, hP0.skew, StabInvB.reM_isGood V₂ hP0.good, hP0.hX, hP0.hW, hP0.resX, hP0.resW, hP0.weil⟩
  obtain ⟨M₁, hM₁⟩ := GlobalTheory.T.exists_good_schrodinger_model F E σ B hT.base a (a + b) (reS G.V V₂) G₁.W _ _ _ _ hV₂ hT₁.geo.hW
  obtain ⟨e₀, he₀⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hKP.base).1 F E σ B a (a + (b + 2)) (reS G.V V₂) G.W (StabInvB.reM G.M V₂) _ _ om _ _ _ _
    hP (a + b) (reS G.V V₂) G₁.W H' a (a + b + 1) M₁ rfl hC.hH' hM₁).1
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.exists_unipotent_haar_domain F E σ B (a + (b + 2)) (a + b) G.W G₁.W H' a (a + b + 1) _ _ _ _
    hT.base hT.geo.hW hT₁.geo.hW hC.hH'
  obtain ⟨C, hC0, hiso⟩ := GlobalTheory.T.eigen_intertwiner_double_restriction hKP F E σ B a (a + (b + 2)) (a + b) (reS G.V V₂) G.W G₁.W (StabInvB.reM G.M V₂) M₁ H'
    a (a + b + 1) hC.hH' hM₁ e₀ he₀ n₁ X₁ H₀ j₀ j₁ M₂ hH₀ hM₂ e₂ (StabInvB.reM_isEv V₂ hev)
  have hΨ : om (g, h) Φ ∈ schA F _ := hT.weil.isUSplitting.pres _ Φ (StabInv.polData_le_schA hT.geo.hM hΦ)
  have hx0 : H₀.x ≠ 0 := by
    intro h0
    have := hH₀.xy
    rw [h0] at this
    simp [form] at this
  have key := hiso _ _ om _ _ _ _ hP μ 𝓕 hμ h𝓕 h1 _ hΨ H₀.x hx0 hH₀.xx
  have k1 := key q hq.1 hq.2
  have k2 := key 1 (one_mem _) (by simp [mat])
  rw [k1] at k2
  have k3 := mul_left_cancel₀ hC0 k2
  have hone : om (1, 1) (om (g, h) Φ) = om (g, h) Φ := by
    rw [Prod.mk_one_one, map_one om, Module.End.one_apply]
  have hmul : om (q, 1) (om (g, h) Φ) = om (q * g, h) Φ := by
    rw [← Module.End.mul_apply, ← map_mul om, Prod.mk_mul_mk, one_mul]
  have k4 : thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (q, 1) (om (g, h) Φ)))) =
      thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (1, 1) (om (g, h) Φ)))) := k3
  rw [hone, hmul] at k4
  exact k4

theorem unfold_cone : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ → ∀ γ : {x : Fin a → E // x ≠ 0 ∧ form σ G.V.J x x = 0} → UA σ G.V.J, (∀ x, γ x ∈ ratU σ G.V.J ∧ mat (γ x) *ᵥ incV F x.1 = incV F H₀.x) → ∀ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H₀.x = incV F H₀.x}) 𝓓 G.M.μ → ∀ Φ ∈ PolData B G.M, ∀ h, ∫ g in G.M.dom, ∑' x, thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (γ x * g, h) Φ))) ∂G.M.μ = ∫ g in 𝓓, thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (g, h) Φ))) ∂G.M.μ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev γ hγ 𝓓 h𝓓
    Φ hΦ h
  classical
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI := hT.geo.hM.haar
  set f : UA σ G.V.J → ℂ := fun g => thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (g, h) Φ))) with hf
  set Q : Subgroup (UA σ G.V.J) :=
    ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H₀.x = incV F H₀.x} with hQdef
  have hQ : ∀ q, q ∈ Q ↔ q ∈ ratU σ G.V.J ∧ mat q *ᵥ incV F H₀.x = incV F H₀.x := fun q =>
    ⟨fun hq => ⟨hq.1, StabInv.fix_of_mem_closure _ hq.2⟩, fun hq => ⟨hq.1, Subgroup.subset_closure hq.2⟩⟩
  haveI : Countable (Matrix (Fin a) (Fin a) E) := (inferInstance : Countable (Fin a → Fin a → E))
  haveI : Countable Q := by
    refine Function.Injective.countable
      (f := fun q : Q => Classical.choose (GlobalTheory.StabCosetDomain.rat_desc q.1 ((hQ q.1).1 q.2).1)) ?_
    intro q q' hqq
    have h1 := (Classical.choose_spec (GlobalTheory.StabCosetDomain.rat_desc q.1 ((hQ q.1).1 q.2).1)).1
    have h2 := (Classical.choose_spec (GlobalTheory.StabCosetDomain.rat_desc q'.1 ((hQ q'.1).1 q'.2).1)).1
    have hm : mat q.1 = mat q'.1 := by
      rw [h1, h2]
      exact congrArg (fun m => Matrix.map m (inclR (F := F) (AF F))) hqq
    exact Subtype.ext (Subtype.ext (Units.ext hm))
  haveI : SMulInvariantMeasure Q (UA σ G.V.J) G.M.μ := ⟨fun q s _ => measure_preimage_mul G.M.μ (q : UA σ G.V.J) s⟩
  obtain ⟨hdisj, hfd⟩ := GlobalTheory.StabCosetDomain.translates_isFundamentalDomain hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁'
    hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev γ hγ
  have hD := hfd Q hQ
  set T : {x : Fin a → E // x ≠ 0 ∧ form σ G.V.J x x = 0} → Set (UA σ G.V.J) :=
    fun x => (fun g => (γ x)⁻¹ * g) ⁻¹' G.M.dom with hTdef
  have hmeas : AEStronglyMeasurable f G.M.μ := GlobalTheory.T.second_configuration_triple_compatible hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀
    j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h
  have hfin : ∫⁻ g in ⋃ x, T x, ‖f g‖ₑ ∂G.M.μ < ⊤ := GlobalTheory.T.second_configuration_archimedean_identity hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂
    n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h Q hQ _ hD
  have hnm : ∀ x, NullMeasurableSet (T x) G.M.μ := fun x =>
    hT.geo.hM.dom.nullMeasurableSet.preimage (measurePreserving_mul_left G.M.μ (γ x)⁻¹).quasiMeasurePreserving
  have hcv : ∀ x (k : UA σ G.V.J → ℂ), ∫ g in G.M.dom, k (γ x * g) ∂G.M.μ = ∫ g in T x, k g ∂G.M.μ := by
    intro x k
    have := (measurePreserving_mul_left G.M.μ (γ x)⁻¹).setIntegral_preimage_emb
      (measurableEmbedding_mulLeft _) (fun z => k (γ x * z)) G.M.dom
    simp only [mul_inv_cancel_left] at this
    exact this.symm
  have hcvl : ∀ x (k : UA σ G.V.J → ENNReal), ∫⁻ g in G.M.dom, k (γ x * g) ∂G.M.μ = ∫⁻ g in T x, k g ∂G.M.μ := by
    intro x k
    have := (measurePreserving_mul_left G.M.μ (γ x)⁻¹).setLIntegral_comp_preimage_emb
      (measurableEmbedding_mulLeft _) (fun z => k (γ x * z)) G.M.dom
    simp only [mul_inv_cancel_left] at this
    exact this.symm
  have hint : IntegrableOn f (⋃ x, T x) G.M.μ := ⟨hmeas.restrict, hfin⟩
  have hsum : ∑' x, ∫⁻ g in G.M.dom, ‖f (γ x * g)‖ₑ ∂G.M.μ ≠ ⊤ := by
    simp_rw [hcvl _ (fun g => ‖f g‖ₑ)]
    rw [← lintegral_iUnion₀ hnm hdisj]
    exact hfin.ne
  have hsm : ∀ x, AEStronglyMeasurable (fun g => f (γ x * g)) (G.M.μ.restrict G.M.dom) := fun x =>
    (hmeas.comp_measurePreserving (measurePreserving_mul_left G.M.μ (γ x))).restrict
  have hinv : ∀ (q : Q) (g : UA σ G.V.J), f (q • g) = f g := fun q g =>
    coneTerm_left_inv_val hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h
      Q hQ q.1 q.2 g
  calc ∫ g in G.M.dom, ∑' x, f (γ x * g) ∂G.M.μ = ∑' x, ∫ g in G.M.dom, f (γ x * g) ∂G.M.μ :=
        integral_tsum hsm hsum
    _ = ∑' x, ∫ g in T x, f g ∂G.M.μ := tsum_congr fun x => hcv x f
    _ = ∫ g in ⋃ x, T x, f g ∂G.M.μ := (integral_iUnion_ae hnm hdisj hint).symm
    _ = ∫ g in 𝓓, f g ∂G.M.μ := hD.setIntegral_eq h𝓓 hinv

end GlobalTheory.ThK.ConeUnfold

end

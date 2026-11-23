import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanInvolutionSystemsConjArchimedeanUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianCartanInvolutionSystemsConjugateArcStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralArchimedeanInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsRelevantSpace

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKReV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem polData_le_schA {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W)
    (hM : M.IsGood B.ψ) : PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, hSB, hvac, rfl⟩
  refine GlobalTheory.TensUniq.pure_mem_schA f φ hSB ?_
  filter_upwards [hvac, hM.std] with v h1 h2
  rw [h1, h2]

theorem acts_pure {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} (hM : M.IsGood B.ψ)
    (Op : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)) (T : SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d))
    (hT : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) Op f (T f)) (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _) (hvac : ∀ᶠ v in cofinite, φ v = M.vac v) :
    Op (pure f φ) = pure (T f) φ :=
  hT f _ (GlobalTheory.MajTransport.rest_pure f φ hSB ((hvac.and hM.std).mono fun v hv => hv.1.trans hv.2))

theorem polData_transport {n d : ℕ} {X Y : Spc F E n} {W Z : Spc F E d} {B : Base F E} {M : Model σ X W}
    (hM : M.IsGood B.ψ) (Op : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ))
    (T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d))
    (hT : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) Op f (T.symm f))
    (hpol : (M.Pol B.ψ B.emb).map (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) =
      (GlobalTheory.MajTransport.reM M Y Z).Pol B.ψ B.emb) :
    ∀ Φ ∈ PolData B (GlobalTheory.MajTransport.reM M Y Z), Op Φ ∈ PolData B M := by
  intro Φ hΦ
  have hle : PolData B (GlobalTheory.MajTransport.reM M Y Z) ≤ (PolData B M).comap Op := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, φ, hSB, hvac, rfl⟩
    show Op (pure f φ) ∈ PolData B M
    rw [acts_pure hM Op (fun f => T.symm f) hT f φ hSB hvac]
    refine Submodule.subset_span ⟨T.symm f, ?_, φ, hSB, hvac, rfl⟩
    rw [← hpol] at hf
    obtain ⟨f₀, hf₀, rfl⟩ := hf
    simpa using hf₀
  exact hle hΦ

theorem nonZero_reV : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (V : Spc F E a) (V' : Spc F E a')
    (W : Spc F E (a + a')), IsTriple B G X om om' → IsTriple B (reG G V V' W) X om om' →
    (∃ Φ ∈ PolData B (reG G V V' W).M, (reG G V V' W).M.I om Φ ≠ 0) → ∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' V V' W hT hT₂ ⟨Φ₂, hΦ₂, hne⟩
  obtain ⟨g, hg, hθg⟩ := GlobalTheory.T.cartan_involution_systems_conj_archimedean_unitary F E σ B a _ _ G.V V hT.base hT.geo.hV hT₂.geo.hV
  obtain ⟨h, hh, hθh⟩ := GlobalTheory.T.skewHermitian_cartanInvolutionSystems_conjugate_archimedean F E σ B (a + a') _ _ G.W W hT.base hT.geo.hW hT₂.geo.hW
  obtain ⟨T, hT1, hT2⟩ := GlobalTheory.T.weil_representation_unitary_equiv hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hT.base hT.geo.hV
    hT.geo.hW hT.geo.hM hT.weil g hg h hh
  have hpol := GlobalTheory.MajTransport.pair_pol (Y := V) (Z := W) hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hg hh hT1 hT2
    hθg hθh
  have hΦ : om (g⁻¹, h⁻¹) Φ₂ ∈ PolData B G.M :=
    polData_transport hT.geo.hM (om (g⁻¹, h⁻¹)) T hT2 hpol Φ₂ hΦ₂
  have hS : Φ₂ ∈ schA F (Fin a × Fin (a + a')) := polData_le_schA B (reG G V V' W).M hT₂.geo.hM hΦ₂
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hne
  refine ⟨om (g⁻¹, h⁻¹) Φ₂, hΦ, fun h0 => hy ?_⟩
  have e := GlobalTheory.T.theta_integral_archimedean_invariant hKP.base F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1 g⁻¹ (GlobalTheory.MajTransport.uat_inv hg) h⁻¹ Φ₂ hS ((show UA σ G.W.J from y) * h)
  rw [mul_inv_cancel_right, h0] at e
  exact e.symm

end GlobalTheory.ThKReV

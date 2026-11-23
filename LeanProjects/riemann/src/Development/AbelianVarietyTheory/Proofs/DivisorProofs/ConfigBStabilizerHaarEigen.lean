import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConeRepresentatives
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawEvaluationHaarArchimedeanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawEvaluationHaarNonarchimedean
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeSmallSerLine

theorem inv_line {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (v : Fin n → AE F E) (l : (AE F E)ˣ)
    (h : mat g *ᵥ v = l.1 • v) : mat g⁻¹ *ᵥ v = (l⁻¹).1 • v := by
  have key : mat g⁻¹ *ᵥ (mat g *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, GlobalTheory.ConeSmallCTReps.mat_inv_mul, Matrix.one_mulVec]
  rw [h, Matrix.mulVec_smul] at key
  calc mat g⁻¹ *ᵥ v = (l⁻¹).1 • (l.1 • mat g⁻¹ *ᵥ v) := by
        rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    _ = (l⁻¹).1 • v := by rw [key]

theorem ctLine : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃ s₁ : ℝ, ∀ T : Set (UA σ G.W.J), GlobalTheory.ConeSmallCT.IsReps T H'.x → ∀ s : ℂ, s₁ < s.re →
      GlobalTheory.ConeSmallCT.LocUnifSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) T →
      GlobalTheory.ThK.CTAdd.CTInt H' (GlobalTheory.ConeSmallSer.partSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) (GlobalTheory.ConeSmallSer.lineSet H'.x T)) ∧
        IsCT H' (GlobalTheory.ConeSmallSer.partSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) (GlobalTheory.ConeSmallSer.lineSet H'.x T)) (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ'
  refine ⟨0, fun T hR s _ _ => ?_⟩
  set f := GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2) with hf
  obtain ⟨t₀, ⟨ht₀T, l, hl⟩, huniq⟩ := hR.2 1 (one_mem _)
  rw [one_mul] at hl
  have hstab : GlobalTheory.ConeSmallSer.StabLn H'.x t₀ := ⟨l⁻¹, by simpa using inv_line t₀⁻¹ _ l hl⟩
  have hline : GlobalTheory.ConeSmallSer.lineSet H'.x T = {t₀} := by
    ext t
    constructor
    · rintro ⟨htT, m, hm⟩
      exact huniq t ⟨htT, m⁻¹, by rw [one_mul]; exact inv_line t _ m hm⟩
    · rintro rfl
      exact ⟨ht₀T, hstab⟩
  have hpart : ∀ h, GlobalTheory.ConeSmallSer.partSum f (GlobalTheory.ConeSmallSer.lineSet H'.x T) h = f (t₀ * h) := by
    intro h
    rw [hline]
    unfold GlobalTheory.ConeSmallSer.partSum
    exact tsum_singleton t₀ (fun t => f (t * h))
  have hinv : ∀ u ∈ unip σ G.W H', ∀ h, f (t₀ * (u * h)) = f h := by
    intro u hu h
    rw [hf, GlobalTheory.T.seesaw_evaluation_haar_nonarchimedean hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' _ t₀ (hR.1 ht₀T) hstab,
      GlobalTheory.T.seesaw_evaluation_haar_archimedean hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' _ u hu]
  have hconst : ∀ (μ' : Measure (unip σ G.W H')) (h : UA σ G.W.J),
      (fun u : unip σ G.W H' => GlobalTheory.ConeSmallSer.partSum f (GlobalTheory.ConeSmallSer.lineSet H'.x T) (u.1 * h)) = fun _ => f h := by
    intro _ h
    funext u
    rw [hpart, hinv u.1 u.2]
  refine ⟨fun μ' 𝓕 _ _ h1 h => ?_, fun μ' 𝓕 _ _ h1 h => ?_⟩
  · rw [hconst μ' h]
    exact integrableOn_const (by simp [h1])
  · rw [hconst μ' h, setIntegral_const]
    simp [Measure.real, h1]

end GlobalTheory.ConeSmallSerLine

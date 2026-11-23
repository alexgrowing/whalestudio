import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerHaarEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerHaarIntegralAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerHaarUnfoldingStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem GlobalTheory.ConeSmallSer.ctSeries : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃ s₁ : ℝ, ∀ T : Set (UA σ G.W.J), GlobalTheory.ConeSmallCT.IsReps T H'.x → ∀ s : ℂ, s₁ < s.re →
      GlobalTheory.ConeSmallCT.LocUnifSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) T → ∃ T₂ T₃ T₄ : UA σ G.W.J → ℂ,
        IsCT H' (fun h => ∑' t : T, GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2) (t.1 * h)) (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2) + T₂ + T₃ + T₄) ∧
        GlobalTheory.ConeSmallCT.HasLawC G₁.W H' X.β (-s + ((a + b + 1 : ℕ) : ℂ) / 2) T₂ ∧
        GlobalTheory.ConeSmallCT.HasLawC G₁.W H' X.α (((b + 2 : ℕ) : ℂ) / 2) T₃ ∧
        GlobalTheory.ConeSmallCT.HasLawC G₁.W H' X.β (((a + 2 : ℕ) : ℂ) / 2) T₄ :=
  by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ'
  obtain ⟨s₁, h₁⟩ := GlobalTheory.T.config_b_stabilizer_haar_eigen hKP F E σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ'
  obtain ⟨s₂, h₂⟩ := GlobalTheory.T.config_b_stabilizer_haar_unfolding hKP F E σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ'
  obtain ⟨s₃, h₃⟩ := GlobalTheory.T.config_b_stabilizer_haar_integral_alt hKP F E σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ'
  refine ⟨max s₁ (max s₂ s₃), ?_⟩
  intro T hTr s hs hsum
  have hs1 : s₁ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs2 : s₂ < s.re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs
  have hs3 : s₃ < s.re := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hs
  obtain ⟨iL, cL⟩ := h₁ T hTr s hs1 hsum
  obtain ⟨iM, T₃, T₄, cM, l₃, l₄⟩ := h₂ T hTr s hs2 hsum
  obtain ⟨iB, T₂, cB, l₂⟩ := h₃ T hTr s hs3 hsum
  refine ⟨T₂, T₃, T₄, ?_, l₂, l₃, l₄⟩
  set f := GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2) with hf
  have hsplit : (fun h => ∑' t : T, f (t.1 * h)) = GlobalTheory.ConeSmallSer.partSum f (GlobalTheory.ConeSmallSer.lineSet H'.x T) +
      GlobalTheory.ConeSmallSer.partSum f (GlobalTheory.ConeSmallSer.midSet H'.x T) + GlobalTheory.ConeSmallSer.partSum f (GlobalTheory.ConeSmallSer.bigSet H'.x T) := by
    funext h
    obtain ⟨bnd, hb, hbb⟩ := hsum {h} isCompact_singleton
    exact GlobalTheory.ConeSmallSer.tsum_eq_three H'.x T f h (Summable.of_norm_bounded hb fun t => hbb t h rfl)
  have iLM : GlobalTheory.ThK.CTAdd.CTInt H' (GlobalTheory.ConeSmallSer.partSum f (GlobalTheory.ConeSmallSer.lineSet H'.x T) +
      GlobalTheory.ConeSmallSer.partSum f (GlobalTheory.ConeSmallSer.midSet H'.x T)) :=
    (GlobalTheory.ThK.CTAdd.ctIntSub H').add_mem iL iM
  have hall := GlobalTheory.ThK.CTAdd.isCT_add H' iLM iB (GlobalTheory.ThK.CTAdd.isCT_add H' iL iM cL cM) cB
  have heq : f + T₂ + T₃ + T₄ = f + (T₃ + T₄) + T₂ := by abel
  rw [hsplit, heq]
  exact hall

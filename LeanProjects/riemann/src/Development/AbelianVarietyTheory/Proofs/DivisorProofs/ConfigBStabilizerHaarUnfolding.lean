import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviTorusElementCm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorIdeleNormalizedAbsIdeleHalfAtInfinity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarStabilizerPeriodCaseBThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarStabilizerPeriodCaseBFourthStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeSmallMid

theorem midCT : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃ s₁ : ℝ, ∀ T : Set (UA σ G.W.J), GlobalTheory.ConeSmallCT.IsReps T H'.x → ∀ s : ℂ, s₁ < s.re →
      GlobalTheory.ConeSmallCT.LocUnifSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) T →
      GlobalTheory.ThK.CTAdd.CTInt H' (GlobalTheory.ConeSmallSer.partSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) (GlobalTheory.ConeSmallSer.midSet H'.x T)) ∧ ∃ T₃ T₄ : UA σ G.W.J → ℂ, IsCT H' (GlobalTheory.ConeSmallSer.partSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) (GlobalTheory.ConeSmallSer.midSet H'.x T)) (T₃ + T₄) ∧
        GlobalTheory.ConeSmallCT.HasLawC G₁.W H' X.α (((b + 2 : ℕ) : ℂ) / 2) T₃ ∧
        GlobalTheory.ConeSmallCT.HasLawC G₁.W H' X.β (((a + 2 : ℕ) : ℂ) / 2) T₄ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hCfg e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ'
  obtain ⟨s₁a, ha⟩ := GlobalTheory.T.haar_stabilizer_period_case_b_third hKP F E σ B a b G G₁ H H' hCfg e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ'
  obtain ⟨s₁b, hb⟩ := GlobalTheory.T.haar_stabilizer_period_case_b_fourth hKP F E σ B a b G G₁ H H' hCfg e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ'
  refine ⟨max s₁a s₁b, ?_⟩
  intro T hTr s hs hLU
  have hsa : s₁a < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hsb : s₁b < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  refine ⟨ha T hTr s hsa hLU, ?_⟩
  obtain ⟨c, hc, hJ1, hJ2⟩ := hb T hTr s hsb hLU
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.ThK.exists_isLevi F E σ B _ _ G.W G₁.W H' _ _ _ _ hT.base.cm hT.geo.hW hCfg.hH'
    (GlobalTheory.Eis.Conv.halfE F E)
  have habs := GlobalTheory.Eis.Conv.absE_halfE F E σ hT.base.cm
  have hcard : 0 < Fintype.card (InfinitePlace F) := by
    obtain ⟨τ⟩ : Nonempty (F →+* ℂ) := inferInstance
    exact Fintype.card_pos_iff.2 ⟨InfinitePlace.mk τ⟩
  have hr0 : (0 : ℝ) < (absE F E (GlobalTheory.Eis.Conv.halfE F E) : ℝ) := by
    rw [habs]; positivity
  have hr1 : (absE F E (GlobalTheory.Eis.Conv.halfE F E) : ℝ) ≠ 1 := by
    rw [habs]; push_cast
    have h4 : (1 : ℝ) < 4 ^ Fintype.card (InfinitePlace F) := one_lt_pow₀ (by norm_num) hcard.ne'
    intro h1; rw [inv_eq_one] at h1; linarith
  have hlt : b + 2 < a := hT.geo.lt
  have hne := ne_of_re_ne' (u := X.α (GlobalTheory.Eis.Conv.halfE F E)) (v := X.β (GlobalTheory.Eis.Conv.halfE F E)) hr0 hr1
    (w := ((b + 2 : ℕ) : ℂ) / 2) (w' := ((a + 2 : ℕ) : ℂ) / 2) (by
      have e3 : ((b + 2 : ℕ) : ℂ) / 2 = ((((b : ℝ) + 2) / 2 : ℝ) : ℂ) := by push_cast; ring
      have e4 : ((a + 2 : ℕ) : ℂ) / 2 = ((((a : ℝ) + 2) / 2 : ℝ) : ℂ) := by push_cast; ring
      have hab : (b : ℝ) + 2 + 1 ≤ a := by exact_mod_cast hlt
      rw [e3, e4]; simp only [Complex.ofReal_re]; intro h; linarith)
  obtain ⟨T₃, T₄, hTe, h3, h4⟩ := exists_split hJ1 hJ2 hm₀ hne
  exact ⟨T₃, T₄, hTe ▸ hc, h3, h4⟩

end GlobalTheory.ConeSmallMid

end

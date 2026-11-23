import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalGoodPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalGoodPlaceEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalUnramifiedVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalSphericalValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalLocalUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalDeterminedByUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearRightStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.WeilLinA

theorem omA_h_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D : Type}
    [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν β : kˣ →* ℂˣ) (g : GL A k) (Φ : Matrix A D k → ℂ) :
    GlobalTheory.SplitFlip.omA ν β g 1 Φ = GlobalTheory.SplitFlip.omA ν 1 g 1 Φ := by
  funext X; simp [GlobalTheory.SplitFlip.omA]

theorem omA_g_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D : Type}
    [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν β : kˣ →* ℂˣ) (h : GL D k) (Φ : Matrix A D k → ℂ) :
    GlobalTheory.SplitFlip.omA ν β 1 h Φ = GlobalTheory.SplitFlip.omA 1 β 1 h Φ := by
  funext X; simp [GlobalTheory.SplitFlip.omA]

theorem one_mem_UAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (Y : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev := by
  intro u _
  simp [mat]

theorem isSmoothChar_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ : kˣ →* ℂˣ) (h : GlobalTheory.SmGL.IsSmoothChar χ) : GlobalTheory.SmGL.IsSmoothChar χ⁻¹ := by
  have e : (χ⁻¹).ker = χ.ker := by ext x; simp [MonoidHom.mem_ker]
  unfold GlobalTheory.SmGL.IsSmoothChar at h ⊢
  rw [e]; exact h

theorem isUnitaryChar_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ : kˣ →* ℂˣ) (h : GlobalTheory.SmGL.IsUnitaryChar χ) : GlobalTheory.SmGL.IsUnitaryChar χ⁻¹ := by
  intro x
  have := h x
  simp [this]

theorem localOps_eq_omA : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∃ (ν₀ β₀ : (Fv F v)ˣ →* ℂˣ) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)),
      (∃ t : E →ₐ[F] Fv F v, ν₀ = chrW X.ν t ∨ ν₀ = (chrW X.ν t)⁻¹) ∧
      GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧ GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ ∧
      Set.BijOn ι (SB (Fin a × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) : Set _) ∧
      (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ →
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ g' 1 (ι φ)) ∧
      (∀ g' : GL (Fin a) (Fv F v), ∃ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ g' 1 (ι φ)) ∧
      (∀ h' : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h' (ι φ)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hv
  obtain ⟨t, ι, hι⟩ := GlobalTheory.T.exists_linear_functional_good_place hP F E σ B a a' G X om om' hTr v hv
  obtain ⟨ν₀, hV⟩ := GlobalTheory.T.linear_weil_functional_spherical_value hP F E σ B a a' G X om om' hTr v hv t ι hι (GlobalTheory.T.linear_weil_functional_good_place_equivariant hP F E σ B a a' G X om om' hTr v hv t ι hι)
  obtain ⟨t', ht'⟩ := GlobalTheory.T.linear_weil_functional_local_uniqueness hP F E σ B a a' G X om om' hTr v hv t ι hι ν₀ hV
  obtain ⟨β₀, hW⟩ := GlobalTheory.T.linear_weil_functional_translation_equivariant hP F E σ B a a' G X om om' hTr v hv t ι hι (GlobalTheory.T.linear_weil_functional_unramified_vector hP F E σ B a a' G X om om' hTr v hv t ι hι)
  obtain ⟨hβs, hβu⟩ := GlobalTheory.T.linear_weil_functional_determined_by_unramified hP F E σ B a a' G X om om' hTr v hv t ι hι β₀ hW
  obtain ⟨hs, hu⟩ := GlobalTheory.T.local_character_smooth_unitary hP F E σ B a a' G X om om' hTr v hv t'
  have hνs : GlobalTheory.SmGL.IsSmoothChar ν₀ := by
    rcases ht' with h | h
    · rw [h]; exact hs
    · rw [h]; exact isSmoothChar_inv _ hs
  have hνu : GlobalTheory.SmGL.IsUnitaryChar ν₀ := by
    rcases ht' with h | h
    · rw [h]; exact hu
    · rw [h]; exact isUnitaryChar_inv _ hu
  have hloc := ((GlobalTheory.T.theta_action_exists hP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1 v).1
  refine ⟨ν₀, β₀, ι, ⟨t', ht'⟩, hνs, hνu, hβs, hβu, hι.bij, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', -, hg'⟩ := hV g hg
    exact ⟨g', fun φ hφ φ₁ hφ₁ hA => by rw [hg' φ hφ φ₁ hφ₁ hA, omA_h_one ν₀ β₀]⟩
  · intro g'
    obtain ⟨g, hg, hgt⟩ := GlobalTheory.T.local_unitary_group_surjects_general_linear hP F E σ B a a' G X om om' hTr v hv t g'
    refine ⟨g, hg, fun φ hφ => ?_⟩
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc g hg 1 (one_mem_UAt σ G.W _) φ hφ
    obtain ⟨g'', hg'', hgeq⟩ := hV g hg
    have : g'' = g' := Units.ext (hg''.symm.trans hgt)
    subst this
    exact ⟨φ₁, hφ₁, hA, by rw [hgeq φ hφ φ₁ hφ₁ hA, omA_h_one ν₀ β₀]⟩
  · intro h'
    obtain ⟨h, hh, hht⟩ := GlobalTheory.T.local_unitary_group_surjects_general_linear_right hP F E σ B a a' G X om om' hTr v hv t h'
    refine ⟨h, hh, fun φ hφ => ?_⟩
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc 1 (one_mem_UAt σ G.V _) h hh φ hφ
    obtain ⟨h'', hh'', hheq⟩ := hW h hh
    have : h'' = h' := Units.ext (hh''.symm.trans hht)
    subst this
    exact ⟨φ₁, hφ₁, hA, by rw [hheq φ hφ φ₁ hφ₁ hA, omA_g_one ν₀ β₀]⟩

end GlobalTheory.WeilLinA

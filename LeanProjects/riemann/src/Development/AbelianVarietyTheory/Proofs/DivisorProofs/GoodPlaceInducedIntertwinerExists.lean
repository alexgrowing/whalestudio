import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipAugLeJacKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteMapsSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSubmoduleFirstFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedTwoBlockEquivStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit

noncomputable section

namespace GlobalTheory.ZetaCoinvSplit

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1600000 in

theorem zeta_coinv : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ v, X.Good v → ∀ t : E →ₐ[F] Fv F v,
    ∃ (P : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] IndAA (Fv F v) a a' ![chrW X.α t, chrW X.β t])
      (c : GL (Fin (a + a')) (Fv F v)),
      (∀ f, ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), P φ = f) ∧
      (∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), P φ = 0 → φ ∈ augAt om v) ∧
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁) ∧
      ∀ h ∈ UAt σ G.W (evFin F v), ∀ g : GL (Fin (a + a')) (Fv F v),
        (mat h).map (piW t) = ((c * g * c⁻¹ : GL (Fin (a + a')) (Fv F v)) : Matrix (Fin (a + a')) (Fin (a + a')) (Fv F v)) →
        ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om (1, h)) φ φ₁ → P φ₁ = indAA (Fv F v) a a' ![chrW X.α t, chrW X.β t] g (P φ) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT v hv t
  classical
  have hP : GlobalTheory.FunPr.Hypotheses₂ := hKP.base
  have hvT : v ∉ X.T := hv.1
  haveI := hT.geo.hV.lat
  haveI := hT.geo.hW.lat
  obtain ⟨b, hb⟩ := exists_isSplitBasis t G.V.L hT.base.cm
  obtain ⟨c, hc⟩ := exists_isSplitBasis t G.W.L hT.base.cm
  obtain ⟨ι, hι, -⟩ := GlobalTheory.T.split_basis_witt_model_local hP F E σ B _ _ _ _ _ _ _ om _ _ _ _ (GlobalTheory.KSplit.isPair_big hT) v t b c hb hc
  obtain ⟨hα, -, hrα⟩ := GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.α hT.chars.heckeα v t
  obtain ⟨hβ, -, hrβ⟩ := GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.β hT.chars.heckeβ v t
  have hw : splitPrime t ∉ above E (X.T : Set (Pl F)) := by
    show ¬ (splitPrime t).under (𝓞 F) ∈ (X.T : Set (Pl F))
    rw [splitPrime_under]
    exact hvT
  have uα := hrα.2 (hT.chars.unrα _ hw)
  have uβ := hrβ.2 (hT.chars.unrβ _ hw)
  have uν : GlobalTheory.SplitWeil.IsUnram (chrW X.α t / chrW X.β t) := fun x hx => by
    rw [MonoidHom.div_apply, uα x hx, uβ x hx, div_one]
  obtain ⟨l, hl, hl1⟩ := GlobalTheory.T.unramified_character_normalized_equivariant_functional (Fv F v) a _ (((a + a' : ℕ) : ℂ) / 2) (hα.div hβ) uν
  set α := chrW X.α t with hαd
  set β := chrW X.β t with hβd
  have hbij := Model.IsLin.bij hι
  have m : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ι φ ∈ GlobalTheory.SplitWeil.SB _ := fun φ h => hbij.mapsTo h
  have hI := GlobalTheory.T.induced_representation_irreducible hP.bernsteinUnitaryProductIrreducible (Fv F v) a a' α β hα hβ
  obtain ⟨p, hp⟩ := GlobalTheory.KSplit.exists_linear_ext (SB _) (GlobalTheory.KSplit.indSp a a' α β)
    (fun φ => GlobalTheory.KSplit.mapA a' l (α / β) β (ι φ))
    (fun φ h => GlobalTheory.T.intertwining_map_into_induced_left _ a a' α β l hβ hl _ (m φ h))
    (fun φ h φ' h' => by simp only [map_add]; exact GlobalTheory.KSplit.mapA_add hl (m φ h) (m φ' h'))
    (fun z φ h => by simp only [map_smul]; exact GlobalTheory.KSplit.mapA_smul hl z (m φ h))
  have act := fun g hg h hh φ hφ φ₁ hφ₁ H => GlobalTheory.T.linear_witt_model_unitary_action hP F E σ B _ _ _ _ _ _ _ om _ _ _ _
    (GlobalTheory.KSplit.isPair_big hT) v t b c ι hι g hg h hh φ hφ φ₁ hφ₁ H
  rw [GlobalTheory.KSplit.chrW_div, inv_div, ← hαd, ← hβd] at act
  have tr : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ →
      (p φ₁ : GL (Fin (a + a')) (Fv F v) → ℂ) = fun y => (p φ : GL (Fin (a + a')) (Fv F v) → ℂ) (y * GlobalTheory.KSplit.locMat t c h) :=
    fun h hh φ hφ φ₁ hφ₁ H => by
      funext y
      rw [hp _ hφ₁, hp _ hφ, act 1 (GlobalTheory.KSplit.one_mem_UAt _ v) h hh φ hφ φ₁ hφ₁ H, map_one,
        GlobalTheory.KSplit.mapA_omA_right]
  have ne : ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), p φ ≠ 0 := by
    obtain ⟨Φ, hΦ, h0⟩ := GlobalTheory.KSplit.mapA_ne_zero (a' := a') (ν := α / β) (β := β) (l := l)
      ⟨_, GlobalTheory.KSplit.indicator_intM_mem_SB, hl1 ▸ one_ne_zero⟩
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΦ
    exact ⟨φ, hφ, fun h => h0 (by rw [← hp φ hφ, h]; rfl)⟩
  have onto : (SB (Fin a × Fin (a + a') → Fv F v)).map p = ⊤ := GlobalTheory.KSplit.map_eq_top _ _ hI p (fun φ hφ x => by
    obtain ⟨φ₁, h1, h2⟩ := hbij.surjOn (GlobalTheory.SplitFlip.omA_mem_SB (α / β) β 1 x (m φ hφ))
    exact ⟨φ₁, h1, funext fun y => by rw [hp _ h1, hp _ hφ, h2, GlobalTheory.KSplit.mapA_omA_right]⟩) ne
  have inv : augAt om v ≤ LinearMap.ker p := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, φ, hφ, φ₁, hφ₁, H, rfl⟩
    refine LinearMap.mem_ker.2 ?_
    rw [map_sub, sub_eq_zero]
    refine Subtype.ext ?_
    rw [hp _ hφ₁, hp _ hφ, act g hg 1 (GlobalTheory.KSplit.one_mem_UAt _ v) φ hφ φ₁ hφ₁ H, map_one,
      GlobalTheory.KSplit.mapA_omA_left hl _ (m φ hφ)]
  have augSB : augAt om v ≤ SB (Fin a × Fin (a + a') → Fv F v) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact sub_mem hφ₁ hφ
  obtain ⟨e, he⟩ := GlobalTheory.T.induced_two_block_equiv (Fv F v) a a' α β
  refine ⟨e.toLinearMap ∘ₗ p, c, ?_, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨φ, hφ, hpφ⟩ : e.symm f ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map p := onto ▸ Submodule.mem_top
    exact ⟨φ, hφ, by simp [hpφ]⟩
  · intro φ hφ h0
    have h0' : p φ = 0 := e.injective (by simpa using h0)
    have hgood := GlobalTheory.T.character_at_uniformizer_not_root_of_unity F E σ B a a' G X om om' hT v hv
    rcases GlobalTheory.T.augmentation_submodule_first_factor hP F E σ B a a' G X om om' hT v hv hgood (LinearMap.ker p ⊓ SB _) (le_inf inv augSB)
        inf_le_right (fun h hh ψ hψ ψ₁ hψ₁ H => ⟨LinearMap.mem_ker.2 (Subtype.ext (by
          rw [tr h hh ψ hψ.2 ψ₁ hψ₁ H, LinearMap.mem_ker.1 hψ.1]
          rfl)), hψ₁⟩) with hN | hN
    · exact hN.le ⟨h0', hφ⟩
    · exfalso
      obtain ⟨ψ, hψ, hne⟩ := ne
      have : ψ ∈ LinearMap.ker p ⊓ SB _ := hN.ge hψ
      exact hne this.1
  · intro h hh φ hφ
    obtain ⟨φ₁, ⟨h1, H⟩, -⟩ := (GlobalTheory.T.theta_action_exists hP F E σ B _ _ _ _ _ _ _ om _ _ _ _ (GlobalTheory.KSplit.isPair_big hT) v).1 1
      (GlobalTheory.KSplit.one_mem_UAt _ v) h hh φ hφ
    exact ⟨φ₁, h1, H⟩
  · intro h hh g hg φ hφ φ₁ hφ₁ H
    have hlm : GlobalTheory.KSplit.locMat t c h = g := by
      ext1
      rw [GlobalTheory.KSplit.locMat_val, hg]
      simp [Matrix.mul_assoc]
    apply Subtype.ext
    apply Subtype.ext
    funext y
    show (e (p φ₁)).1.1 y = (e (p φ)).1.1 (y * g)
    rw [he, he, tr h hh φ hφ φ₁ hφ₁ H, hlm]

end GlobalTheory.ZetaCoinvSplit

end

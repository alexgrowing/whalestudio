import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedTensorSchwartzFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictedTensorRepresentativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleTransferAlongConfigAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleTransferAlongConfigASecondStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

theorem GlobalTheory.ThK.exists_local_data_cone_ne_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      ei ≠ 0 → (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ (μKi : Measure (KAt K (evI F))) (μi : Measure (idelesAt E (evI F))) (μKf : ∀ v : Pl F, Measure (KAt K (evFin F v)))
      (μf : ∀ v : Pl F, Measure (idelesAt E (evFin F v))), IsNormK K (evI F) μKi → μi.IsHaarMeasure →
      (∀ v, IsNormK K (evFin F v) (μKf v)) → (∀ v, IsNormE E v (μf v)) → ∀ T : Finset (Pl F), X.T ⊆ T →
    ∀ (f₁ : SInf F (Fin b × Fin (b + a'))) (φ₁ : ∀ v : Pl F, (Fin b × Fin (b + a') → Fv F v) → ℂ) (h₁ : UA σ G₁.W.J),
      (∀ v, φ₁ v ∈ SB _) → (∀ v ∉ T, φ₁ v = G₁.M.vac v) → G₁.M.I om₁ (pure f₁ φ₁) h₁ ≠ 0 →
      ∃ f ∈ G.M.Pol B.ψ B.emb, ∃ φ : ∀ v : Pl F, (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ,
        (∀ v, φ v ∈ SB _) ∧ (∀ v ∉ T, φ v = G.M.vac v) ∧
        G₁.M.I om₁ (pure (coneInf B G.M om ei K μKi μi (shiftA H H') X.ν ((b + 2 - a') / 2) f) (fun v => if v ∈ T then coneFin B G.M om v (ev v) K (μKf v) (μf v) (shiftA H H') X.ν ((b + 2 - a') / 2) (φ v) else G₁.M.vac v)) h₁ ≠ 0 := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hCfg hT hT₁ e he ei ev hei hev hfac K hK μKi μi μKf μf
    hμKi hμi hμKf hμf T hXT f₁ φ₁ h₁ hφ₁ hφ₁T hI
  have hcof : ∀ᶠ v in cofinite, φ₁ v = G₁.M.vac v :=
    (T.finite_toSet.eventually_cofinite_notMem).mono fun v hv => hφ₁T v hv
  obtain ⟨l, hl, hlinv⟩ := GlobalTheory.T.exists_restricted_tensor_representative hKP F E σ B b a' G₁ X om₁ om₁' hT₁ φ₁ h₁ hφ₁ hcof
  have hl0 : l ≠ 0 := fun h0 => hI (by rw [← hl f₁, h0, ContinuousLinearMap.zero_apply])
  obtain ⟨f, hfPol, hf⟩ := GlobalTheory.T.triple_transfer_along_config_a_second hKP F E σ B b a' G G₁ H H' X om om' om₁ om₁' hCfg hT hT₁ e he ei ev hei
    hev hfac K hK μKi μi hμKi hμi l hl0 hlinv
  rw [hl] at hf
  set fI := coneInf B G.M om ei K μKi μi (shiftA H H') X.ν ((b + 2 - a') / 2) f with hfI
  set cF : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) → (Fin b × Fin (b + a') → Fv F v) → ℂ :=
    fun v => coneFin B G.M om v (ev v) K (μKf v) (μf v) (shiftA H H') X.ν ((b + 2 - a') / 2) with hcF
  have hvac : ∀ v, G.M.vac v ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) := fun v => (hT.geo.hM.vac v).1
  have key : ∀ S : Finset (Pl F), S ⊆ T → ∃ φ : ∀ v : Pl F, (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ,
      (∀ v, φ v ∈ SB _) ∧ (∀ v ∉ T, φ v = G.M.vac v) ∧ (∀ v ∈ S, cF v (φ v) ∈ SB _) ∧
      G₁.M.I om₁ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure fI (fun v => if v ∈ S then cF v (φ v) else φ₁ v)) h₁ ≠ 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨G.M.vac, hvac, fun _ _ => rfl, fun v hv => absurd hv (Finset.notMem_empty v), ?_⟩
      have e0 : (fun v => if v ∈ (∅ : Finset (Pl F)) then cF v (G.M.vac v) else φ₁ v) = φ₁ :=
        funext fun v => if_neg (Finset.notMem_empty v)
      rw [e0]
      exact hf
    | @insert a s han ih =>
      intro hsub
      have haT : a ∈ T := hsub (Finset.mem_insert_self a s)
      obtain ⟨φ, hφSB, hφT, hφs, hIs⟩ := ih ((Finset.subset_insert a s).trans hsub)
      set φ' : ∀ v : Pl F, (Fin b × Fin (b + a') → Fv F v) → ℂ := fun v => if v ∈ s then cF v (φ v) else φ₁ v with hφ'
      have hφ'SB : ∀ w, φ' w ∈ SB _ := fun w => by
        by_cases hw : w ∈ s
        · simp only [hφ', if_pos hw]; exact hφs w hw
        · simp only [hφ', if_neg hw]; exact hφ₁ w
      have hφ'cof : ∀ᶠ w in cofinite, φ' w = G₁.M.vac w :=
        (T.finite_toSet.eventually_cofinite_notMem).mono fun w hw => by
          have hws : w ∉ s := fun h => hw (hsub (Finset.mem_insert_of_mem h))
          simp only [hφ', if_neg hws]; exact hφ₁T w hw
      obtain ⟨hadd, hsmul, hinv⟩ := GlobalTheory.T.restricted_tensor_schwartz_function hKP F E σ B b a' G₁ X om₁ om₁' hT₁ fI φ' h₁ a hφ'SB hφ'cof
      have hupd : Function.update φ' a (φ₁ a) = φ' := by
        funext w
        by_cases hw : w = a
        · subst hw; rw [Function.update_self]; simp only [hφ', if_neg han]
        · rw [Function.update_of_ne hw]
      obtain ⟨p, hpSB, hcp, hne⟩ := GlobalTheory.T.triple_transfer_along_config_a hKP F E σ B b a' G G₁ H H' X om om' om₁ om₁' hCfg hT hT₁ e he ei ev
        hei hev hfac K hK a (μKf a) (μf a) (hμKf a) (hμf a)
        (fun q => G₁.M.I om₁ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure fI (Function.update φ' a q)) h₁) hadd hsmul
        ⟨φ₁ a, hφ₁ a, by simp only [hupd]; exact hIs⟩ hinv
      refine ⟨Function.update φ a p, fun w => ?_, fun w hw => ?_, fun w hw => ?_, ?_⟩
      · by_cases hw : w = a
        · subst hw; rw [Function.update_self]; exact hpSB
        · rw [Function.update_of_ne hw]; exact hφSB w
      · have hwa : w ≠ a := fun h => hw (h ▸ haT)
        rw [Function.update_of_ne hwa]; exact hφT w hw
      · by_cases hwa : w = a
        · subst hwa; rw [Function.update_self]; exact hcp
        · rw [Function.update_of_ne hwa]
          exact hφs w ((Finset.mem_insert.1 hw).resolve_left hwa)
      · have e1 : (fun w => if w ∈ insert a s then cF w (Function.update φ a p w) else φ₁ w) =
            Function.update φ' a (cF a p) := by
          funext w
          by_cases hwa : w = a
          · subst hwa; rw [Function.update_self, Function.update_self, if_pos (Finset.mem_insert_self _ _)]
          · rw [Function.update_of_ne hwa, Function.update_of_ne hwa]
            simp only [hφ', Finset.mem_insert, hwa, false_or]
        rw [e1]
        exact hne
  obtain ⟨φ, h1, h2, -, h4⟩ := key T subset_rfl
  refine ⟨f, hfPol, φ, h1, h2, ?_⟩
  have e2 : (fun v => if v ∈ T then cF v (φ v) else G₁.M.vac v) = (fun v => if v ∈ T then cF v (φ v) else φ₁ v) := by
    funext v
    by_cases hv : v ∈ T
    · rw [if_pos hv, if_pos hv]
    · rw [if_neg hv, if_neg hv, hφ₁T v hv]
  show G₁.M.I om₁ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure fI (fun v => if v ∈ T then cF v (φ v) else G₁.M.vac v)) h₁ ≠ 0
  rw [e2]
  exact h4

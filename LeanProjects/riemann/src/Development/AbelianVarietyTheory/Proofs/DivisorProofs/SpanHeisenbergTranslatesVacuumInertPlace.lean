import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertLocalUniformizerImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerTranslatesSpanSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

open scoped GlobalTheory.VacAny

namespace GlobalTheory.InertSpan

theorem span_translates_vac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (AE F E))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∀ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v →
      Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw _ L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ s hs
  obtain ⟨-, -, -, -, -, -, -, -, -, hAt, hSurj, -⟩ := hC
  have hunr : PsiUnr B.ψ v := (hT.base.inert v w hw).2.2
  have hvac := hT.geo.hM'.vac v
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v
  have key : ∀ x, ((ρ x s : SB _) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) =
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (κ x)) (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
    fun x => GlobalTheory.InertAvg.tens_inj v R hR0 (hR _ s.2).1
      ((hρ x s R (hR _ s.2)).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo _ _ v _ (hAt x) _ R (hR _ s.2)))
  have hsurj : ∀ p : (Fin a' × Fin (a + a') → Fv F v) × (Fin a' × Fin (a + a') → Fv F v),
      ∃ x, GlobalTheory.LatVac.locCo G.M'.co v (κ x) = p := by
    intro p
    obtain ⟨x, hx⟩ := hSurj (G.M'.co.e.symm (fun k => GlobalTheory.LatVac.liftV v (p.1 k), fun k => GlobalTheory.LatVac.liftV v (p.2 k)))
      (by
        intro u hu
        rw [← LinearEquiv.map_smul]
        convert G.M'.co.e.symm.map_zero using 2
        ext k
        · exact GlobalTheory.LatVac.at_liftV v (p.1 k) u hu
        · exact GlobalTheory.LatVac.at_liftV v (p.2 k) u hu)
    refine ⟨x, ?_⟩
    rw [hx]
    ext k
    · simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]
    · simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]
  have hs0 : (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ≠ 0 := hs ▸ hvac.2.1
  have hcond : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) ↔
      x ∈ v.adicCompletionIntegers F := hunr
  have hrange : Set.range (fun p => schr (GlobalTheory.LatVac.psiAt B.ψ v) p (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) =
      (SB (Fin a' × Fin (a + a') → Fv F v)).subtype '' Set.range (fun x => ρ x s) := by
    ext f
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨x, hx⟩ := hsurj p
      exact ⟨ρ x s, ⟨x, rfl⟩, by rw [Submodule.subtype_apply, key, hx]⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, (key x).symm⟩
  rw [eq_top_iff]
  rintro m -
  have hm := GlobalTheory.SchrSpan.mem_span_schr_of_mem_SB F v (GlobalTheory.LatVac.psiAt B.ψ v) _ hcond _ s.2 hs0 _ m.2
  rw [hrange, Submodule.span_image] at hm
  obtain ⟨n, hn, hnm⟩ := hm
  rwa [← Subtype.ext hnm]

end GlobalTheory.InertSpan

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalInvarianceFirstOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LemF.InfLevi

theorem ei_levi : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (g₀ : UA σ G₁.V.J) (g : UA σ G.V.J), IsLevi H 1 g₀ g → g ∈ UAt σ G.V (evI F) → g₀ ∈ UAt σ G₁.V (evI F) →
      ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')), ei (locOpInf (om (g, 1)) f) = locOpInf (om₁ (g₀, 1)) (ei f) := by
  intro hP F E _ _ _ _ _ σ B b a' G G₁ H H' cfg e hev ei ev hloc X om om' om₁ om₁' T T₁ g₀ g hLv hg hg₀ f
  have hL := (EvInvALoc.global_laws hP F E σ B b a' G G₁ H H' cfg e hev X om om' om₁ om₁' T T₁).2 g₀ g hLv
  have hM := T.geo.hM
  have hM₁ := T₁.geo.hM
  obtain ⟨-, hevv, hpure⟩ := hloc

  have hfin : ∀ {κ : Type} [Fintype κ] (z : κ → AF F), At (evI F) z → ∀ (w : Pl F) (i : κ), evFin F w (z i) = 0 :=
    fun z hz w i => by
      rw [← partInf_of_at hz, partInf, Pi.smul_apply, smul_eq_mul, map_mul,
        show evFin F w (realAd F 1) = 0 from map_zero (evalV F w), zero_mul]
  let r₀ : (Fin (b + 2) × Fin (b + 2 + a') → AF F) → ℂ := fun x => ∏ᶠ w, G.M.vac w fun i => evFin F w (x i)
  let r₁ : (Fin b × Fin (b + a') → AF F) → ℂ := fun x => ∏ᶠ w, G₁.M.vac w fun i => evFin F w (x i)
  have hr₀ : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := fun x z hz => by
    simp only [r₀, Pi.add_apply, map_add, hfin z hz, add_zero]
  have hr₁ : ∀ x z, At (evI F) z → r₁ (x + z) = r₁ x := fun x z hz => by
    simp only [r₁, Pi.add_apply, map_add, hfin z hz, add_zero]
  have ht₀ : ∀ h : SInf F (Fin (b + 2) × Fin (b + 2 + a')), tens (evI F) ⇑h r₀ = pure h G.M.vac := fun h => rfl
  have ht₁ : ∀ h : SInf F (Fin b × Fin (b + a')), tens (evI F) ⇑h r₁ = pure h G₁.M.vac := fun h => rfl
  have hS₀ : ∀ h : SInf F (Fin (b + 2) × Fin (b + 2 + a')), pure h G.M.vac ∈ schA F _ := fun h =>
    GlobalTheory.TensUniq.pure_mem_schA h _ (fun w => (hM.vac w).1) hM.std
  have hS₁ : ∀ h : SInf F (Fin b × Fin (b + a')), pure h G₁.M.vac ∈ schA F _ := fun h =>
    GlobalTheory.TensUniq.pure_mem_schA h _ (fun w => (hM₁.vac w).1) hM₁.std
  have hR₀ : ∀ h : SInf F (Fin (b + 2) × Fin (b + 2 + a')), Rest (evI F) ⇑h r₀ := fun h => ⟨hr₀, hS₀ h⟩
  have hR₁ : ∀ h : SInf F (Fin b × Fin (b + a')), Rest (evI F) ⇑h r₁ := fun h => ⟨hr₁, hS₁ h⟩

  have hep : ∀ h : SInf F (Fin (b + 2) × Fin (b + 2 + a')), e (pure h G.M.vac) = pure (ei h) G₁.M.vac := fun h => by
    rw [hpure h G.M.vac (fun w => (hM.vac w).1) (Eventually.of_forall fun _ => rfl)]
    congr 1
    funext w
    exact (hevv w).1

  obtain ⟨f₁, hf₁⟩ := GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ (b + 2) (b + 2 + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om
    T.base.cm T.base.std T.weil g hg f
  obtain ⟨h₁, hh₁⟩ := GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ b (b + a') G₁.V G₁.W G₁.M B.ψ X.β (X.β / X.α) om₁
    T₁.base.cm T₁.base.std T₁.weil g₀ hg₀ (ei f)
  rw [locOpInf_eq hf₁, locOpInf_eq hh₁]
  have k : pure (ei f₁) G₁.M.vac = pure h₁ G₁.M.vac := by
    have a1 := hf₁ r₀ (hR₀ f)
    have a2 := hh₁ r₁ (hR₁ (ei f))
    rw [ht₀, ht₀] at a1
    rw [ht₁, ht₁] at a2
    rw [← hep, ← a1, hL _ (hS₀ f), hep, a2]
  by_contra hne
  refine GlobalTheory.EvNonzero.pure_ne_zero (ei f₁ - h₁) (sub_ne_zero.2 hne) G₁.M.vac (fun w => (hM₁.vac w).2.1) hM₁.std ?_
  funext x
  have := congrFun k x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.sub_apply, Pi.zero_apply] at this ⊢
  rw [sub_mul, this, sub_self]

end GlobalTheory.ThK.LemF.InfLevi

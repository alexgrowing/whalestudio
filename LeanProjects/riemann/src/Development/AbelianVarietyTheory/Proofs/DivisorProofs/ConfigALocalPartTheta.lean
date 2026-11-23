import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalInvarianceFirstOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerExtension
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.InfUnipA

variable {F : Type} [Field F] [NumberField F]

theorem eq_of_pure_eq' {κ : Type} [Fintype κ] {f f' : SInf F κ} {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ}
    (h0 : ∀ v, φ v ≠ 0) (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ) : f = f' := by
  by_contra hne
  refine GlobalTheory.ThK.EvNeZero.pure_ne_zero (f - f') (sub_ne_zero.2 hne) φ h0 hstd ?_
  funext x
  have := congrFun h x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.sub_apply, Pi.zero_apply, sub_mul] at this ⊢
  rw [this, sub_self]

theorem infUnipA : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ u ∈ unip σ G.V H, u ∈ UAt σ G.V (evI F) → ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
      ei (locOpInf (om (u, 1)) f) = ei f := by
  intro hP F E _ _ _ _ _ σ B b a' G G₁ H H' cfg e hev ei ev hloc X om om' om₁ om₁' T T₁ u hu huI f
  obtain ⟨hU, -⟩ := GlobalTheory.ThK.EvInvALoc.global_laws hP F E σ B b a' G G₁ H H' cfg e hev X om om' om₁ om₁' T T₁
  obtain ⟨-, hevv, hpure⟩ := hloc
  have hM := T.geo.hM
  have hM₁ := T₁.geo.hM
  have hex := GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ (b + 2) (b + 2 + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om
    T.base.cm T.base.std T.weil u huI f
  have hA : Acts (evI F) (om (u, 1)) f (locOpInf (om (u, 1)) f) := acts_locOpInf hex
  have hvacSB : ∀ v, G.M.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hRest : Rest (evI F) f (fun x => ∏ᶠ v, G.M.vac v fun i => evFin F v (x i)) := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · have h : ∀ w i, evFin F w (z i) = 0 := fun w i => by
        rw [← partInf_of_at hz, partInf, Pi.smul_apply, smul_eq_mul, map_mul,
          show evFin F w (realAd F 1) = 0 from map_zero (evalV F w), zero_mul]
      simp only [Pi.add_apply, map_add, h, add_zero]
    · exact GlobalTheory.TensUniq.pure_mem_schA f G.M.vac hvacSB hM.std
  have h1 : om (u, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f G.M.vac) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (locOpInf (om (u, 1)) f) G.M.vac := hA _ hRest
  have hc : ∀ᶠ v in cofinite, G.M.vac v = G.M.vac v := Eventually.of_forall fun _ => rfl
  have key := hU u hu _ hRest.2
  change e (om (u, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f G.M.vac)) = e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f G.M.vac) at key
  rw [h1, hpure _ _ hvacSB hc, hpure _ _ hvacSB hc] at key
  simp only [fun v => (hevv v).1] at key
  exact eq_of_pure_eq' (fun v => (hM₁.vac v).2.1) hM₁.std key

end GlobalTheory.ThK.InfUnipA

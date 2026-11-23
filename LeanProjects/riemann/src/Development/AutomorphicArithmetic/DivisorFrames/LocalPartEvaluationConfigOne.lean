import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
import Development.AutomorphicArithmetic.DivisorFrames.UnipotentSchwartzLocallyConstant
import Development.AutomorphicArithmetic.DivisorFrames.LocalThetaPartitionTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLocallyConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCoefficientTendstoZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceCharacterAnnihilatorCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

theorem UpperTheory.local_part_evaluation_config_one :
    GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
                 (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
                 ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', GlobalTheory.ThK.LemF.IsLocPart G.M' G₁.M' e' ei' ev' →
                 ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F), ∀ l : ((Fin b × Fin (a + b) → Fv F v) → ℂ) →ₗ[ℂ] ℂ, ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
                   (fun s => l (evS B G.M' v (ev' v) H H' φ s)) ∈ SB (Fv F v ⊗[F] E) := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' hE ei' ev' hL X om om' om₁ om₁' hT hT₁ v l φ hφ
  have hψ : Continuous B.ψ := hT.base.std.1
  have hψv : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hψ v
  have hne : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hT.base.std v
  haveI := GlobalTheory.LocTateInt.t2Space_Fv_tensor (E := E) v
  have hU : {t : Fv F v ⊗[F] E | schr (GlobalTheory.LatVac.psiAt B.ψ v)
      (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.VanishLoc.uAt H H' v t)) φ = φ} ∈ nhds 0 :=
    (GlobalTheory.VanishLocCont.tendsto_locCo_uAt G.M' H H' v).eventually
      (GlobalTheory.SchrSmall.schr_eventually_eq v (GlobalTheory.LatVac.psiAt B.ψ v) hψv φ hφ)
  have hK := GlobalTheory.TraceAnnCompact.isCompact_trace_ann v (GlobalTheory.LatVac.psiAt B.ψ v) hψv hne _ hU
  refine ⟨(UpperTheory.unipotent_schwartz_locally_constant F E σ B _ _ _ _ _ _ G.M' H H' hψ v φ hφ).comp (fun f => l (ev' v f)),
    HasCompactSupport.intro hK fun s hs => ?_⟩
  simp only [Set.mem_setOf_eq, not_forall] at hs
  obtain ⟨t, ht, hne1⟩ := hs
  have h1 := UpperTheory.local_theta_partition_triple hP F E σ B a b G G₁ H H' hC e' hE ei' ev' hL X om om' om₁ om₁' hT hT₁ v φ hφ t s
  rw [(locOp_rho G.M'.co hψ v (GlobalTheory.VanishLoc.uAt H H' v t) hφ).2, ht] at h1
  have hne2 : GlobalTheory.LatVac.psiAt B.ψ v (-Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * s)) ≠ 1 := by
    intro h
    apply hne1
    have h3 := (GlobalTheory.LatVac.psiAt B.ψ v).map_add_eq_mul (-Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * s))
      (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * s))
    rw [neg_add_cancel, AddChar.map_zero_eq_one, h, one_mul] at h3
    exact h3.symm
  have h2 : (GlobalTheory.LatVac.psiAt B.ψ v (-Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * s)) - 1) •
      evS B G.M' v (ev' v) H H' φ s = 0 := by
    rw [sub_smul, ← h1, one_smul, sub_self]
  have h4 := (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne2)
  show l (evS B G.M' v (ev' v) H H' φ s) = 0
  rw [h4, map_zero]

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitExistenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaLiftTransfer
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.SpanVSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem thetaInt_add {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W)
    (hpres : ∀ p, ∀ Φ ∈ schA F (Fin n × Fin d), om p Φ ∈ schA F (Fin n × Fin d))
    {Φ Ψ : (Fin n × Fin d → AF F) → ℂ} (hΦ : Φ ∈ schA F _) (hΨ : Ψ ∈ schA F _) (cΦ : M.Conv om Φ) (cΨ : M.Conv om Ψ) :
    M.I om (Φ + Ψ) = M.I om Φ + M.I om Ψ := by
  funext h
  simp only [Model.I, Pi.add_apply]
  rw [← integral_add (cΦ h) (cΨ h)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g => GlobalTheory.ThK.SqIntCont.theta_add om hpres hΦ hΨ g h)

theorem thetaInt_smul {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (z : ℂ)
    (Φ : (Fin n × Fin d → AF F) → ℂ) : M.I om (z • Φ) = z • M.I om Φ := by
  funext h
  simp only [Model.I, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g => GlobalTheory.ThK.SqIntCont.theta_smul om z _ g h)

theorem polData_of_polMatch {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {R : RealMaps F a a'}
    {Rf : FinMaps F a a'} {Φ : (Fin a × Fin (a + a') → AF F) → ℂ} {Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ}
    (hPM : PolMatch B G X R Rf Φ Φ') : Φ ∈ PolData B G.M := by
  obtain ⟨T, -, m, m', f, φ, f', φ', hf, -, e1, -, -⟩ := hPM
  refine e1 ▸ Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_
  exact ⟨f i, (hf i).1, φ i, (hf i).2.1,
    Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by_contra fun hT => hv ((hf i).2.2 v hT)), rfl⟩

end GlobalTheory.ThK.SpanVSplit

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarEigenTripleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerHaarEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerHaarUnfoldingStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeMem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem rho_zero' {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {σ : E →ₐ[F] E} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (w : Matrix (Fin n) (Fin d) (AE F E)) : M.co.rho ψ w (0 : (Fin n × Fin d → AF F) → ℂ) = 0 := by
  funext x
  simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

theorem rho_add' {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {σ : E →ₐ[F] E} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (w : Matrix (Fin n) (Fin d) (AE F E)) (a b : (Fin n × Fin d → AF F) → ℂ) :
    M.co.rho ψ w (a + b) = M.co.rho ψ w a + M.co.rho ψ w b := by
  funext x
  simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]

theorem rho_smul' {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {σ : E →ₐ[F] E} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (w : Matrix (Fin n) (Fin d) (AE F E)) (c : ℂ) (a : (Fin n × Fin d → AF F) → ℂ) :
    M.co.rho ψ w (c • a) = c • M.co.rho ψ w a := by
  funext x
  simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem schA_le_of_pure' {κ : Type} [Fintype κ] {N : Submodule ℂ ((κ → AF F) → ℂ)}
    (h : ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) → pure f φ ∈ N) :
    schA F κ ≤ N := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  replace hg := GlobalTheory.SBSpan.mem_span_restrictedProd F _ g hg
  induction hg using Submodule.span_induction with
  | zero => rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _]; exact N.zero_mem
  | add a b _ _ ha hb =>
    rw [show pureA F f (a + b) = pureA F f a + pureA F f b from funext fun _ => mul_add _ _ _]; exact N.add_mem ha hb
  | smul c a _ ha =>
    rw [show pureA F f (c • a) = c • pureA F f a from funext fun _ => mul_left_comm _ _ _]; exact N.smul_mem c ha
  | mem p hp =>
    obtain ⟨φ, hφ, hs, rfl⟩ := hp
    exact h f φ hφ hs

theorem cone_mem_schA : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Ψ ∈ schA F (Fin b × Fin (b + a')) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e hE X om om' om₁ om₁' hT hT₁
  have hpres : ∀ (x : UA σ G.V.J × UA σ G.W.J), ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), om x Φ ∈ schA F _ :=
    fun x Φ hΦ => (IsUWeilPair.isUSplitting hT.weil).pres x Φ hΦ
  have hzero : cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) 0 = 0 := by
    funext y
    simp [cone, rho_zero']
  have hadd : ∀ Φ₁ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ Φ₂ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (Φ₁ + Φ₂) =
        cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Φ₁ +
          cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Φ₂ := by
    intro Φ₁ h₁ Φ₂ h₂
    funext y
    simp only [cone, Pi.add_apply]
    rw [← integral_add (GlobalTheory.T.config_a_stabilizer_haar_eigen hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e hE X om om' om₁ om₁' hT hT₁ Φ₁ h₁ y)
      (GlobalTheory.T.config_a_stabilizer_haar_eigen hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e hE X om om' om₁ om₁' hT hT₁ Φ₂ h₂ y)]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    beta_reduce
    rw [← integral_add (GlobalTheory.T.config_a_haar_eigen_triple hKP F E σ B b a' G G₁ H H' hC μ hμ e hE X om om' om₁ om₁' hT hT₁ _ (hpres _ _ h₁) y)
      (GlobalTheory.T.config_a_haar_eigen_triple hKP F E σ B b a' G G₁ H H' hC μ hμ e hE X om om' om₁ om₁' hT hT₁ _ (hpres _ _ h₂) y)]
    refine integral_congr_ae (Eventually.of_forall fun l => ?_)
    beta_reduce
    rw [map_add, rho_add', map_add, Pi.add_apply]
    ring
  have hsmul : ∀ (c : ℂ) (Φ : (Fin (b + 2) × Fin (b + 2 + a') → AF F) → ℂ),
      cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (c • Φ) =
        c • cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Φ := by
    intro c Φ
    funext y
    simp only [cone, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    beta_reduce
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun l => ?_)
    beta_reduce
    rw [map_smul, rho_smul', map_smul, Pi.smul_apply, smul_eq_mul]
    ring
  let N : Submodule ℂ ((Fin (b + 2) × Fin (b + 2 + a') → AF F) → ℂ) :=
    { carrier := {Φ | Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) ∧
        cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Φ ∈ schA F (Fin b × Fin (b + a'))}
      zero_mem' := ⟨Submodule.zero_mem _, by rw [hzero]; exact Submodule.zero_mem _⟩
      add_mem' := fun {Φ₁ Φ₂} h₁ h₂ => ⟨Submodule.add_mem _ h₁.1 h₂.1, by
        rw [hadd Φ₁ h₁.1 Φ₂ h₂.1]; exact Submodule.add_mem _ h₁.2 h₂.2⟩
      smul_mem' := fun c {Φ} h => ⟨Submodule.smul_mem _ c h.1, by
        rw [hsmul c Φ]; exact Submodule.smul_mem _ c h.2⟩ }
  have hle : schA F (Fin (b + 2) × Fin (b + 2 + a')) ≤ N := by
    refine schA_le_of_pure' fun f φ hφ hs => ?_
    have hv : ∀ᶠ v in cofinite, φ v = G.M.vac v := (hs.and hT.geo.hM.std).mono fun v h => h.1.trans h.2.symm
    exact ⟨GlobalTheory.TensUniq.pure_mem_schA f φ hφ hs,
      GlobalTheory.T.config_a_stabilizer_haar_unfolding hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e hE X om om' om₁ om₁' hT hT₁ f φ hφ hv⟩
  exact fun Ψ hΨ => (hle hΨ).2

end GlobalTheory.ConeMem

end

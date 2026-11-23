import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLocalApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaGoodPlaceLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLatticeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeilTransferW

theorem augAt_stable_W : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ augAt om' v, ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ → φ₁ ∈ augAt om' v := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v h hh φ hφ φ₁ hφ₁ hact
  obtain ⟨S, hS, hlin, -, -⟩ := local_weil_operator_second_space hP F E σ B a a' G X om om' hT v h hh
  have hone : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := fun u _ => by simp [mat]
  obtain ⟨hex, -, -⟩ := GlobalTheory.T.theta_action_exists hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' G.q (a' - G.q)
    (a + a' - (G.p + G.q)) (G.p + G.q) (GlobalTheory.ThK.Inhab.pairV' hT) v
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a' × Fin (a + a')) v
  have eqR : ∀ φ₁ φ₂ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R → φ₁ = φ₂ := by
    intro φ₁ φ₂ e0
    have hRc := (hR 0 (Submodule.zero_mem _)).1
    funext y
    have hp : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
    have e := congrFun e0 (fun i => GlobalTheory.LatVac.liftV v (y i))
    have e2 : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by simpa using hRc 0 _ hp
    simp only [tens, GlobalTheory.LatVac.evFin_liftV, e2] at e
    exact mul_right_cancel₀ hR0 e
  have hSR : ∀ ψ ∈ SB (Fin a' × Fin (a + a') → Fv F v), om' (1, h) (tens (evFin F v) ψ R) = tens (evFin F v) (S ψ) R :=
    fun ψ hψ => (hS ψ hψ).2 R (hR ψ hψ)
  have hle : augAt om' v ≤ SB (Fin a' × Fin (a + a') → Fv F v) := by
    rw [augAt, Submodule.span_le]
    rintro z ⟨g, -, ψ, hψ, ψ₁, hψ₁, -, rfl⟩
    exact sub_mem hψ₁ hψ
  have hS0 : S 0 = 0 := by
    have e := hlin 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1
    simp only [smul_zero, add_zero, one_smul] at e
    first | exact left_eq_add.1 e | simpa using e
  have hadd : ∀ x ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ y ∈ SB (Fin a' × Fin (a + a') → Fv F v), S (x + y) = S x + S y := by
    intro x hx y hy
    simpa using hlin x hx y hy 1
  have hsmul : ∀ (c : ℂ), ∀ x ∈ SB (Fin a' × Fin (a + a') → Fv F v), S (c • x) = c • S x := by
    intro c x hx
    simpa [hS0] using hlin x hx 0 (Submodule.zero_mem _) c
  have hcomm : ∀ g : UA σ G.V'.J, ∀ f, om' (g, 1) (om' (1, h) f) = om' (1, h) (om' (g, 1) f) := by
    intro g f
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
      mul_one, one_mul, mul_one, one_mul]
  have hgen : ∀ g ∈ UAt σ G.V' (evFin F v), ∀ ψ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ ψ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om' (g, 1)) ψ ψ₁ → Acts (evFin F v) (om' (g, 1)) (S ψ) (S ψ₁) := by
    intro g hg ψ hψ ψ₁ hψ₁ hgψ
    obtain ⟨χ, ⟨hχ, hχa⟩, -⟩ := hex g hg 1 (fun u _ => by simp [mat]) (S ψ) (hS ψ hψ).1
    have e : χ = S ψ₁ := by
      apply eqR
      rw [← hχa R (hR _ (hS ψ hψ).1), ← hSR ψ hψ, hcomm, hgψ R (hR ψ hψ), hSR ψ₁ hψ₁]
    exact e ▸ hχa
  have key : ∀ x (hx : x ∈ augAt om' v), S x ∈ augAt om' v := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, hg, ψ, hψ, ψ₁, hψ₁, hgψ, rfl⟩ := hz
      have e : S (ψ₁ - ψ) = S ψ₁ - S ψ := by
        have := hlin ψ hψ ψ₁ hψ₁ (-1)
        rw [neg_one_smul, neg_one_smul, neg_add_eq_sub, neg_add_eq_sub] at this
        exact this
      rw [e]
      exact Submodule.subset_span ⟨g, hg, S ψ, (hS ψ hψ).1, S ψ₁, (hS ψ₁ hψ₁).1, hgen g hg ψ hψ ψ₁ hψ₁ hgψ, rfl⟩
    | zero => rw [hS0]; exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      rw [hadd x (hle hx) y (hle hy)]; exact add_mem ihx ihy
    | smul c x hx ihx =>
      rw [hsmul c x (hle hx)]; exact Submodule.smul_mem _ c ihx
  have hφSB := hle hφ
  have e : φ₁ = S φ := (hex 1 hone h hh φ hφSB).unique ⟨hφ₁, hact⟩ (hS φ hφSB)
  rw [e]
  exact key φ hφ

end GlobalTheory.WeilTransferW

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalEigenTripleStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.InfB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem locOpInf_om_rho {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    (hψ : IsStd ψ) {χX χW : Chr F E} {om : Rep σ X W} (hW : M.IsWeil ψ χX χW om) {g : UA σ X.J}
    (hex : ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (g, 1)) f f₁)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) :
    locOpInf (M.co.rho ψ (partInf F (mat g * u))) (locOpInf (om (g, 1)) f) =
      locOpInf (om (g, 1)) (locOpInf (M.co.rho ψ (partInf F u)) f) := by
  have hS := IsUWeilPair.isUSplitting hW
  have hact : actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) (partInf F u) = partInf F (mat g * u) := by
    change mat g * (partInf F u) * (mat (1 : UA σ W.J))ᵀ = _
    have h1 : mat (1 : UA σ W.J) = 1 := rfl
    rw [h1, Matrix.transpose_one, Matrix.mul_one, partInf, partInf, Matrix.mul_smul]
  obtain ⟨r, h0, hr⟩ := exists_rest_inf F (Fin n × Fin d)
  refine DFunLike.coe_injective (eq_of_tens_inf h0 (hr f).1 ?_)
  have h2 := hS.impl (g, 1) (partInf F u) _ (hr f).2
  rw [hact, (locOpInf_rho M.co hψ u f).1 r (hr _), acts_locOpInf (hex _) r (hr _), acts_locOpInf (hex _) r (hr _),
    (locOpInf_rho M.co hψ _ _).1 r (hr _)] at h2
  exact h2.symm

omit [NumberField E] in

theorem mat_mul_shiftB {n d n₁ d₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} (H' : Plane E d d₁)
    {t : (AE F E)ˣ} {g₀ : UA σ X₁.J} {m : UA σ X.J} (hm : IsLevi (W₁ := X₁) H t g₀ m) (s : (AE F E)ˣ) :
    mat m * shiftB σ H H' (t * s) = shiftB σ H H' s := by
  rw [shiftB, shiftB, Matrix.mul_smul, Matrix.mul_vecMulVec, hm.2.1, Matrix.smul_vecMulVec, smul_smul, ← map_mul,
    Units.val_mul, mul_comm (t : AE F E), mul_assoc, Units.mul_inv, mul_one]

theorem levi_cone_law : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ t g₀ m, IsLevi (W₁ := G₁.V') H t g₀ m → m ∈ UAt σ G.V' (evI F) → g₀ ∈ UAt σ G₁.V' (evI F) →
    ∀ (s : (AE F E)ˣ) (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))),
      ei' (locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' s))) (locOpInf (om' (m, 1)) f)) =
        fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t •
          locOpInf (om₁' (g₀, 1)) (ei' (locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' (t * s)))) f)) := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he ei' ev' hL X om om' om₁ om₁' hT hT₁ t g₀ m hm hmi hg s f
  have hex := GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ _ _ _ _ G.M' B.ψ _ _ om' hT.base.cm hT.base.std hT.weil' m hmi
  rw [← mat_mul_shiftB H' hm s, locOpInf_om_rho hT.base.std hT.weil' hex]
  exact (GlobalTheory.T.config_b_local_eigen_triple hP F E σ B a b G G₁ H H' hC e' he ei' ev' hL X om om' om₁ om₁' hT hT₁).2 t g₀ m hm hmi hg _

end GlobalTheory.ThK.InfB

end

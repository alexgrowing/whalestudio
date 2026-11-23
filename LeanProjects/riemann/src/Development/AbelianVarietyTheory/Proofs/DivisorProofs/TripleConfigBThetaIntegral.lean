import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEigenIntertwinerTripleFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentHaarDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerDoubleRestrictionStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.StabInvB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def reM {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (Y : Spc F E n) : Model σ (reS X Y) W :=
  ⟨M.co, M.vac, M.μ, M.dom⟩

theorem reM_isGood {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} (Y : Spc F E n) {ψ : AddChar (AF F) ℂ}
    (hM : M.IsGood ψ) : (reM M Y).IsGood ψ :=
  ⟨hM.rat, hM.vac, hM.std, hM.haar, hM.dom⟩

theorem reM_isEv {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}
    {M : Model σ X W} {M₁ : Model σ X₁ W₁} (Y : Spc F E n) {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
    {I : Set (Matrix (Fin n) (Fin d) (AE F E))} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (he : IsEv B M M₁ ι ι' I e) :
    IsEv B (reM M Y) M₁ ι ι' I e :=
  ⟨he.maps, he.Heisenberg₂, he.inv, he.loc⟩

theorem coneTerm_left_inv : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)) (hC : CfgB B G G₁ H H') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁') (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)) (hV₂ : (reS G.V V₂).IsHerm σ B (a - G.p) G.p) (hH₀ : H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁) (hM₂ : M₂.IsGood B.ψ) (hev : IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂) (Φ : Fn F a (a + (b + 2))) (hΦ : Φ ∈ PolData B G.M) (h : UA σ G.W.J) (Q : Subgroup (UA σ G.V.J)) (hQ : ∀ q, q ∈ Q ↔ q ∈ ratU σ G.V.J ∧ mat q *ᵥ incV F H₀.x = incV F H₀.x), ∀ q ∈ Q, ∀ g : UA σ G.V.J, ‖thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (q * g, h) Φ)))‖ₑ = ‖thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (g, h) Φ)))‖ₑ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h Q hQ q hqQ g
  have hq := (hQ q).1 hqQ
  have hP0 := Inhab.pairV hT
  have hP : IsPair B (reM G.M V₂) X.β (X.β / X.α) om (a - G.p) G.p (a + (b + 2) - (G.p + G.q)) (G.p + G.q) :=
    ⟨hP0.base, hV₂, hP0.skew, reM_isGood V₂ hP0.good, hP0.hX, hP0.hW, hP0.resX, hP0.resW, hP0.weil⟩
  obtain ⟨M₁, hM₁⟩ := GlobalTheory.T.exists_good_schrodinger_model F E σ B hT.base a (a + b) (reS G.V V₂) G₁.W _ _ _ _ hV₂ hT₁.geo.hW
  obtain ⟨e₀, he₀⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hKP.base).1 F E σ B a (a + (b + 2)) (reS G.V V₂) G.W (reM G.M V₂) _ _ om _ _ _ _
    hP (a + b) (reS G.V V₂) G₁.W H' a (a + b + 1) M₁ rfl hC.hH' hM₁).1
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.exists_unipotent_haar_domain F E σ B (a + (b + 2)) (a + b) G.W G₁.W H' a (a + b + 1) _ _ _ _
    hT.base hT.geo.hW hT₁.geo.hW hC.hH'
  obtain ⟨C, hC0, hiso⟩ := GlobalTheory.T.eigen_intertwiner_double_restriction hKP F E σ B a (a + (b + 2)) (a + b) (reS G.V V₂) G.W G₁.W (reM G.M V₂) M₁ H' a (a + b + 1)
    hC.hH' hM₁ e₀ he₀ n₁ X₁ H₀ j₀ j₁ M₂ hH₀ hM₂ e₂ (reM_isEv V₂ hev)
  have hΨ : om (g, h) Φ ∈ schA F _ := hT.weil.isUSplitting.pres _ Φ (StabInv.polData_le_schA hT.geo.hM hΦ)
  have hx0 : H₀.x ≠ 0 := by
    intro h0
    have := hH₀.xy
    rw [h0] at this
    simp [form] at this
  have key := hiso _ _ om _ _ _ _ hP μ 𝓕 hμ h𝓕 h1 _ hΨ H₀.x hx0 hH₀.xx
  have k1 := key q hq.1 hq.2
  have k2 := key 1 (one_mem _) (by simp [mat])
  rw [k1] at k2
  have k3 := mul_left_cancel₀ hC0 k2
  have hone : om (1, 1) (om (g, h) Φ) = om (g, h) Φ := by
    rw [Prod.mk_one_one, map_one om, Module.End.one_apply]
  have hmul : om (q, 1) (om (g, h) Φ) = om (q * g, h) Φ := by
    rw [← Module.End.mul_apply, ← map_mul om, Prod.mk_mul_mk, one_mul]
  have k4 : thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (q, 1) (om (g, h) Φ)))) =
      thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (1, 1) (om (g, h) Φ)))) := k3
  rw [hone, hmul] at k4
  rw [k4]

end GlobalTheory.ThK.StabInvB

end

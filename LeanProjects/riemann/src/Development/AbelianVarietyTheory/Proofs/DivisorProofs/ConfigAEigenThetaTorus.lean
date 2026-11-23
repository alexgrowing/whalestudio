import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LeviSmall

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {α β : Chr F E} {n m : ℕ} (hα : ResEtaPow K α n) (hβ : ResEtaPow K β m) :
    ResEtaPow K (α / β) (m + n) := by
  intro a
  rw [MonoidHom.div_apply, Circle.coe_div, hα a, hβ a]
  split_ifs
  · simp
  · simp [pow_add, div_eq_mul_inv, mul_comm]
    rw [← inv_pow]
    simp

theorem isHecke_div {α β : Chr F E} (hα : IsHecke F E α) (hβ : IsHecke F E β) : IsHecke F E (α / β) := by
  refine ⟨?_, fun x => ?_⟩
  · show Continuous fun z => α z / β z
    exact hα.1.div' hβ.1
  · rw [MonoidHom.div_apply, hα.2 x, hβ.2 x, div_one]

theorem polData_le {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} (hM : M.IsGood B.ψ) :
    PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro Φ ⟨f, -, φ, hSB, hv, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB (hv.and hM.std |>.mono fun v h => h.1.trans h.2)

theorem I_smul_shift {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (c : ℂ)
    (Ψ : (Fin n × Fin d → AF F) → ℂ) (h₁ : UA σ W.J) : M.I om (c • om (1, h₁) Ψ) 1 = c * M.I om Ψ h₁ := by
  unfold Model.I
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext g
  unfold theta thetaSum
  rw [map_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

end GlobalTheory.ThK.LeviSmall

open GlobalTheory.ThK.LeviSmall in

theorem GlobalTheory.ThK.evalZero_levi_small : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e', IsEv B G.M' G₁.M' 1 H'.ι (iso0 a' H') e' → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ Φ' ∈ PolData B G.M', ∀ (t : (AE F E)ˣ) (h₁ : UA σ G₁.W.J) (m : UA σ G.W.J), IsLevi H' t h₁ m → ∀ h, G₁.M'.I om₁' (e' (om' (1, m * h) Φ')) 1 = (X.α t : ℂ) * (((absE F E t : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ) * G₁.M'.I om₁' (e' (om' (1, h) Φ')) h₁ := by
  intro hK F E _ _ _ _ _ σ B b a' G G₁ H H' hC e' he' X om om' om₁ om₁' hT hT₁ Φ' hΦ' t h₁ m hL h
  rcases G with ⟨p, q, V, V', W, M, M'⟩
  rcases G₁ with ⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩
  have eV : V₁' = V' := hC.eV
  have eq : q = 0 := hC.q0
  have eq₁ : q₁ = 0 := hC.q1
  subst eV eq eq₁
  dsimp only at *
  have hP : IsPair B M' X.α (X.α / X.β) om' 0 (a' - 0) _ _ :=
    { base := hT.base, herm := hT.geo.hV', skew := hT.geo.hW, good := hT.geo.hM', hX := hT.chars.heckeα,
      hW := isHecke_div hT.chars.heckeα hT.chars.heckeβ, resX := hT.chars.resα,
      resW := resEtaPow_div hT.chars.resα hT.chars.resβ, weil := hT.weil' }
  have hP₁ : IsPair B M₁' X.α (X.α / X.β) om₁' 0 (a' - 0) _ _ :=
    { base := hT₁.base, herm := hT₁.geo.hV', skew := hT₁.geo.hW, good := hT₁.geo.hM', hX := hT₁.chars.heckeα,
      hW := isHecke_div hT₁.chars.heckeα hT₁.chars.heckeβ, resX := hT₁.chars.resα,
      resW := resEtaPow_div hT₁.chars.resα hT₁.chars.resβ, weil := hT₁.weil' }
  have hS : om' (1, h) Φ' ∈ schA F (Fin a' × Fin (b + 2 + a')) :=
    hT.weil'.isUSplitting.pres (1, h) Φ' (polData_le hT.geo.hM' hΦ')
  have key := GlobalTheory.T.adapted_plane_second_variable hK.base F E σ B a' (b + 2 + a') V₁' W M' X.α (X.α / X.β) om' 0 (a' - 0) _ _ hP (b + a') W₁ H' 0 (b + 1)
    M₁' om₁' _ _ hC.hH' hP₁ e' he' 1 t h₁ m hL 1 (one_mem _) (om' (1, h) Φ') hS
  rw [one_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one] at key
  rw [key, I_smul_shift]

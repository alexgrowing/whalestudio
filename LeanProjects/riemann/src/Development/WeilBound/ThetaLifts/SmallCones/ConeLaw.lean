import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.ConeUnf

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Core

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

theorem levi_one (H : Plane E d d₁) : IsLevi (σ := σ) (W := W) (W₁ := W₁) H 1 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mat_one']

theorem absE_ne (l : (AE F E)ˣ) : (absE F E l : ℝ) ≠ 0 := by
  have : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact_mod_cast left_ne_zero_of_mul_eq_one this

theorem absE_pos (l : (AE F E)ˣ) : 0 < (absE F E l : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg _) (absE_ne l).symm

structure LawsT (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (om₀ : Rep σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (u : (AE F E)ˣ → Ten F E n d) (w : (AE F E)ˣ → ℂ) (ι : (AE F E)ˣ → (AE F E)ˣ) : Prop where
  one : ι 1 = 1
  w1 : w 1 = 1
  uni : ∀ m ∈ unip σ X H, ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (u 1) (om (m, 1) Ψ)) = e (M.co.rho B.ψ (u 1) Ψ)
  tor : ∀ l g₁ p h₁ p', IsLevi H (ι l) g₁ p → IsLevi H' 1 h₁ p' → ∀ Ψ ∈ schA F (Fin n × Fin d),
    (((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) • e (M.co.rho B.ψ (u 1) (om (p, p') Ψ)) =
      w l • om₀ (g₁, h₁) (e (M.co.rho B.ψ (u l) Ψ))

structure Laws (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (om₀ : Rep σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (u : (AE F E)ˣ → Ten F E n d) (ν χ : Chr F E) (z : ℕ) (ι : (AE F E)ˣ → (AE F E)ˣ) : Prop
    extends LawsT B M om om₀ H H' e u (fun l => (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) ι where
  torW : ∀ t h₁ p', IsLevi H' t h₁ p' → ∃ s : (AE F E)ˣ, ∀ l, ∀ Ψ ∈ schA F (Fin n × Fin d),
    e (M.co.rho B.ψ (u l) (om (1, p') Ψ)) = ((χ t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) *
      ((ν s : ℂ) * ((absE F E s : ℝ) : ℂ) ^ z)) • om₀ (1, h₁) (e (M.co.rho B.ψ (u (l * s)) Ψ))

variable {B : Base F E} {M : Model σ X W} {om : Rep σ X W} {M₀ : Model σ X₁ W₁} {om₀ : Rep σ X₁ W₁} {H : Plane E n n₁}
  {H' : Plane E d d₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {μ : Measure (AE F E)ˣ} {u : (AE F E)ˣ → Ten F E n d} {ν χ : Chr F E} {z : ℕ}
  {ι : (AE F E)ˣ → (AE F E)ˣ} {w : (AE F E)ˣ → ℂ} {χX χW : Chr F E} {r s r' s' r₀ s₀ r₀' s₀' : ℕ}

theorem LawsT.theta (h : LawsT B M om om₀ H H' e u w ι) {l g₁ p h₁ p'} (h1 : IsLevi H (ι l) g₁ p) (h2 : IsLevi H' 1 h₁ p') {Ψ}
    (hΨ : Ψ ∈ schA F (Fin n × Fin d)) :
    thetaSum F (e (M.co.rho B.ψ (u 1) (om (p, p') Ψ))) * (((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) =
      theta om₀ (e (M.co.rho B.ψ (u l) Ψ)) g₁ h₁ * w l := by
  have := congrArg (thetaSum F) (h.tor l g₁ p h₁ p' h1 h2 Ψ hΨ)
  rw [thetaSum_smul', thetaSum_smul'] at this
  rw [mul_comm, this, mul_comm]
  rfl

theorem LawsT.rat (h : LawsT B M om om₀ H H' e u w ι) (hD : StabDec) (hTB : ThetaBasic) (hp : IsPair B M χX χW om r s r' s')
    (hp₀ : IsPair B M₀ χX χW om₀ r₀ s₀ r₀' s₀') {j₀ j₁} (hH : H.IsAdapted σ B X X₁ j₀ j₁)
    (hs : ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (u 1) Ψ) ∈ schA F (Fin n₁ × Fin d₁)) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    (y) {δ} (hδ : δ ∈ ratU σ X.J) (hx : mat δ *ᵥ incV F H.x = incV F H.x) (g) :
    thv B M om e (u 1) Φ y (δ * g) = thv B M om e (u 1) Φ y g := by
  obtain ⟨m, hm, g₁, p, hp1, rfl, hr⟩ := (hD F E σ B n n₁ X X₁ H j₀ j₁ r s hp.base (Or.inl hp.herm) hH).1 δ 1 (by simpa using hx)
  have hΨ := pair_pres hp (g, y) hΦ
  have e1 : om (m * p * g, y) Φ = om (m, 1) (om (p, 1) (om (g, y) Φ)) := by simp [om_mul, mul_assoc]
  have e2 := h.theta (l := 1) (by rwa [h.one]) (levi_one (W₁ := W₁) H') hΨ
  have e3 := ((hTB F E σ B _ _ X₁ W₁ M₀ χX χW om₀ _ _ _ _ hp₀).1 _ (hs _ hΨ)).2.1 g₁ (hr hδ) 1 (one_mem _) 1 1
  simp only [h.one, h.w1, map_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, mul_one, Circle.coe_one, one_pow] at e2 e3
  unfold thv
  rw [e1, h.uni m hm _ (pair_pres hp _ hΨ), e2, e3]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, ← Prod.one_eq_mk]

theorem Laws.coneI_law [μ.IsMulRightInvariant] [MeasurableMul (AE F E)ˣ] (h : Laws B M om om₀ H H' e u ν χ z ι)
    (hp : IsPair B M χX χW om r s r' s') {K : Subgroup (UA σ X.J)} (μK : Measure K) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    {t h₁ p} (hl : IsLevi H' t h₁ p) (y) :
    coneI B M om M₀ om₀ e K μK μ u ν z (om (1, p * y) Φ) 1 =
      (χ t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) * coneI B M om M₀ om₀ e K μK μ u ν z (om (1, y) Φ) h₁ := by
  obtain ⟨s, hs⟩ := h.torW t h₁ p hl
  unfold coneI
  rw [← integral_const_mul]
  congr 1
  funext k
  rw [← integral_mul_right_eq_self (fun l => M₀.I om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) (om (1, y) Φ)))) h₁ * (ν l : ℂ) *
    ((absE F E l : ℝ) : ℂ) ^ z) s, ← integral_const_mul]
  congr 1
  funext l
  have e1 : om (k.1, 1) (om (1, p * y) Φ) = om (1, p) (om (k.1, 1) (om (1, y) Φ)) := by simp [om_mul]
  rw [e1, hs l _ (pair_pres hp _ (pair_pres hp _ hΦ))]
  simp only [Model.I, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, map_smul, thetaSum_smul', om_mul, Prod.mk_mul_mk, mul_one, one_mul, integral_const_mul,
    map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul, mul_pow]
  ring

end Core

end PositivityTheory.ThKCT

end

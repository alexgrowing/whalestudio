import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisInvKRegularIffIsUnit
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

theorem map_pair_selfDual {F : Type} [NontriviallyNormedField F] [LocallyCompactSpace F] [MeasurableSpace F]
    [BorelSpace F] {r : ℕ} {V : Type} [AddCommGroup V] [Module F V] [TopologicalSpace V] [IsModuleTopology F V]
    [IsTopologicalAddGroup V] [ContinuousSMul F V] [MeasurableSpace V] [BorelSpace V]
    (ψ : AddChar F ℂ) (B : V → V → F) (hBs : ∀ x y, B x y = B y x)
    (e₁ e₂ : V ≃ₗ[F] (Fin r → F)) (hB : ∀ x y, e₁ x ⬝ᵥ e₂ y = B x y)
    (μV : Measure V) (hV : SelfDual μV (fun x y => ψ (B x y)))
    (ν : Measure (Fin r → F)) (hν : SelfDual ν (fun x y => ψ (x ⬝ᵥ y)))
    (h₀ : (Fin r → F) → ℂ) (ht₀ : IsTest h₀) (h₀0 : h₀ 0 = 1) :
    ∃ c₁ c₂ : ℂ, (∀ φ : (Fin r → F) → ℂ, ∫ x, φ (e₁ x) ∂μV = c₁ * ∫ y, φ y ∂ν) ∧
      (∀ φ : (Fin r → F) → ℂ, ∫ x, φ (e₂ x) ∂μV = c₂ * ∫ y, φ y ∂ν) ∧ c₁ * c₂ = 1 := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology F := secondCountable_of_proper
  haveI := hV.1
  haveI := hν.1
  let E₁ : V ≃L[F] (Fin r → F) :=
    { e₁ with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e₁.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e₁.symm.toLinearMap }
  let E₂ : V ≃L[F] (Fin r → F) :=
    { e₂ with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e₂.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e₂.symm.toLinearMap }
  haveI : (Measure.map E₁ μV).IsAddHaarMeasure := E₁.isAddHaarMeasure_map μV
  haveI : (Measure.map E₂ μV).IsAddHaarMeasure := E₂.isAddHaarMeasure_map μV
  have hm₁ := Measure.isAddLeftInvariant_eq_smul (Measure.map E₁ μV) ν
  have hm₂ := Measure.isAddLeftInvariant_eq_smul (Measure.map E₂ μV) ν
  set c₁ := (Measure.map E₁ μV).addHaarScalarFactor ν
  set c₂ := (Measure.map E₂ μV).addHaarScalarFactor ν
  let M₁ := E₁.toHomeomorph.toMeasurableEquiv
  let M₂ := E₂.toHomeomorph.toMeasurableEquiv
  have hM₁ : ∀ x, M₁ x = e₁ x := fun _ => rfl
  have hM₂ : ∀ x, M₂ x = e₂ x := fun _ => rfl
  have hmap : ∀ (M : V ≃ᵐ (Fin r → F)) (c : ENNReal), Measure.map M μV = c • ν →
      ∀ φ : (Fin r → F) → ℂ, ∫ x, φ (M x) ∂μV = (c.toReal : ℂ) * ∫ y, φ y ∂ν := by
    intro M c hc φ
    rw [← integral_map_equiv M φ, hc, integral_smul_measure, Complex.real_smul]
  set FF := fourB ν (fun x y => ψ (x ⬝ᵥ y))
  set FV := fourB μV (fun x y => ψ (B x y))
  set f : V → ℂ := h₀ ∘ E₁
  have hf : IsTest f := ⟨ht₀.1.comp_continuous E₁.continuous, ht₀.2.comp_homeomorph E₁.toHomeomorph⟩
  have ha : ∀ c, FV f c = (c₁ : ℂ) * FF h₀ (e₂ c) := by
    intro c
    have := hmap M₁ c₁ hm₁ (fun y => h₀ y * ψ (y ⬝ᵥ e₂ c))
    simp only [hM₁, ENNReal.coe_toReal] at this
    simp only [FV, FF, fourB, f, Function.comp_apply]
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [← hB]; rfl
  have hb : ∀ b, FV (FV f) b = (c₁ : ℂ) * (c₂ : ℂ) * FF (FF h₀) (e₁ b) := by
    intro b
    have := hmap M₂ c₂ hm₂ (fun y => FF h₀ y * ψ (y ⬝ᵥ e₁ b))
    simp only [hM₂, ENNReal.coe_toReal] at this
    show ∫ c, FV f c * ψ (B c b) ∂μV = _
    simp only [ha]
    have e : ∀ c, (c₁ : ℂ) * FF h₀ (e₂ c) * ψ (B c b) = (c₁ : ℂ) * (FF h₀ (e₂ c) * ψ (e₂ c ⬝ᵥ e₁ b)) := by
      intro c; rw [hBs, ← hB, dotProduct_comm, mul_assoc]
    simp only [e]
    rw [integral_const_mul, this, mul_assoc]
    rfl
  refine ⟨c₁, c₂, fun φ => ?_, fun φ => ?_, ?_⟩
  · have := hmap M₁ c₁ hm₁ φ; simpa only [hM₁, ENNReal.coe_toReal] using this
  · have := hmap M₂ c₂ hm₂ φ; simpa only [hM₂, ENNReal.coe_toReal] using this
  have h1 := hb 0
  have h3 : FV (FV f) 0 = f (-0) := hV.2 f hf 0
  have h4 : FF (FF h₀) 0 = h₀ (-0) := hν.2 h₀ ht₀ 0
  rw [h3, map_zero, h4] at h1
  simp only [neg_zero, f, Function.comp_apply, map_zero, h₀0, mul_one] at h1
  rw [← h1]

theorem pi_selfDual (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] [MeasurableSpace F] [BorelSpace F] (μF : Measure F) [μF.IsAddHaarMeasure]
    (hvol : μF (Metric.closedBall 0 1) = 1) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (r : ℕ) :
    SelfDual (Measure.pi fun _ : Fin r => μF) (fun x y => ψ (x ⬝ᵥ y)) ∧
      IsTest ((Set.univ.pi fun _ : Fin r => Metric.closedBall (0 : F) 1).indicator 1) := by
  haveI := hU.ultraF
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology F := secondCountable_of_proper
  set S : Set (Fin r → F) := Set.univ.pi fun _ => Metric.closedBall 0 1 with hSdef
  have hmem : ∀ y : Fin r → F, y ∈ S ↔ ∀ i, ‖y i‖ ≤ 1 := by
    intro y; simp [S, Set.mem_pi, Metric.mem_closedBall, dist_zero_right]
  have hSo : IsOpen S :=
    isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall 0 one_ne_zero
  have hSc : IsCompact S := isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hScl : IsClosed S := isClosed_set_pi fun _ _ => Metric.isClosed_closedBall
  let Mg : AddSubgroup (Fin r → F) :=
    { carrier := S
      zero_mem' := by rw [hmem]; simp
      add_mem' := by
        intro a b ha hb
        rw [hmem] at ha hb ⊢
        intro i; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
      neg_mem' := by
        intro a ha
        rw [hmem] at ha ⊢
        intro i; simpa using ha i }
  have hMg : (Mg : Set (Fin r → F)) = S := rfl
  let β : LinearMap.BilinForm F (Fin r → F) := Matrix.toBilin' 1
  have hβ : ∀ x y, β x y = x ⬝ᵥ y := by intro x y; simp [β, Matrix.toBilin'_apply']
  have hβs : β.IsSymm := by
    first
    | exact ⟨fun x y => by simp [hβ, dotProduct_comm]⟩
    | exact fun x y => by simp [hβ, dotProduct_comm]
  have hβn : β.Nondegenerate := Matrix.Nondegenerate.toBilin' (Matrix.nondegenerate_of_det_ne_zero (by simp))
  have key := (GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ (Fin r → F) β hβs hβn (Measure.pi fun _ => μF) inferInstance).1 Mg
    (by rw [hMg]; exact hSo) (by rw [hMg]; exact hSc)
  have hdual : {y | ∀ x ∈ Mg, ψ (β x y) = 1} = S := by
    ext y
    simp only [Set.mem_setOf_eq, hβ]
    constructor
    · intro h
      rw [hmem]
      intro i
      by_contra hi
      push_neg at hi
      obtain ⟨x0, hx0, hx0'⟩ := hψ.2
      have hyi : y i ≠ 0 := by intro h0; rw [h0, norm_zero] at hi; linarith
      have hsmall : ‖(y i)⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hi
      have hx : Pi.single i (x0 * (y i)⁻¹) ∈ Mg := by
        show _ ∈ S
        rw [hmem]
        intro j
        by_cases hj : j = i
        · subst hj; simp only [Pi.single_eq_same]; exact hx0' _ hsmall
        · simp [Pi.single_eq_of_ne hj]
      have h2 := h _ hx
      have e : Pi.single i (x0 * (y i)⁻¹) ⬝ᵥ y = x0 := by
        simp only [dotProduct, Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [mul_assoc, inv_mul_cancel₀ hyi, mul_one]
      rw [e] at h2
      exact hx0 h2
    · intro hy x hx
      have hx' : x ∈ S := hx
      rw [hmem] at hy hx'
      apply hψ.1
      simp only [dotProduct]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
      rw [norm_mul]; exact mul_le_one₀ (hx' i) (norm_nonneg _) (hy i)
  have hvolS : (Measure.pi fun _ : Fin r => μF) S = 1 := by
    rw [hSdef, Measure.pi_pi]; simp [hvol]
  have hsd : SelfDual (Measure.pi fun _ : Fin r => μF) (fun x y => ψ (β x y)) :=
    key.1.2 (by rw [hdual, hMg, hvolS, one_mul])
  refine ⟨?_, ?_⟩
  · have e : (fun x y : Fin r → F => ψ (x ⬝ᵥ y)) = (fun x y => ψ (β x y)) := by funext x y; rw [hβ]
    rw [e]; exact hsd
  · exact ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hScl, hSo⟩).isLocallyConstant,
      HasCompactSupport.intro hSc fun x hx => Set.indicator_of_notMem hx _⟩

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc

theorem fourG_act_pt_eq_fourK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ μK : Measure A.K, SelfDual μK (A.kerK ψ) → ∀ f' : Gl r F → ℂ, IsTest f' → ∀ (g : GL (Fin r) F) (b c : A.K), fourG M ψ f' (act g (LinDesc.pt A hG lam b c)) = A.fourK μK ψ (fun x => f' (act g (LinDesc.pt A hG lam x.1 x.2))) (b, c) := by
  intro F E _ _ _ _ hU A r τ p hG lam M ψ hψ μK hK f' _ g b c
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI := hU.lcF
  obtain ⟨hsd, ht0⟩ := pi_selfDual F E M.μF M.volF ψ hψ r
  set ν : Measure (Fin r → F) := Measure.pi fun _ : Fin r => M.μF with hν
  let gm : Matrix (Fin r) (Fin r) F := (g : Matrix (Fin r) (Fin r) F)
  let gi : Matrix (Fin r) (Fin r) F := ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)
  have hgig : gi * gm = 1 := by simp [gi, gm]
  have hggi : gm * gi = 1 := by simp [gi, gm]
  let gL : (Fin r → F) ≃ₗ[F] (Fin r → F) :=
    { toFun := fun v => gm *ᵥ v
      invFun := fun v => gi *ᵥ v
      map_add' := fun v w => mulVec_add _ _ _
      map_smul' := fun a v => by simp [mulVec_smul]
      left_inv := fun v => by simp [mulVec_mulVec, hgig]
      right_inv := fun v => by simp [mulVec_mulVec, hggi] }
  let hL : (Fin r → F) ≃ₗ[F] (Fin r → F) :=
    { toFun := fun v => v ᵥ* gi
      invFun := fun v => v ᵥ* gm
      map_add' := fun v w => add_vecMul _ _ _
      map_smul' := fun a v => by simp [smul_vecMul]
      left_inv := fun v => by simp [vecMul_vecMul, hgig]
      right_inv := fun v => by simp [vecMul_vecMul, hggi] }
  let ρL : A.K →ₗ[F] (Fin r → F) :=
    { toFun := fun c i => Algebra.trace F A.K (τ ^ (i : ℕ) * c)
      map_add' := by intro x y; funext i; simp [mul_add]
      map_smul' := by intro a x; funext i; simp [mul_smul_comm] }
  have hρ : Function.Bijective ρL := (GlobalTheory.JR.EtInv.invK_regular_iff_isUnit F E A r τ p lam hG).1
  let e₁ : A.K ≃ₗ[F] (Fin r → F) := (bas A hG).equivFun.trans gL
  let e₂ : A.K ≃ₗ[F] (Fin r → F) := (LinearEquiv.ofBijective ρL hρ).trans hL
  have he₁ : ∀ x, e₁ x = gm *ᵥ (bas A hG).equivFun x := fun _ => rfl
  have he₂ : ∀ x, e₂ x = (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * x)) ᵥ* gi := fun _ => rfl
  have hB : ∀ x y, e₁ x ⬝ᵥ e₂ y = Algebra.trace F A.K (x * y) := by
    intro x y
    rw [he₁, he₂, dotProduct_comm, ← dotProduct_mulVec, mulVec_mulVec, hgig, one_mulVec]
    conv_rhs => rw [← (bas A hG).sum_equivFun x]
    rw [Finset.sum_mul, map_sum]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bas_apply, smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]
  obtain ⟨c₁, c₂, h₁, h₂, hc⟩ := map_pair_selfDual ψ (fun x y => Algebra.trace F A.K (x * y))
    (fun x y => by rw [mul_comm]) e₁ e₂ hB μK hK ν hsd _ ht0 (by simp)
  let X : Matrix (Fin r) (Fin r) F := gm * companion p * gi
  let G : (Fin r → F) → (Fin r → F) → ℂ := fun x y => f' (X, x, y, lam) * ψ (y ⬝ᵥ e₁ b + e₂ c ⬝ᵥ x)
  have lhs : fourG M ψ f' (act g (pt A hG lam b c)) = ∫ x, (∫ y, G x y ∂ν) ∂ν := rfl
  have rhs : A.fourK μK ψ (fun x => f' (act g (pt A hG lam x.1 x.2))) (b, c) =
      ∫ x, (∫ y, G (e₁ x) (e₂ y) ∂μK) ∂μK := by
    unfold Et.fourK
    refine integral_congr_ae (Eventually.of_forall fun x => integral_congr_ae (Eventually.of_forall fun y => ?_))
    show f' (act g (pt A hG lam x y)) * A.psiK ψ (b * y + x * c) = G (e₁ x) (e₂ y)
    simp only [G]
    congr 1
    rw [Et.psiK, map_add, ← hB, ← hB, dotProduct_comm (e₁ b), dotProduct_comm (e₁ x)]
  rw [lhs, rhs]
  have inner : ∀ x, ∫ y, G (e₁ x) (e₂ y) ∂μK = c₂ * ∫ y, G (e₁ x) y ∂ν := fun x => h₂ (fun y => G (e₁ x) y)
  rw [integral_congr_ae (Eventually.of_forall inner), integral_const_mul, h₁ (fun x => ∫ y, G x y ∂ν)]
  rw [← mul_assoc, mul_comm c₂, hc, one_mul]

end GlobalTheory.JR.LinDesc

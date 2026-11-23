import Development.WeilBound.CoreStatements.BranchingTraces.FormTSingle

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace PositivityTheory.UnitaryDecomposition

section Abs

variable {G K K' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [SFinite ν] [ν.IsMulLeftInvariant]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

structure URep (ρ : G → K →L[ℂ] K) : Prop where
  mul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x)
  adj : ∀ g x y, ⟪ρ g x, y⟫_ℂ = ⟪x, ρ g⁻¹ y⟫_ℂ
  nrm : ∀ g x, ‖ρ g x‖ = ‖x‖
  cont : ∀ x, Continuous fun g => ρ g x

theorem exists_intertwiner {ρ : G → K →L[ℂ] K} {σ : G → K' →L[ℂ] K'} (hρ : URep ρ) (hσ : URep σ)
    (hirr : ∀ S : Submodule ℂ K', IsClosed (S : Set K') → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤) (κ : ℝ)
    (hS : ∀ v w v' w' : K', ∫ g, ⟪w, σ g v⟫_ℂ * conj ⟪w', σ g v'⟫_ℂ ∂ν = κ * (⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ))
    (w : K') (hw : w ≠ 0) (hm : Integrable (fun h => ⟪w, σ h w⟫_ℂ) ν) (a : K) :
    ∃ j : K' →L[ℂ] K, (∀ g x, j (σ g x) = ρ g (j x)) ∧ ∀ b, ⟪b, j w⟫_ℂ = ∫ h, conj ⟪w, σ h w⟫_ℂ * ⟪b, ρ h a⟫_ℂ ∂ν := by
  let D : Submodule ℂ K' :=
    { carrier := {y | Integrable (fun h => ⟪σ h w, y⟫_ℂ) ν}
      add_mem' := fun {x y} hx hy => (hx.add hy).congr (.of_forall fun h => (inner_add_right _ _ _).symm)
      zero_mem' := by simp
      smul_mem' := fun c x hx => (hx.const_mul c).congr (.of_forall fun h => (inner_smul_right _ _ _).symm) }
  have hsh : ∀ g h y, ⟪σ h w, σ g y⟫_ℂ = ⟪σ (g⁻¹ * h) w, y⟫_ℂ := fun g h y => by rw [hσ.mul, hσ.adj g⁻¹, inv_inv]
  have hD : ∀ g, ∀ y ∈ D, σ g y ∈ D := fun g y hy => by
    show Integrable _ ν
    simp only [hsh]
    exact Integrable.comp_mul_left hy g⁻¹
  have hwD : w ∈ D := by
    exact (Complex.conjCLE.toContinuousLinearMap.integrable_comp hm).congr (.of_forall fun h => inner_conj_symm _ _)
  have hi : ∀ y ∈ D, Integrable (fun h => ⟪σ h w, y⟫_ℂ • ρ h a) ν := fun y hy =>
    (hy.norm.mul_const ‖a‖).mono' (hy.1.smul (hρ.cont a).aestronglyMeasurable) (.of_forall fun h => by rw [norm_smul, hρ.nrm])
  let J : D →ₗ[ℂ] K :=
    { toFun := fun y => ∫ h, ⟪σ h w, y.1⟫_ℂ • ρ h a ∂ν
      map_add' := fun x y => by
        rw [← integral_add (hi _ x.2) (hi _ y.2)]
        simp only [Submodule.coe_add, inner_add_right, add_smul]
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← integral_smul]
        simp only [Submodule.coe_smul, inner_smul_right, mul_smul] }
  have hJ : ∀ (y : D) b, ⟪b, J y⟫_ℂ = ∫ h, ⟪σ h w, y.1⟫_ℂ * ⟪b, ρ h a⟫_ℂ ∂ν := fun y b => by
    show ⟪b, ∫ h, _ ∂ν⟫_ℂ = _
    rw [← integral_inner (hi _ y.2)]; simp only [inner_smul_right]
  have hb : Continuous fun x => ⟪a, ρ x a⟫_ℂ := continuous_const.inner (hρ.cont a)
  have hn : ∀ y : D, ⟪J y, J y⟫_ℂ = ⟪y.1, y.1⟫_ℂ * (κ * ∫ t, ⟪σ t w, w⟫_ℂ * ⟪a, ρ t a⟫_ℂ ∂ν) := by
    intro y
    have hc : Integrable (fun h => conj ⟪σ h w, y.1⟫_ℂ) ν := Complex.conjCLE.toContinuousLinearMap.integrable_comp y.2
    have hI : Integrable (Function.uncurry fun h t => conj ⟪σ h w, y.1⟫_ℂ * ⟪σ (h * t) w, y.1⟫_ℂ * ⟪a, ρ t a⟫_ℂ) (ν.prod ν) := by
      have := (measurePreserving_prod_mul ν ν).integrable_comp_of_integrable (hc.mul_prod y.2)
      refine this.mul_bdd (c := ‖a‖ * ‖a‖) (hb.comp continuous_snd).aestronglyMeasurable (.of_forall fun z => ?_)
      exact (norm_inner_le_norm _ _).trans (by rw [hρ.nrm])
    calc ⟪J y, J y⟫_ℂ = ∫ h, ∫ t, conj ⟪σ h w, y.1⟫_ℂ * ⟪σ (h * t) w, y.1⟫_ℂ * ⟪a, ρ t a⟫_ℂ ∂ν ∂ν := by
          rw [← inner_conj_symm, hJ, ← integral_conj]
          refine integral_congr_ae (.of_forall fun h => ?_)
          simp only
          rw [map_mul, inner_conj_symm (ρ h a), hJ, ← integral_const_mul, ← integral_mul_left_eq_self _ h]
          refine integral_congr_ae (.of_forall fun t => ?_)
          simp only
          rw [hρ.adj, ← hρ.mul, inv_mul_cancel_left, mul_assoc]
      _ = ∫ t, ⟪y.1, y.1⟫_ℂ * (κ * (⟪σ t w, w⟫_ℂ * ⟪a, ρ t a⟫_ℂ)) ∂ν := by
          rw [integral_integral_swap hI]
          refine integral_congr_ae (.of_forall fun t => ?_)
          simp only
          rw [integral_mul_const]
          have := hS w y.1 (σ t w) y.1
          simp only [inner_conj_symm] at this ⊢
          simp only [hσ.mul]
          rw [this]; ring
      _ = _ := by rw [integral_const_mul, integral_const_mul]
  have hbd : ∃ C, ∀ y : D, ‖J y‖ ≤ C * ‖D.subtype y‖ := by
    refine ⟨Real.sqrt ‖(κ : ℂ) * ∫ t, ⟪σ t w, w⟫_ℂ * ⟪a, ρ t a⟫_ℂ ∂ν‖, fun y => ?_⟩
    have h := congrArg norm (hn y)
    rw [norm_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, norm_pow, norm_pow] at h
    simp only [Complex.coe_algebraMap, Complex.norm_real, norm_norm] at h
    refine le_of_eq ((pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_)
    rw [h, mul_pow, Real.sq_sqrt (norm_nonneg _), mul_comm]; rfl
  have hden : DenseRange D.subtype := by
    rcases hirr D.topologicalClosure D.isClosed_topologicalClosure (fun g v hv =>
      map_mem_closure (σ g).continuous hv (hD g)) with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ D.le_topologicalClosure hwD)) hw
    · rw [DenseRange, show Set.range D.subtype = D from Subtype.range_coe, dense_iff_closure_eq,
        ← Submodule.topologicalClosure_coe, h, Submodule.top_coe]
  have hj : ∀ y : D, J.extendOfNorm D.subtype y.1 = J y := fun y => LinearMap.extendOfNorm_eq hden hbd y
  refine ⟨J.extendOfNorm D.subtype, fun g x => ?_, fun b => ?_⟩
  · refine hden.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) fun y => ?_
    rw [show D.subtype y = y.1 from rfl, hj y, hj ⟨_, hD g _ y.2⟩]
    refine ext_inner_left ℂ fun b => ?_
    rw [hJ, show ⟪b, ρ g (J y)⟫_ℂ = ⟪ρ g⁻¹ b, J y⟫_ℂ by rw [hρ.adj, inv_inv], hJ, ← integral_mul_left_eq_self _ g]
    refine integral_congr_ae (.of_forall fun h => ?_)
    simp only
    rw [hsh, inv_mul_cancel_left, hρ.adj, inv_inv, hρ.mul]
  · rw [hj ⟨w, hwD⟩, hJ]
    simp only [inner_conj_symm]

end Abs

open Formalism.REAL Formalism.MainNotions.S Formalism.MainNotions.BridgeCSchur

variable {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)}
  {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)} {σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

theorem uRep_self (hU : IsURepOn (UJset ε') σ) : URep fun h : UJ ε' => σ (um h) :=
  ⟨u_mul hU, u_adj hU, fun g => hU.2.1 _ (umat_mem g), fun x => (hU.2.2 x).comp_continuous continuous_umat umat_mem⟩

theorem uRep_emb (hF : Fits ε ε' e) (hU : IsURepOn (UJset ε) π) : URep fun h : UJ ε' => π (emb e (um h)) :=
  ⟨fun g h x => (congrArg (fun y => π y x) (emb_mul _ _)).trans (u_mul hU (embU hF g) (embU hF h) x),
    fun g x y => u_adj hU (embU hF g) x y, fun g => hU.2.1 _ (umat_mem (embU hF g)),
    fun x => (hU.2.2 x).comp_continuous continuous_emb fun h => umat_mem (embU hF h)⟩

theorem schur_haar [CompleteSpace H'] {mu : Fin n → ℝ} (hσ : IsDS ε' mu σ) (ν : Measure (UJ ε')) [ν.IsHaarMeasure] :
    ∃ κ : ℝ, 0 < κ ∧ ∀ v w v' w' : H', Integrable (fun g : UJ ε' => ⟪w, σ (um g) v⟫_ℂ * conj ⟪w', σ (um g) v'⟫_ℂ) ν ∧
      ∫ g : UJ ε', ⟪w, σ (um g) v⟫_ℂ * conj ⟪w', σ (um g) v'⟫_ℂ ∂ν = κ * (⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ) := by
  obtain ⟨d, hd, h⟩ := schur_UJ σ hσ.2.1 hσ.2.2.1 hσ.2.2.2.1 hσ.2.2.2.2.1
  have hc := Measure.haarScalarFactor_pos_of_isHaarMeasure ν (muG ε')
  refine ⟨Measure.haarScalarFactor ν (muG ε') / d, div_pos hc hd, fun v w v' w' => ?_⟩
  have e := Measure.isMulLeftInvariant_eq_smul ν (muG ε')
  set c := Measure.haarScalarFactor ν (muG ε')
  rw [e]
  refine ⟨(h v w v' w').1.smul_measure_nnreal, ?_⟩
  rw [integral_smul_nnreal_measure]
  erw [(h v w v' w').2]
  rw [NNReal.smul_def, Complex.real_smul]
  push_cast; ring

theorem proj_of (hHe : HeBranching) [CompleteSpace H] [CompleteSpace H'] {lam : Fin (n + 1) → ℝ} {mu : Fin n → ℝ}
    (hF : Fits ε ε' e) (h1 : Formalism.QuantumDeterminants.IsHCParam lam) (h2 : Formalism.QuantumDeterminants.IsHCParam mu) (hπ : IsDS ε lam π) (hσ : IsDS ε' mu σ)
    (hW : HeWord ε lam ε' mu) (ν : Measure (UJ ε')) [ν.IsHaarMeasure] :
    ∃ (P : H →L[ℂ] H') (κ : ℝ), Intertw ε' e π σ P ∧ 0 < κ ∧ (∀ w, ‖ContinuousLinearMap.adjoint P w‖ = ‖w‖) ∧
      (∀ v w v' w' : H', Integrable (fun g : UJ ε' => ⟪w, σ (um g) v⟫_ℂ * conj ⟪w', σ (um g) v'⟫_ℂ) ν ∧
        ∫ g : UJ ε', ⟪w, σ (um g) v⟫_ℂ * conj ⟪w', σ (um g) v'⟫_ℂ ∂ν = κ * (⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ)) ∧
      ∀ w : H', ‖w‖ = 1 → Integrable (fun h : UJ ε' => ⟪w, σ (um h) w⟫_ℂ) ν →
        (∀ x : UJ ε', ∫ h : UJ ε', conj ⟪w, σ (um h) w⟫_ℂ * conj ⟪w, σ (um (h⁻¹ * x)) w⟫_ℂ ∂ν = κ * conj ⟪w, σ (um x) w⟫_ℂ) ∧
        ∀ a b : H, ∫ h : UJ ε', conj ⟪w, σ (um h) w⟫_ℂ * ⟪b, π (emb e (um h)) a⟫_ℂ ∂ν =
          κ * (⟪b, ContinuousLinearMap.adjoint P w⟫_ℂ * ⟪ContinuousLinearMap.adjoint P w, a⟫_ℂ) := by
  obtain ⟨i, hi, huniq⟩ := hHe n ε lam ε' mu e H H' π σ hF h1 h2 hπ hσ hW
  obtain ⟨κ, hκ, hS⟩ := schur_haar hσ ν
  have hρ := uRep_emb hF hπ.2.2.1
  have hs := uRep_self hσ.2.2.1
  set P := ContinuousLinearMap.adjoint i.toContinuousLinearMap with hP
  have hPi : ContinuousLinearMap.adjoint P = i.toContinuousLinearMap := ContinuousLinearMap.adjoint_adjoint _
  have hPa : ∀ y x, ⟪y, P x⟫_ℂ = ⟪i y, x⟫_ℂ := fun y x => ContinuousLinearMap.adjoint_inner_right _ y x
  have hint : ∀ (h : UJ ε') x, P (π (emb e (um h)) x) = σ (um h) (P x) := fun h x => ext_inner_left ℂ fun y => by
    have a1 := hρ.adj h⁻¹ (i y) x
    have a2 := hs.adj h⁻¹ y (P x)
    simp only [inv_inv] at a1 a2
    rw [hPa, ← a1, ← a2, hPa, hi]
  refine ⟨P, κ, ⟨?_, hint⟩, hκ, fun w => by rw [hPi]; exact i.norm_map w, hS, fun w hw hm => ⟨fun x => ?_, fun a b => ?_⟩⟩
  · rw [hP, LinearIsometryEquiv.norm_map]; exact i.norm_toContinuousLinearMap_le
  · have := (hS w (σ (um x) w) w w).2
    rw [inner_self_eq_norm_sq_to_K, hw] at this
    rw [inner_conj_symm (σ (um x) w), show (κ : ℂ) * ⟪σ (um x) w, w⟫_ℂ = κ * ((((1 : ℝ) : ℂ)) ^ 2 * ⟪σ (um x) w, w⟫_ℂ) by simp]
    refine Eq.trans (integral_congr_ae (.of_forall fun h => ?_)) this
    have a1 := hs.adj h w (σ (um x) w)
    simp only at a1 ⊢
    rw [u_mul hσ.2.2.1, ← a1, inner_conj_symm (σ (um x) w), mul_comm]
  · obtain ⟨j, hj1, hj2⟩ := exists_intertwiner ν hρ hs (irr_of hσ.2.2.2.1) κ (fun v w v' w' => (hS v w v' w').2) w
      (norm_ne_zero_iff.1 (by rw [hw]; exact one_ne_zero)) hm a
    obtain ⟨c, hc⟩ := huniq j hj1
    have hc2 : c = κ * ⟪i w, a⟫_ℂ := by
      have h3 := hj2 (i w)
      rw [hc, inner_smul_right, i.inner_map_map, inner_self_eq_norm_sq_to_K, hw] at h3
      have h4 := (hS (P a) w w w).2
      rw [inner_self_eq_norm_sq_to_K, hw, hPa] at h4
      simp only [Complex.coe_algebraMap, Complex.ofReal_one, one_pow, mul_one] at h3 h4
      rw [h3, ← h4]
      refine integral_congr_ae (.of_forall fun h => ?_)
      simp only
      rw [← hPa, hint, mul_comm]
    rw [← hj2, hc, inner_smul_right, hc2, hPi]
    show _ = (κ : ℂ) * (⟪b, i w⟫_ℂ * ⟪i w, a⟫_ℂ)
    ring

end PositivityTheory.UnitaryDecomposition

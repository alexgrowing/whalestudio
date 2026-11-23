import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.Intertw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.UnipMemIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.VolOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.FlatInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SwapInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ThBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BfFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.DenseCc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvLaws

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

variable {K : Type} [Field K] [NumberField K]

private theorem repSum {μ : Measure (G1 K (2 + 2))} [μ.IsHaarMeasure] {ι : Type} (s : Finset ι) (φ : ι → L2 μ)
    (F : ι → G1 K (2 + 2) → ℂ) (h : ∀ i, IsContRep μ (φ i) (F i)) : IsContRep μ (∑ i ∈ s, φ i) (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isContRep_zero
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (h i).add ih

private theorem kerConv {d : ℕ} (κ : ℝ → Eu d →L[ℂ] Eu d) (hk : Ker κ) (β : ℝ → ℂ) (v : Eu d) (hβ : Continuous β)
    (hβc : HasCompactSupport β) :
    Continuous (fun x => ∫ t, β (x + t) • κ t v) ∧ HasCompactSupport (fun x => ∫ t, β (x + t) • κ t v) := by
  have e : (fun x => ∫ t, β (x + t) • κ t v) =
      MeasureTheory.convolution β (fun t => κ (-t) v) (ContinuousLinearMap.lsmul ℝ ℂ) volume := by
    funext x
    rw [MeasureTheory.convolution]
    refine Eq.trans ?_ (integral_add_left_eq_self _ x)
    simp
  have c1 : Continuous fun t => κ (-t) v := (hk.1.comp continuous_neg).clm_apply continuous_const
  have c2 : HasCompactSupport fun t => κ (-t) v :=
    (hk.2.comp_homeomorph (Homeomorph.neg ℝ)).mono fun t ht h0 => ht (by
      have : κ (-t) = 0 := h0
      simp [this])
  rw [e]
  exact ⟨c2.continuous_convolution_right _ hβ.locallyIntegrable c1, hβc.convolution _ c2⟩

private theorem lineTerm [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] {μ₂ : Measure (G1 K 2)}
    [μ₂.IsHaarMeasure] {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} (h₁ : CuspIrr μ₂ τ₁) (h₂ : CuspIrr μ₂ τ₂) {D : TypeDat K (2 + 2)}
    {d d' : ℕ} (A : Line μ τ₁ τ₂ D d) (B : Line μ τ₂ τ₁ D d') (a : CC K (2 + 2)) (κ : ℝ → Eu d →L[ℂ] Eu d) (hk : Ker κ)
    (hc : Conv A.J A.J (Rop μ a) κ) (s : ℝ) (β : ℝ → ℂ) (v : Eu d) (u : L (Eu d)) (hβ : Continuous β)
    (hβc : HasCompactSupport β) (hu : ∀ᵐ x : ℝ, u x = β x • v) :
    ∃ (p : Eu d) (q : Eu d'), ∀ g, ct 2 (rc μ a (A.J u)) (lv 1 1 (s - HH g) * g) = A.sec p g + B.sec q g := by
  classical
  obtain ⟨w, hw, hwc, hwe⟩ : ∃ w : ℝ → Eu d, Continuous w ∧ HasCompactSupport w ∧ ∀ x, w x = ∫ t, β (x + t) • κ t v :=
    ⟨_, (kerConv κ hk β v hβ hβc).1, (kerConv κ hk β v hβ hβc).2, fun _ => rfl⟩
  let e := EuclideanSpace.basisFun (Fin d) ℂ
  have hci : ∀ i, Continuous fun x => w x i := fun i => by fun_prop
  have hcc : ∀ i, HasCompactSupport fun x => w x i := fun i =>
    hwc.mono fun x hx h0 => hx (by simp only [h0]; rfl)
  have hsum : ∀ x, w x = ∑ i, w x i • e i := fun x => (e.sum_repr (w x)).symm
  choose U hU using fun i => (denseCc d).2.1 (fun x => w x i) (e i) (hci i) (hcc i)
  have hJ : Rop μ a (A.J u) = A.J (∑ i, U i) := by
    refine hc u _ ?_
    filter_upwards [MeasureTheory.Lp.coeFn_finsetSum Finset.univ U, ae_all_iff.2 hU] with x h2 h3
    rw [h2]
    simp only [Finset.sum_apply, h3]
    rw [← hsum x, hwe]
    refine integral_congr_ae ?_
    filter_upwards [(measurePreserving_add_left volume x).quasiMeasurePreserving.ae hu] with t ht
    rw [ht, map_smul]
  obtain ⟨F, hFd⟩ : ∃ F : Fin d → G1 K (2 + 2) → ℂ, F = fun i => bf (fun x => w x i) (A.sec (e i)) := ⟨_, rfl⟩
  have hsec := fun i => (A.onto (A.sec (e i))).1 ⟨_, rfl⟩
  have hS := fun i => secFun μ₂ τ₁ τ₂ D h₁ h₂ _ (hsec i).1 (hsec i).2
  have hB : ∀ i, PFun (F i) ∧ InBand (F i) := fun i => by
    have h' := bfFun _ _ (hS i) (hci i) (hcc i)
    rw [hFd]
    exact ⟨h'.1, h'.2.1⟩
  have hT := fun i => thBasic μ (F i) (hB i).1.cont (hB i).1.rat (hB i).2
  have hR : IsContRep μ (A.J (∑ i, U i)) (∑ i, th (F i)) := by
    rw [map_sum]
    refine repSum Finset.univ (fun i => A.J (U i)) (fun i => th (F i)) fun i => ⟨(hT i).2.1, (hT i).2.2.1, ?_⟩
    rw [hFd]
    exact A.spec _ _ _ (hci i) (hcc i) (hU i)
  have heq : rc μ a (A.J u) = ∑ i, th (F i) := by
    obtain ⟨c1, -, r1⟩ : IsContRep μ (Rop μ a (A.J u)) (rc μ a (A.J u)) := isContRep_rconv μ a (A.J u)
    obtain ⟨c2, -, r2⟩ := hR
    rw [hJ] at r1
    refine (Continuous.ae_eq_iff_eq μ c1 c2).1 ?_
    filter_upwards [r1, r2] with y y1 y2
    exact y1.symm.trans y2
  have hct : ∀ z, ct 2 (rc μ a (A.J u)) z =
      ∑ i, (volN K * F i z + ∫ X, F i (w0 K * nn X * z) ∂unipMeasure K (2 + 2) 2) := by
    intro z
    simp only [← fun i => (thCt (F i) (hB i).1 (hB i).2 z).2.2.2]
    rw [ct, heq]
    simp only [Finset.sum_apply]
    refine integral_finset_sum _ fun i _ => ?_
    obtain ⟨-, -, C, hC, hsub, -⟩ := volOne (K := K) (2 + 2) 2
    have hcont : Continuous fun X => th (F i) (unipOne K (2 + 2) 2 X * z) :=
      (hT i).2.1.comp ((continuous_unipOne 2).mul continuous_const)
    exact (hcont.continuousOn.integrableOn_compact hC).mono_set hsub
  obtain ⟨h1, -, -, -, -⟩ := hpSpec (K := K)
  obtain ⟨-, -, hl, -⟩ := blkLaws (K := K)
  have hz : ∀ g : G1 K (2 + 2), HP 2 2 (lv 1 1 (s - HH g) * g) = s := fun g => by
    have hn : ∀ (X : UPos (2 + 2) 2 → 𝔸[K]) (g : G1 K (2 + 2)), HH (nn X * g) = HH g := fun X g => by
      have := h1 X 1 1 0 g
      rwa [hl, mul_one, zero_add] at this
    have := h1 0 1 1 (s - HH g) g
    rw [mul_assoc, hn] at this
    change HH _ = s
    rw [this]
    ring
  have hF : ∀ (g : G1 K (2 + 2)) (i : Fin d), F i (lv 1 1 (s - HH g) * g) =
      w s i * Complex.exp ((((2 + 2 : ℕ) : ℝ) / 2 * s : ℝ) : ℂ) * A.sec (e i) g := fun g i => by
    rw [hFd]
    simp only [bf]
    rw [hz g, (hS i).ray]
  have hq : ∀ i, ∃ q : Eu d', B.sec q = fun g =>
      ∫ X, F i (w0 K * nn X * (lv 1 1 (s - HH g) * g)) ∂unipMeasure K (2 + 2) 2 := fun i => by
    have h := intertw μ₂ τ₁ τ₂ D h₁ h₂ (A.sec (e i)) (fun x => w x i) s (hsec i).1 (hsec i).2 (hci i) (hcc i)
    rw [hFd]
    exact (B.onto _).2 h
  choose q hq using hq
  refine ⟨Complex.exp ((((2 + 2 : ℕ) : ℝ) / 2 * s : ℝ) : ℂ) • w s, ∑ i, q i, fun g => ?_⟩
  rw [hct, Finset.sum_add_distrib]
  congr 1
  · have hs : A.sec (w s) g = ∑ i, w s i * A.sec (e i) g := by
      conv_lhs => rw [hsum s]
      rw [map_sum]
      simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [map_smul, Pi.smul_apply, hs, smul_eq_mul, Finset.mul_sum, (volOne (K := K) 0 0).2.1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hF, Complex.ofReal_one, one_mul]
    ring
  · rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hq]

private theorem lineIn [IsTotallyComplex K] {μ : Measure (G1 K (2 + 2))} [μ.IsHaarMeasure] {d : ℕ}
    (J : L (Eu d) →ₗᵢ[ℂ] L2 μ) (C : Submodule ℂ (L2 μ)) (hC : IsClosed (C : Set (L2 μ)))
    (h : ∀ (β : ℝ → ℂ) (v : Eu d) (u : L (Eu d)), Continuous β → HasCompactSupport β → (∀ᵐ x : ℝ, u x = β x • v) → J u ∈ C)
    (u : L (Eu d)) : J u ∈ C := by
  have hcl : IsClosed {u : L (Eu d) | J u ∈ C} := hC.preimage J.continuous
  have hle : (Submodule.span ℂ {u : L (Eu d) | ∃ (β : ℝ → ℂ) (v : Eu d), Continuous β ∧ HasCompactSupport β ∧ ∀ᵐ x : ℝ, u x = β x • v} :
      Set (L (Eu d))) ⊆ {u : L (Eu d) | J u ∈ C} := by
    have : Submodule.span ℂ {u : L (Eu d) | ∃ (β : ℝ → ℂ) (v : Eu d), Continuous β ∧ HasCompactSupport β ∧ ∀ᵐ x : ℝ, u x = β x • v} ≤
        C.comap J.toLinearMap := by
      refine Submodule.span_le.2 ?_
      rintro u ⟨β, v, h1, h2, h3⟩
      exact h β v u h1 h2 h3
    exact this
  exact closure_minimal hle hcl ((denseCc d).1 u)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.ctMem :
    ForAllC fun K _ _ μ _ _ _ _ _ D _ _ A A' => ∀ (a : CC K (2 + 2)) (P : L2 μ →L[ℂ] L2 μ), IsOrthogonalProjectionTwoLines A.J A'.J P → D.Hecke a → ∀ φ, P φ = φ → ∀ s : ℝ,
      ∃ v v', ∀ g, ct 2 (rc μ a φ) (lv 1 1 (s - HH g) * g) = A.sec v g + A'.sec v' g := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP D d d' A A' a P hP0 ha φ hφ s
  have hPs : Pair μ₂ τ₂ τ₁ := ⟨hP.irr₂, hP.irr₁, hP.orth.symm⟩
  obtain ⟨κ, hk, hc, -⟩ := convR K μ μ₂ τ₁ τ₂ hP D d d' A A' a ha
  obtain ⟨κ', hk', hc', -⟩ := convR K μ μ₂ τ₂ τ₁ hPs D d' d A' A a ha
  obtain ⟨kc, -, hin⟩ := (ctKv μ a).1 2
  obtain ⟨z, hzd⟩ : ∃ z : G1 K (2 + 2) → G1 K (2 + 2), z = fun g => lv 1 1 (s - HH g) * g := ⟨_, rfl⟩
  let Tm : L2 μ →ₗ[ℂ] (G1 K (2 + 2) → ℂ) :=
    { toFun := fun φ g => ⟪kc (z g), φ⟫_ℂ
      map_add' := fun x y => by funext g; simp [inner_add_right]
      map_smul' := fun c x => by funext g; simp [inner_smul_right] }
  have hTc : Continuous Tm := continuous_pi fun g => (innerSL ℂ (kc (z g))).continuous
  have hTm : ∀ (ψ : L2 μ) g, Tm ψ g = ct 2 (rc μ a ψ) (lv 1 1 (s - HH g) * g) := fun ψ g => by
    rw [← hin, show lv 1 1 (s - HH g) * g = z g by rw [hzd]]
    rfl
  let S : Submodule ℂ (G1 K (2 + 2) → ℂ) := LinearMap.range A.sec ⊔ LinearMap.range A'.sec
  have hS : IsClosed (S : Set (G1 K (2 + 2) → ℂ)) := Submodule.closed_of_finiteDimensional S
  let C : Submodule ℂ (L2 μ) := S.comap Tm
  have hC : IsClosed (C : Set (L2 μ)) := hS.preimage hTc
  have hA : ∀ u, A.J u ∈ C := lineIn A.J C hC fun β v u h1 h2 h3 => by
    obtain ⟨p, q, h⟩ := lineTerm μ hP.irr₁ hP.irr₂ A A' a κ hk hc s β v u h1 h2 h3
    have e : Tm (A.J u) = A.sec p + A'.sec q := funext fun g => by rw [hTm, h]; rfl
    change Tm (A.J u) ∈ S
    rw [e]
    exact Submodule.add_mem_sup ⟨p, rfl⟩ ⟨q, rfl⟩
  have hA' : ∀ u, A'.J u ∈ C := lineIn A'.J C hC fun β v u h1 h2 h3 => by
    obtain ⟨p, q, h⟩ := lineTerm μ hP.irr₂ hP.irr₁ A' A a κ' hk' hc' s β v u h1 h2 h3
    have e : Tm (A'.J u) = A.sec q + A'.sec p := funext fun g => by rw [hTm, h, add_comm]; rfl
    change Tm (A'.J u) ∈ S
    rw [e]
    exact Submodule.add_mem_sup ⟨q, rfl⟩ ⟨p, rfl⟩
  let W : Submodule ℂ (L2 μ) := LinearMap.range A.J.toLinearMap ⊔ LinearMap.range A'.J.toLinearMap
  have hWC : W ≤ C := sup_le (by rintro _ ⟨u, rfl⟩; exact hA u) (by rintro _ ⟨u, rfl⟩; exact hA' u)
  have hφW : φ ∈ W.topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro h hh
    have h0 : P h = 0 := (hP0.2.2 h).2 ⟨fun u => (Submodule.mem_orthogonal _ _).1 hh _ (Submodule.mem_sup_left ⟨u, rfl⟩),
      fun u => (Submodule.mem_orthogonal _ _).1 hh _ (Submodule.mem_sup_right ⟨u, rfl⟩)⟩
    have e : ⟪P h, φ⟫_ℂ = ⟪h, P φ⟫_ℂ := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hP0.1 h φ
    rw [← hφ, ← e, h0, inner_zero_left]
  have hφC : Tm φ ∈ S := Submodule.topologicalClosure_minimal W hWC hC hφW
  obtain ⟨_, ⟨v, rfl⟩, _, ⟨v', rfl⟩, h⟩ := Submodule.mem_sup.1 hφC
  exact ⟨v, v', fun g => by rw [← hTm, ← h]; rfl⟩

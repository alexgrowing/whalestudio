import Formalism.SharpRestriction.CuspSpanNormBounds.StarVecMulDM

open MeasureTheory Matrix Finset

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def phiP (k r : ℕ) (κ τ : ℝ) : PairSp k r → PairSp k r :=
  Prod.map (Prod.map (cjT k r κ τ) (cjT k r κ τ)) (Prod.map (cjT k r κ τ) (cjT k r κ τ))

def phiPI (k r : ℕ) (κ τ : ℝ) : PairSp k r → PairSp k r :=
  Prod.map (Prod.map (cjIT k r κ τ) (cjIT k r κ τ)) (Prod.map (cjIT k r κ τ) (cjIT k r κ τ))

section Meas

variable {k r : ℕ} {κ τ : ℝ}

theorem cjE_coe (hκ : 0 < κ) (hτ : 0 < τ) : ⇑(cjE (k := k) (r := r) hκ hτ) = cjT k r κ τ := rfl

theorem measurable_cjT : Measurable (cjT k r κ τ) := continuous_cjT.measurable

theorem measurable_phiP : Measurable (phiP k r κ τ) :=
  (measurable_cjT.prodMap measurable_cjT).prodMap (measurable_cjT.prodMap measurable_cjT)

theorem measurable_phiPI : Measurable (phiPI k r κ τ) :=
  (continuous_cjIT.measurable.prodMap continuous_cjIT.measurable).prodMap
    (continuous_cjIT.measurable.prodMap continuous_cjIT.measurable)

def phiE (hκ : 0 < κ) (hτ : 0 < τ) : PairSp k r ≃ᵐ PairSp k r where
  toFun := phiP k r κ τ
  invFun := phiPI k r κ τ
  left_inv := fun p => Prod.ext (Prod.ext (cjIT_cjT hκ hτ _) (cjIT_cjT hκ hτ _))
    (Prod.ext (cjIT_cjT hκ hτ _) (cjIT_cjT hκ hτ _))
  right_inv := fun p => Prod.ext (Prod.ext (cjT_cjIT hκ hτ _) (cjT_cjIT hκ hτ _))
    (Prod.ext (cjT_cjIT hκ hτ _) (cjT_cjIT hκ hτ _))
  measurable_toFun := measurable_phiP
  measurable_invFun := measurable_phiPI

theorem phiE_coe (hκ : 0 < κ) (hτ : 0 < τ) : ⇑(phiE (k := k) (r := r) hκ hτ) = phiP k r κ τ := rfl

theorem besselIntg_trD (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r) (κN₁ : ENNReal)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1)
    (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (g : Mx k r) (p : PairSp k r) :
    besselIntg (trD L κ τ κN₁ hz hz' hπ hπ' hμW hμW') F (cj k r κ τ g) (phiP k r κ τ p) =
      besselIntg L (fun x => F (cj k r κ τ x)) g p := by
  obtain ⟨⟨h, n⟩, ⟨h', n'⟩⟩ := p
  simp only [besselIntg, trD, phiP, Prod.map_apply, of_cjT]
  rw [psi_cj hκ hτ L.hz.1, psi_cj hκ hτ L.hz'.1, cjI_cj hκ hτ, ← cj_inv hκ hτ (Matrix.of h'), cjI_cj hκ hτ,
    ← cj_inv hκ hτ, ← cj_inv hκ hτ, ← cj_mul hκ hτ, ← cj_mul hκ hτ, ← cj_mul hκ hτ, ← cj_mul hκ hτ]
  rfl

theorem map_cjT_univ (μ : Measure (Mt k r)) : (μ.map (cjT k r κ τ)) Set.univ = μ Set.univ := by
  rw [Measure.map_apply measurable_cjT MeasurableSet.univ, Set.preimage_univ]

theorem measurable_lmulM (s : Mx k r) : Measurable (lmulM (k := k) (r := r) s) := by
  have : Continuous (lmulM (k := k) (r := r) s) := by
    show Continuous fun x : Mt k r => (s * (Matrix.of x : Mx k r) : Mx k r)
    exact continuous_const.matrix_mul (continuous_id : Continuous fun x : Mt k r => x)
  exact this.measurable

theorem lmulM_cjT (hκ : 0 < κ) (hτ : 0 < τ) (s : Mx k r) (x : Mt k r) :
    lmulM s (cjT k r κ τ x) = cjT k r κ τ (lmulM (cjI k r κ τ s) x) := by
  funext i j
  show (s * cj k r κ τ (Matrix.of x)) i j = cj k r κ τ (cjI k r κ τ s * Matrix.of x) i j
  rw [cj_mul hκ hτ, cj_cjI hκ hτ]

theorem isHaarOn_map_cjT (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    {μ : Measure (Mt k r)} (h : IsHaarOn (UWset k r z) μ) :
    IsHaarOn (UWset k r ((τ : ℂ) • z)) (μ.map (cjT k r κ τ)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [UWset_smul hτ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← cjE_coe hκ hτ]; exact MeasurableEquiv.sigmaFinite_map _
  · exact (Measure.map_ne_zero_iff measurable_cjT.aemeasurable).mpr h2
  · rw [← cjE_coe hκ hτ, MeasurableEquiv.map_apply]
    convert h3 using 2
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, cjE_coe, of_cjT, cj_mem_UWset_iff hκ hτ hz]
  · intro s hs
    have hs' : cjI k r κ τ s ∈ UWset k r z := by
      rw [← cj_mem_UWset_iff hκ hτ hz, cj_cjI hκ hτ]; exact hs
    rw [Measure.map_map (measurable_lmulM s) measurable_cjT]
    have e : lmulM s ∘ cjT k r κ τ = cjT k r κ τ ∘ lmulM (cjI k r κ τ s) := funext (lmulM_cjT hκ hτ s)
    rw [e, ← Measure.map_map measurable_cjT (measurable_lmulM _), h4 _ hs']

theorem sFinite_haarLie (S : Set (Mx k r)) (κN : ENNReal) : SFinite (haarLie S κN) := by
  unfold haarLie; infer_instance

theorem pairMeas_eq_map (L L₁ : LocBessel k r) (hW : L₁.μW = L.μW.map (cjT k r κ τ))
    (hW' : L₁.μW' = L.μW'.map (cjT k r κ τ)) (hN : L₁.μN = L.μN.map (cjT k r κ τ)) :
    pairMeas L₁ = (pairMeas L).map (phiP k r κ τ) := by
  have := L.hμW.1.1
  have := L.hμW'.1.1
  have : SFinite L.μN := sFinite_haarLie _ _
  unfold pairMeas
  rw [hW, hW', hN, Measure.map_prod_map _ _ measurable_cjT measurable_cjT,
    Measure.map_prod_map _ _ measurable_cjT measurable_cjT,
    Measure.map_prod_map _ _ (measurable_cjT.prodMap measurable_cjT) (measurable_cjT.prodMap measurable_cjT)]
  rfl

abbrev IxE (k r : ℕ) := Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool

def scF (k r : ℕ) (κ τ : ℝ) (p : IxE k r) : ℝ := (tV k r κ τ p.1)⁻¹ * tV k r κ τ p.2.1

def scFI (k r : ℕ) (κ τ : ℝ) (p : IxE k r) : ℝ := tV k r κ τ p.1 * (tV k r κ τ p.2.1)⁻¹

def scE (k r : ℕ) (κ τ : ℝ) : EuclideanSpace ℝ (IxE k r) →ₗ[ℝ] EuclideanSpace ℝ (IxE k r) where
  toFun y := WithLp.toLp 2 (fun p => scF k r κ τ p * y p)
  map_add' x y := by ext p; simp [mul_add]
  map_smul' c x := by ext p; simp; ring

def scEI (k r : ℕ) (κ τ : ℝ) : EuclideanSpace ℝ (IxE k r) →ₗ[ℝ] EuclideanSpace ℝ (IxE k r) where
  toFun y := WithLp.toLp 2 (fun p => scFI k r κ τ p * y p)
  map_add' x y := by ext p; simp [mul_add]
  map_smul' c x := by ext p; simp; ring

theorem scE_apply (y : EuclideanSpace ℝ (IxE k r)) (p : IxE k r) : scE k r κ τ y p = scF k r κ τ p * y p := rfl

theorem scEI_apply (y : EuclideanSpace ℝ (IxE k r)) (p : IxE k r) : scEI k r κ τ y p = scFI k r κ τ p * y p := rfl

theorem scE_scEI (hκ : 0 < κ) (hτ : 0 < τ) (y : EuclideanSpace ℝ (IxE k r)) : scE k r κ τ (scEI k r κ τ y) = y := by
  ext p
  rw [scE_apply, scEI_apply, ← mul_assoc]
  have h1 := (tV_pos (k := k) (r := r) hκ hτ p.1).ne'
  have h2 := (tV_pos (k := k) (r := r) hκ hτ p.2.1).ne'
  simp only [scF, scFI]
  field_simp

theorem unrealify_scE (y : EuclideanSpace ℝ (IxE k r)) :
    unrealify (scE k r κ τ y) = cj k r κ τ (unrealify y) := by
  ext i j
  rw [cj_apply]
  apply Complex.ext <;> simp [unrealify, scE_apply, scF]

theorem scE_realify (X : Mx k r) :
    scE k r κ τ ((WithLp.equiv 2 _).symm (realifyFun X)) = (WithLp.equiv 2 _).symm (realifyFun (cj k r κ τ X)) := by
  ext ⟨i, j, b⟩
  rw [scE_apply]
  cases b <;> simp [realifyFun, cj_apply, scF]

theorem scEI_realify (X : Mx k r) :
    scEI k r κ τ ((WithLp.equiv 2 _).symm (realifyFun X)) =
      (WithLp.equiv 2 _).symm (realifyFun (cjI k r κ τ X)) := by
  ext ⟨i, j, b⟩
  rw [scEI_apply]
  cases b <;> simp [realifyFun, cjI_apply, scFI]

theorem cj_smul (c : ℂ) (X : Mx k r) : cj k r κ τ (c • X) = c • cj k r κ τ X := by
  unfold cj; rw [Matrix.mul_smul, Matrix.smul_mul]

theorem exp_cj (hκ : 0 < κ) (hτ : 0 < τ) (X : Mx k r) :
    NormedSpace.exp (cj k r κ τ X) = cj k r κ τ (NormedSpace.exp X) := by
  have hu : IsUnit (dMi k r κ τ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse (dMi_mul_dM hκ hτ))
  unfold cj
  rw [← dMi_inv hκ hτ]
  exact Matrix.exp_conj _ _ hu

theorem cj_mem_lieOf_iff (hκ : 0 < κ) (hτ : 0 < τ) (X : Mx k r) :
    cj k r κ τ X ∈ lieOf (Nset k r) ↔ X ∈ lieOf (Nset k r) := by
  unfold lieOf
  simp only [Set.mem_ofPred_eq, ← cj_smul, exp_cj hκ hτ, cj_mem_Nset_iff hκ hτ]

theorem span_mem_of_image {f : EuclideanSpace ℝ (IxE k r) →ₗ[ℝ] EuclideanSpace ℝ (IxE k r)}
    {S : Set (EuclideanSpace ℝ (IxE k r))} (hS : f '' S ⊆ S) {x : EuclideanSpace ℝ (IxE k r)}
    (hx : x ∈ Submodule.span ℝ S) : f x ∈ Submodule.span ℝ S := by
  have h : f x ∈ (Submodule.span ℝ S).map f := Submodule.mem_map_of_mem hx
  rw [Submodule.map_span] at h
  exact Submodule.span_mono hS h

theorem scE_mem (hκ : 0 < κ) (hτ : 0 < τ) :
    ∀ x ∈ lieE (Nset k r), scE k r κ τ x ∈ lieE (Nset k r) := by
  intro x hx
  refine span_mem_of_image ?_ hx
  rintro _ ⟨_, ⟨X, hX, rfl⟩, rfl⟩
  exact ⟨cj k r κ τ X, (cj_mem_lieOf_iff hκ hτ X).mpr hX, (scE_realify X).symm⟩

theorem scEI_mem (hκ : 0 < κ) (hτ : 0 < τ) :
    ∀ x ∈ lieE (Nset k r), scEI k r κ τ x ∈ lieE (Nset k r) := by
  intro x hx
  refine span_mem_of_image ?_ hx
  rintro _ ⟨_, ⟨X, hX, rfl⟩, rfl⟩
  refine ⟨cjI k r κ τ X, ?_, (scEI_realify X).symm⟩
  rw [← cj_mem_lieOf_iff hκ hτ, cj_cjI hκ hτ]; exact hX

open Classical in

def deltaN (k r : ℕ) (κ τ : ℝ) : ℝ :=
  if h : ∀ x ∈ lieE (Nset k r), scE k r κ τ x ∈ lieE (Nset k r) then
    |(LinearMap.det ((scE k r κ τ).restrict h))⁻¹|
  else 1

theorem det_scE_ne (hκ : 0 < κ) (hτ : 0 < τ) :
    LinearMap.det ((scE k r κ τ).restrict (scE_mem hκ hτ)) ≠ 0 := by
  have hc : ((scE k r κ τ).restrict (scE_mem hκ hτ)) ∘ₗ ((scEI k r κ τ).restrict (scEI_mem hκ hτ)) =
      LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_restrict_apply, LinearMap.id_apply]
    exact scE_scEI hκ hτ _
  have := congrArg LinearMap.det hc
  rw [LinearMap.det_comp, LinearMap.det_id] at this
  exact left_ne_zero_of_mul_eq_one this

theorem deltaN_pos (hκ : 0 < κ) (hτ : 0 < τ) : 0 < deltaN k r κ τ := by
  rw [deltaN, dif_pos (scE_mem hκ hτ)]
  exact abs_pos.mpr (inv_ne_zero (det_scE_ne hκ hτ))

theorem unrealify_add' (x y : EuclideanSpace ℝ (IxE k r)) : unrealify (x + y) = unrealify x + unrealify y := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

theorem unrealify_smul' (c : ℝ) (x : EuclideanSpace ℝ (IxE k r)) : unrealify (c • x) = (c : ℂ) • unrealify x := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

def unrealL' (k r : ℕ) : EuclideanSpace ℝ (IxE k r) →ₗ[ℝ] Mx k r where
  toFun := unrealify
  map_add' := unrealify_add'
  map_smul' := by
    intro c x
    rw [unrealify_smul']
    exact Complex.coe_smul c _

open scoped Matrix.Norms.Operator in
theorem continuous_expM' : Continuous (fun X : Mx k r => NormedSpace.exp X) := NormedSpace.exp_continuous

def expL (S : Set (Mx k r)) : lieE S → Mt k r :=
  fun x i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (IxE k r))) i j

theorem continuous_expL (S : Set (Mx k r)) : Continuous (expL S) := by
  have h1 : Continuous (fun x : EuclideanSpace ℝ (IxE k r) => unrealify x) :=
    (unrealL' k r).continuous_of_finiteDimensional
  have h3 : Continuous (fun x : lieE S => (unrealify (x : EuclideanSpace ℝ (IxE k r)) : Mx k r)) :=
    h1.comp continuous_subtype_val
  exact continuous_expM'.comp h3

theorem cjT_expL (hκ : 0 < κ) (hτ : 0 < τ) (x : lieE (Nset k r)) :
    cjT k r κ τ (expL (Nset k r) x) = expL (Nset k r) ((scE k r κ τ).restrict (scE_mem hκ hτ) x) := by
  funext i j
  show cj k r κ τ (NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (IxE k r)))) i j =
    NormedSpace.exp (unrealify (((scE k r κ τ).restrict (scE_mem hκ hτ) x : lieE (Nset k r)) :
      EuclideanSpace ℝ (IxE k r))) i j
  rw [LinearMap.coe_restrict_apply, unrealify_scE, exp_cj hκ hτ]

theorem map_haarLie_N (hκ : 0 < κ) (hτ : 0 < τ) (κN : ENNReal) :
    (haarLie (Nset k r) κN).map (cjT k r κ τ) =
      haarLie (Nset k r) (κN * ENNReal.ofReal (deltaN k r κ τ)) := by
  have hA := det_scE_ne (k := k) (r := r) hκ hτ
  have e : cjT k r κ τ ∘ expL (Nset k r) = expL (Nset k r) ∘ ((scE k r κ τ).restrict (scE_mem hκ hτ)) :=
    funext (cjT_expL hκ hτ)
  have h0 : haarLie (Nset k r) κN = κN • (volume : Measure (lieE (Nset k r))).map (expL (Nset k r)) := rfl
  have h1 : haarLie (Nset k r) (κN * ENNReal.ofReal (deltaN k r κ τ)) =
      (κN * ENNReal.ofReal (deltaN k r κ τ)) • (volume : Measure (lieE (Nset k r))).map (expL (Nset k r)) := rfl
  rw [h0, h1, Measure.map_smul, Measure.map_map measurable_cjT (continuous_expL _).measurable, e,
    ← Measure.map_map (continuous_expL _).measurable
      ((scE k r κ τ).restrict (scE_mem hκ hτ)).continuous_of_finiteDimensional.measurable,
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hA, Measure.map_smul, smul_smul, deltaN,
    dif_pos (scE_mem hκ hτ)]

theorem pairMeas_trD (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1) :
    pairMeas (trD L κ τ (L.κN * ENNReal.ofReal (deltaN k r κ τ)) hz hz' hπ hπ' hμW hμW') =
      (pairMeas L).map (phiP k r κ τ) :=
  pairMeas_eq_map L _ rfl rfl (map_haarLie_N hκ hτ L.κN).symm

theorem J_eq_integral (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (g : Mx k r) :
    L.J F g = ∫ p, besselIntg L F g p ∂(pairMeas L) := rfl

theorem J_trD (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1)
    (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (g : Mx k r) :
    (trD L κ τ (L.κN * ENNReal.ofReal (deltaN k r κ τ)) hz hz' hπ hπ' hμW hμW').J F (cj k r κ τ g) =
      L.J (fun x => F (cj k r κ τ x)) g := by
  refine (J_eq_integral (trD L κ τ (L.κN * ENNReal.ofReal (deltaN k r κ τ)) hz hz' hπ hπ' hμW hμW') F
    (cj k r κ τ g)).trans ?_
  rw [J_eq_integral, pairMeas_trD hκ hτ, ← phiE_coe hκ hτ, integral_map_equiv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  exact besselIntg_trD hκ hτ L _ hz hz' hπ hπ' hμW hμW' F g p

theorem OrbInt_trD (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r) (κN₁ : ENNReal)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1)
    (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (g : Mx k r) (s : ENNReal) (ν : Measure (PairSp k r)) :
    OrbInt (trD L κ τ κN₁ hz hz' hπ hπ' hμW hμW') F (cj k r κ τ g) (s • ν.map (phiP k r κ τ)) =
      (s.toReal : ℂ) • OrbInt L (fun x => F (cj k r κ τ x)) g ν := by
  unfold OrbInt
  rw [integral_smul_measure, ← phiE_coe hκ hτ, integral_map_equiv, Complex.coe_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  exact besselIntg_trD hκ hτ L _ hz hz' hπ hπ' hμW hμW' F g p

end Meas

end Formalism.MainNotions.FrameBoundFromBesselTorus

import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMatMemUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversion
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.MeasTransport

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem star_smul_vec [hU : Unram F E] {r : ℕ} (a : F) (c : Fin r → E) : star (a • c) = a • star c := by
  funext i
  show star (a • c i) = a • star (c i)
  rw [Algebra.smul_def, Algebra.smul_def, star_mul', hU.star_fix, mul_comm]

def trForm [Unram F E] (r : ℕ) : LinearMap.BilinForm F (Fin r → E) :=
  LinearMap.mk₂ F (fun c b => Algebra.trace F E (star c ⬝ᵥ b))
    (fun c c' b => by simp only [star_add, add_dotProduct, map_add])
    (fun a c b => by simp only [star_smul_vec, smul_dotProduct, map_smul])
    (fun c b b' => by simp only [dotProduct_add, map_add])
    (fun a c b => by simp only [dotProduct_smul, map_smul])

theorem trForm_apply [Unram F E] {r : ℕ} (c b : Fin r → E) :
    trForm (F := F) r c b = Algebra.trace F E (star c ⬝ᵥ b) := rfl

theorem trace_star [hU : Unram F E] (z : E) : Algebra.trace F E (star z) = Algebra.trace F E z := by
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := starRingAut) (fun a => hU.star_fix a)
  exact Algebra.trace_eq_of_algEquiv σ z

theorem trForm_symm [Unram F E] (r : ℕ) : (trForm (F := F) (E := E) r).IsSymm := by
  refine ⟨fun c b => ?_⟩
  rw [trForm_apply, trForm_apply, ← trace_star (F := F) (star b ⬝ᵥ c), ← star_dotProduct_star, star_star]

theorem trForm_sepLeft [hU : Unram F E] (r : ℕ) (c : Fin r → E) (h : ∀ b, trForm (F := F) r c b = 0) : c = 0 := by
  haveI : CharZero F := hU.charZero
  by_contra hc
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hc (funext h')
  have h1 := h (Pi.single i (star (c i))⁻¹)
  rw [trForm_apply, dotProduct_single, Pi.star_apply, mul_inv_cancel₀ (star_ne_zero.mpr hi),
    ← map_one (algebraMap F E), Algebra.trace_algebraMap, hU.finrank_eq] at h1
  norm_num at h1

theorem trForm_nondeg [Unram F E] (r : ℕ) : (trForm (F := F) (E := E) r).Nondegenerate := by
  refine ⟨fun c h => trForm_sepLeft (F := F) r c h, fun b h => trForm_sepLeft (F := F) r b fun c => ?_⟩
  rw [(trForm_symm r).eq]; exact h c

theorem kerL_eq [hU : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)}
    (hx : A.IsIsom x j) (y' y : A.L) :
    A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := by
  obtain ⟨b⟩ := (GlobalTheory.JR.Et.quadratic_structure F E A).1
  haveI : Module.Free A.K A.L := Module.Free.of_basis b
  haveI : Module.Finite A.K A.L := Module.Finite.of_basis b
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : Module.Finite F A.L := Module.Finite.trans A.K A.L
  haveI : Module.Finite E A.L := Module.Finite.of_restrictScalars_finite F E A.L
  unfold Et.kerL Et.psiK
  rw [hx, Algebra.trace_trace (R := F) (S := E) (T := A.L), ← Algebra.trace_trace (R := F) (S := A.K) (T := A.L)]
  congr 2
  rw [show algebraMap A.K A.L x * star y' * y = x • (star y' * y) by rw [Algebra.smul_def, mul_assoc], map_smul,
    smul_eq_mul]

end GlobalTheory.JR.MeasTransport

namespace GlobalTheory.JR.MeasTransport

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem addChar_sum (ψ : AddChar F ℂ) {ι : Type} (s : Finset ι) (f : ι → F) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem pi_selfDual [hU : Unram F E] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (r : ℕ) (M : Meas r F E) :
    letI := M.mE
    SelfDual (Measure.pi fun _ : Fin r => M.μE) (fun a b => ψ (trForm (F := F) r a b)) := by
  letI := M.mE
  haveI := M.bE
  haveI := M.haarE
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi

  let O : AddSubgroup (Fin r → E) :=
    { carrier := {v | ∀ i, ‖v i‖ ≤ 1}
      zero_mem' := by intro i; simp
      add_mem' := fun {a b} ha hb i => (IsUltrametricDist.norm_add_le_max (a i) (b i)).trans (max_le (ha i) (hb i))
      neg_mem' := fun {a} ha i => by simpa using ha i }
  have hmem : ∀ v, v ∈ O ↔ ∀ i, ‖v i‖ ≤ 1 := fun v => Iff.rfl
  have hOset : (O : Set (Fin r → E)) = Set.univ.pi fun _ => Metric.closedBall (0 : E) 1 := by
    ext v; simp [O, Set.mem_pi]
  have hOo : IsOpen (O : Set (Fin r → E)) := by
    rw [hOset]; exact isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hOk : IsCompact (O : Set (Fin r → E)) := by
    rw [hOset]; exact isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hc := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.2
  have hdual : {y | ∀ x ∈ O, ψ (trForm (F := F) r x y) = 1} = (O : Set (Fin r → E)) := by
    ext y
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, hmem]
    constructor
    · intro h i
      refine (hc (y i)).1 fun e he => ?_
      have h1 := h (Pi.single i (star e)) (by
        intro k
        by_cases hk : k = i
        · subst hk; simp [hU.norm_star, he]
        · simp [hk])
      rw [trForm_apply] at h1
      simpa [dotProduct, Pi.single_apply, apply_ite star] using h1
    · intro h x hx
      rw [trForm_apply, dotProduct, map_sum, addChar_sum]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [Pi.star_apply]
      exact (hc (y i)).2 (h i) (star (x i)) (by rw [hU.norm_star]; exact hx i)
  have hvol : (Measure.pi fun _ : Fin r => M.μE) O = 1 := by
    rw [hOset, Measure.pi_pi]; simp [M.volE]
  haveI : (Measure.pi fun _ : Fin r => M.μE).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have key := (GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ (Fin r → E) (trForm r) (trForm_symm r) (trForm_nondeg r) (Measure.pi fun _ : Fin r => M.μE) inferInstance).1 O
    hOo hOk |>.1
  rw [key, hdual, hvol, one_mul]

theorem map_selfDual [hU : Unram F E] [MeasurableSpace E] [BorelSpace E] (A : Et F E) (ψ : AddChar F ℂ) {r : ℕ}
    {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j) (μ : Measure A.L) (hμ : SelfDual μ (A.kerL ψ x)) :
    SelfDual (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) := by
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi

  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  let jF : A.L ≃ₗ[F] (Fin r → E) := j.restrictScalars F
  have hc : Continuous jF := IsModuleTopology.continuous_of_linearMap jF.toLinearMap
  have hcs : Continuous jF.symm := IsModuleTopology.continuous_of_linearMap jF.symm.toLinearMap
  let jC : A.L ≃L[F] (Fin r → E) := { jF with continuous_toFun := hc, continuous_invFun := hcs }
  have hcoe : (⇑jC : A.L → Fin r → E) = ⇑j := rfl
  have hme : MeasurableEmbedding (⇑j) := by rw [← hcoe]; exact jC.toHomeomorph.measurableEmbedding
  haveI := hμ.1
  have hfour : ∀ (g : (Fin r → E) → ℂ) (y : A.L),
      fourB (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) g (j y) = fourB μ (A.kerL ψ x) (g ∘ j) y := by
    intro g y
    unfold fourB
    rw [hme.integral_map]
    simp only [Function.comp, kerL_eq A ψ hx, trForm_apply]
  refine ⟨by rw [← hcoe]; exact jC.isAddHaarMeasure_map μ, fun f hf v => ?_⟩
  obtain ⟨y, rfl⟩ := j.surjective v
  have hfj : IsTest (f ∘ j) := by
    refine ⟨hf.1.comp_continuous (by rw [← hcoe]; exact jC.continuous), ?_⟩
    rw [← hcoe]; exact hf.2.comp_homeomorph jC.toHomeomorph
  rw [hfour]
  have h2 : (fourB (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) f) ∘ j = fourB μ (A.kerL ψ x) (f ∘ j) :=
    funext fun y => hfour f y
  rw [h2, hμ.2 _ hfj y]
  simp [map_neg]

theorem map_isIsom_eq_pi : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → (∀ y' y, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) ∧ ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → (letI := M.mE; Measure.map j μ = Measure.pi fun _ : Fin r => M.μE) := by
  intro F E _ _ _ _ hU A ψ hψ r M x j hx
  refine ⟨fun y' y => kerL_eq A ψ hx y' y, fun μ hμ => ?_⟩
  letI := M.mE
  haveI := M.bE
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi

  obtain ⟨⟨μ0, _, huniq⟩, _⟩ := GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ (Fin r → E) (trForm r)
    (trForm_symm r) (trForm_nondeg r)
  exact (huniq _ (map_selfDual A ψ hx μ hμ)).trans (huniq _ (pi_selfDual ψ hψ r M)).symm

end GlobalTheory.JR.MeasTransport

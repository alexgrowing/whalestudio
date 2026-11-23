import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteCompactRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSlowlyIncreasingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCentreAnnihilatorCompatibleMapsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSmoothAdelicFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingRightTranslateMaxCompactStatement

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth.SmoothFinite

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def stabL (φ : Sm E a) : Subgroup (GL (Fin a) (Af E)) where
  carrier := {k | finRep E a k φ = φ}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

theorem height_mul_le (c : GL (Fin a) (Cinf E)) : ∃ B : ℝ, 1 ≤ B ∧ ∀ y, height (y * c) ≤ B * height y := by
  refine ⟨1 + ‖rmul (toL c.val)‖ + ‖lmul (toL (c⁻¹).val)‖,
    by linarith [norm_nonneg (rmul (toL c.val)), norm_nonneg (lmul (toL (c⁻¹).val))], fun y => ?_⟩
  have h1 : toL (y * c).val = rmul (toL c.val) (toL y.val) := rfl
  have h2 : toL ((y * c)⁻¹).val = lmul (toL (c⁻¹).val) (toL (y⁻¹).val) := by
    rw [_root_.mul_inv_rev]; rfl
  have e1 := (rmul (toL c.val)).le_opNorm (toL y.val)
  have e2 := (lmul (toL (c⁻¹).val)).le_opNorm (toL (y⁻¹).val)
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (rmul (toL c.val))
  have n4 := norm_nonneg (lmul (toL (c⁻¹).val))
  unfold height
  rw [h1, h2]
  nlinarith

theorem growth_cptRep {φ : Sm E a} (hφ : φ.1 ∈ growth E a) (k : Kinf E a) : (cptRep E a k φ).1 ∈ growth E a := by
  intro g
  obtain ⟨C, N, hC⟩ := hφ g
  obtain ⟨B, hB, hB'⟩ := height_mul_le (Unitary.toUnits k : GL (Fin a) (Cinf E))
  have C0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N :=
      pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left this hp
  refine ⟨C * B ^ N, N, fun y => ?_⟩
  change ‖φ.1 (g * infGL E a y * infGL E a (Unitary.toUnits k))‖ ≤ _
  rw [mul_assoc, ← map_mul]
  refine (hC _).trans ?_
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (y * Unitary.toUnits k)]) (hB' y) N) C0

theorem spanK_induction {φ : Sm E a} {p : Sm E a → Prop} (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y))
    (hsmul : ∀ (c : ℂ) x, p x → p (c • x)) (hk : ∀ k, p (cptRep E a k φ)) {w : Sm E a}
    (hw : w ∈ spanK E a φ) : p w := by
  induction hw using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hk k
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

theorem fin_cpt_comm (k : GL (Fin a) (Af E)) (c : Kinf E a) :
    finRep E a k * cptRep E a c = cptRep E a c * finRep E a k := by
  change rt E a (finGL E a k) * rt E a (infGL E a (Unitary.toUnits c)) =
    rt E a (infGL E a (Unitary.toUnits c)) * rt E a (finGL E a k)
  rw [← map_mul, ← map_mul, infGL_comm]

variable {φ : Sm E a}

theorem growth_mem (hφ : IsAutForm φ) {w : Sm E a} (hw : w ∈ spanK E a φ) : w.1 ∈ growth E a :=
  spanK_induction (p := fun w : Sm E a => w.1 ∈ growth E a) (zero_mem _)
    (fun x y hx hy => by rw [Submodule.coe_add]; exact add_mem hx hy)
    (fun c x hx => by rw [Submodule.coe_smul]; exact Submodule.smul_mem _ c hx)
    (fun k => growth_cptRep (φ := φ) hφ.growth k) hw

theorem left_mem (hφ : IsAutForm φ) {w : Sm E a} (hw : w ∈ spanK E a φ) :
    ∀ γ g, w.1 (ratGL E a γ * g) = w.1 g :=
  spanK_induction (p := fun w : Sm E a => ∀ γ g, w.1 (ratGL E a γ * g) = w.1 g) (fun _ _ => rfl)
    (fun x y hx hy γ g => by simp [hx γ g, hy γ g])
    (fun c x hx γ g => by simp [hx γ g])
    (fun k γ g => by
      change φ.1 (ratGL E a γ * g * infGL E a (Unitary.toUnits k)) = φ.1 (g * infGL E a (Unitary.toUnits k))
      rw [mul_assoc, hφ.left]) hw

theorem fixed_mem {k : GL (Fin a) (Af E)} (hk : k ∈ stabL φ) {w : Sm E a} (hw : w ∈ spanK E a φ) :
    finRep E a k w = w :=
  spanK_induction (p := fun w : Sm E a => finRep E a k w = w) (map_zero _)
    (fun x y hx hy => by rw [map_add, hx, hy])
    (fun c x hx => by rw [map_smul, hx])
    (fun c => by
      have hk' : finRep E a k φ = φ := hk
      rw [← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk']) hw

theorem killed_mem {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (h0 : z φ = 0) {w : Sm E a}
    (hw : w ∈ spanK E a φ) : z w = 0 :=
  spanK_induction (p := fun w : Sm E a => z w = 0) (map_zero _)
    (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
    (fun c x hx => by rw [map_smul, hx, smul_zero])
    (fun c => by
      rw [← Module.End.mul_apply, GlobalTheory.ZalgCpt.zalg_comm_cptRep E a c z hz, Module.End.mul_apply, h0, map_zero]) hw

variable (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α : Lie E a → ℂ}

theorem smoothing_add (hα : IsTest (invSet E a) α) (φ ψ : Sm E a) :
    smoothing ν α (φ + ψ).1 = smoothing ν α φ.1 + smoothing ν α ψ.1 := by
  funext x
  simp only [Pi.add_apply, smoothing]
  refine (integral_congr_ae (.of_forall fun y => ?_)).trans
    (integral_add (hα.integrable_mul ν isOpen_invSet (φ.2 x).continuousOn)
      (hα.integrable_mul ν isOpen_invSet (ψ.2 x).continuousOn))
  by_cases h : IsUnit (Matrix.of y) <;> simp [chart, h, mul_add]

theorem smoothing_smul (c : ℂ) (φ : Sm E a) :
    smoothing ν α (c • φ).1 = c • smoothing ν α φ.1 := by
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, smoothing]
  refine (integral_congr_ae (.of_forall fun y => ?_)).trans (integral_const_mul c _)
  by_cases h : IsUnit (Matrix.of y) <;> simp [chart, h, mul_left_comm]

def smoothMap (hα : IsTest (invSet E a) α) (W : Submodule ℂ (Sm E a)) : W →ₗ[ℂ] Sm E a where
  toFun w := ⟨smoothing ν α w.1.1, GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα w.1.1 w.1.2⟩
  map_add' w w' := Subtype.ext (smoothing_add ν hα w.1 w'.1)
  map_smul' c w := Subtype.ext (smoothing_smul ν c w.1)

theorem smoothMap_mem (hα : IsTest (invSet E a) α) (hK : KInv α) (hφ : IsAutForm φ) :
    smoothMap ν hα (spanK E a φ) ∈ mapsJ φ (stabL φ) := by
  refine ⟨⟨fun k w => ?_, fun w => ⟨?_, fun γ g => ?_, fun k hk => ?_⟩⟩, fun z hz h0 w => ?_⟩
  · apply Subtype.ext; funext g
    exact GlobalTheory.T.smoothing_right_translate_maxCompact E a ν α hK w.1.1 k g
  · intro l
    obtain ⟨β, hβ, e⟩ : ∃ β, IsTest (invSet E a) β ∧
        ((l.map (lie E a)).prod (smoothMap ν hα (spanK E a φ) w)).1 = smoothing ν β w.1.1 := by
      induction l with
      | nil => exact ⟨α, hα, rfl⟩
      | cons X l ih =>
        obtain ⟨β, hβ, e⟩ := ih
        refine ⟨dens X β, isTest_dens X hβ, funext fun g => ?_⟩
        rw [List.map_cons, List.prod_cons, Module.End.mul_apply, lie_apply, e]
        exact GlobalTheory.T.lieDerivative_realLieSmoothing_eq_density E a ν β hβ w.1.1 w.1.2 X g
    rw [e]
    exact GlobalTheory.T.realLieSmoothing_mem_slowlyIncreasing E a ν β hβ w.1.1 (growth_mem hφ w.2)
  · show smoothing ν α w.1.1 (ratGL E a γ * g) = smoothing ν α w.1.1 g
    have hl := left_mem hφ w.2
    simp only [smoothing, chart, mul_assoc, hl]
  · apply Subtype.ext; funext g
    show smoothing ν α w.1.1 (g * finGL E a k) = smoothing ν α w.1.1 g
    have hw : (fun x => w.1.1 (x * finGL E a k)) = w.1.1 := congrArg Subtype.val (fixed_mem hk w.2)
    simp only [smoothing]
    rw [← chart_rt_fin, hw]
  · show (z ⟨smoothing ν α w.1.1, GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα w.1.1 w.1.2⟩) = 0
    apply Subtype.ext
    rw [GlobalTheory.T.centreEnvelopingAlgebra_commute_realLieSmoothing E a ν α hα w.1 _ z hz, killed_mem hz h0 w.2]
    funext g
    simp [smoothing, chart]

end

theorem exists_finite_space : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a), IsAutForm φ →
    ∃ V : Submodule ℂ (Sm E a), FiniteDimensional ℂ V ∧ V ≤ tame E a ∧ ∀ α, IsTest (invSet E a) α → KInv α →
      ∃ h : smoothing ν α φ.1 ∈ Sm E a, (⟨smoothing ν α φ.1, h⟩ : Sm E a) ∈ V := by
  intro hP E _ _ _ a ν _ φ hφ
  let w0 : spanK E a φ := ⟨φ, self_mem_spanK φ⟩
  haveI := GlobalTheory.T.finiteDimensional_centreAnnihilatorCompatibleMaps hP E a φ hφ (stabL φ) hφ.level
  refine ⟨(mapsJ φ (stabL φ)).map (LinearMap.applyₗ w0), inferInstance, ?_, fun α hα hK =>
    ⟨GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα φ.1 φ.2, smoothMap ν hα _, smoothMap_mem ν hα hK hφ, rfl⟩⟩
  rintro _ ⟨T, hT, rfl⟩
  exact (hT.1.2 w0).1

end GlobalTheory.AutGrowth.SmoothFinite

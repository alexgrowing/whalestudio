import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.L1

section General

variable {G Γ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [MeasurableSpace Γ] [BorelSpace Γ]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem ofFn_prod_single {M : Type} [Monoid M] :
    ∀ (k : ℕ) (a : Fin k → M) (j : Fin k), (∀ i, i ≠ j → a i = 1) → (List.ofFn a).prod = a j := by
  intro k
  induction k with
  | zero => intro a j; exact j.elim0
  | succ k ih =>
    intro a j h
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun j' => ?_) j (motive := fun j => (∀ i, i ≠ j → a i = 1) → a 0 * (List.ofFn fun i => a i.succ).prod = a j) h
    · intro h
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact h _ (Fin.succ_ne_zero i)
    · intro h
      rw [h 0 (Fin.succ_ne_zero j').symm, one_mul]
      exact ih (fun i => a i.succ) j' fun i hi => h _ (fun e => hi (Fin.succ_injective _ e))

private theorem ofFn_mulSingle {k : ℕ} (g : Fin k → G) :
    (List.ofFn fun i => (Pi.mulSingle i (g i) : Fin k → G)).prod = g := by
  funext j
  have e := map_list_prod (Pi.evalMonoidHom (fun _ : Fin k => G) j)
    (List.ofFn fun i => (Pi.mulSingle i (g i) : Fin k → G))
  simp only [Pi.evalMonoidHom_apply] at e
  rw [e, List.map_ofFn]
  refine (ofFn_prod_single k _ j fun i hi => ?_).trans ?_
  · simp [Pi.mulSingle_eq_of_ne hi.symm]
  · simp

private theorem continuous_ofFn_prod : ∀ (k : ℕ) (s : Fin k → G →* Γ), (∀ i, Continuous (s i)) →
    Continuous fun g : Fin k → G => (List.ofFn fun i => s i (g i)).prod := by
  intro k
  induction k with
  | zero => intro s _; simpa using continuous_const
  | succ k ih =>
    intro s hs
    simp only [List.ofFn_succ, List.prod_cons]
    exact ((hs 0).comp (continuous_apply 0)).mul
      ((ih (fun i => s i.succ) fun i => hs _).comp
        (continuous_pi fun i => continuous_apply i.succ))

private theorem inner_cc (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (π : UnitaryRep G H)
    (f : CompactlySupportedContinuousMap G ℂ) (w v : H) :
    ⟪w, π.integrated μ (UnitaryRep.ccToL1 μ f) v⟫_ℂ = ∫ g, f g * ⟪w, π g v⟫_ℂ ∂μ := by
  have hint : Integrable (fun g => f g • π g v) μ :=
    (f.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  rw [UnitaryRep.integrated_ccToL1_apply, ← integral_inner hint]
  simp only [inner_smul_right]

private theorem inner_ofFn_prod (μ : Measure G) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ]
    (π : UnitaryRep Γ H) : ∀ (k : ℕ) (s : Fin k → G →* Γ) (hs : ∀ i, Continuous (s i))
    (φ : Fin k → CompactlySupportedContinuousMap G ℂ) (w v : H),
    ⟪w, (List.ofFn fun i => (π.compHom (s i) (hs i)).integrated μ (UnitaryRep.ccToL1 μ (φ i))).prod v⟫_ℂ =
      ∫ g : Fin k → G, (∏ i, φ i (g i)) * ⟪w, π (List.ofFn fun i => s i (g i)).prod v⟫_ℂ
        ∂(Measure.pi fun _ => μ) := by
  intro k
  induction k with
  | zero =>
    intro s hs φ w v
    rw [Measure.pi_of_empty (fun _ : Fin 0 => μ) (fun i => i.elim0), integral_dirac]
    simp
  | succ k ih =>
    intro s hs φ w v
    have hint : ∀ i, Integrable (φ i) μ := fun i =>
      (φ i).continuous.integrable_of_hasCompactSupport (φ i).hasCompactSupport
    have hF : Integrable (fun g : Fin (k + 1) → G =>
        (∏ i, φ i (g i)) * ⟪w, π (List.ofFn fun i => s i (g i)).prod v⟫_ℂ)
        (Measure.pi fun _ => μ) := by
      refine (Integrable.fintype_prod (f := fun i => (φ i : G → ℂ)) hint).mul_bdd
        (c := ‖w‖ * ‖v‖) ?_ (Filter.Eventually.of_forall fun g => π.norm_inner_orbit_le w v _)
      exact (continuous_const.inner ((π.continuous_orbit v).comp
        (continuous_ofFn_prod _ s hs))).aestronglyMeasurable
    have mp := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0).symm
    rw [← mp.integral_comp' _]
    refine Eq.trans ?_ (integral_prod _ (mp.integrable_comp_of_integrable hF)).symm
    rw [List.ofFn_succ, List.prod_cons, ContinuousLinearMap.mul_apply, inner_cc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [UnitaryRep.compHom_apply]
    rw [UnitaryRep.inner_map_right, ih (fun i => s i.succ) (fun i => hs _) (fun i => φ i.succ),
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.prod_univ_succ, List.ofFn_succ,
      List.prod_cons, Fin.insertNthEquiv_zero, Fin.cons_zero, Fin.cons_succ]
    show _ = (φ 0 x * ∏ i, φ i.succ (g i)) *
      ⟪w, π (s 0 x * (List.ofFn fun i => s i.succ (g i)).prod) v⟫_ℂ
    rw [UnitaryRep.map_mul_apply, UnitaryRep.inner_map_right π (s 0 x) w]
    ring

end General

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.tensOp :
    UpperTheory.ConvolutionTheory.L1.TensOp := by
  intro F E _ _ _ _ _ σ m D n νE _ νF _ hν s hs hposition H _ _ _ π φ β hβ
  obtain ⟨hcg, -, hmul, hcont, -⟩ := UpperTheory.ConvolutionTheory.L1.archBasic F E σ m D n
  have hglue : ∀ g : Fin (m + 1) → archGroup F n,
      UpperTheory.ConvolutionTheory.L1.glueA D n g = (List.ofFn fun i => s i (g i)).prod := by
    intro g
    have e := map_list_prod (MonoidHom.mk' (UpperTheory.ConvolutionTheory.L1.glueA D n) hmul)
      (List.ofFn fun i => (Pi.mulSingle i (g i) : Fin (m + 1) → archGroup F n))
    rw [UpperTheory.ConvolutionTheory.L1.ofFn_mulSingle, List.map_ofFn] at e
    refine e.trans ?_
    congr 1
    congr 1
    funext i
    exact (hposition i (g i)).symm
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
  rw [UpperTheory.ConvolutionTheory.L1.inner_ofFn_prod, UpperTheory.ConvolutionTheory.L1.inner_cc]
  have hm : Continuous fun x : archGroup E n => β x * ⟪w, π x v⟫_ℂ :=
    β.continuous.mul (continuous_const.inner (π.continuous_orbit v))
  have e1 : ∫ x, β x * ⟪w, π x v⟫_ℂ ∂νE = ∫ x, β x * ⟪w, π x v⟫_ℂ
      ∂(Measure.map (UpperTheory.ConvolutionTheory.L1.glueA D n) (Measure.pi fun _ => νF)) := by
    rw [← hν]
  rw [e1, integral_map hcont.aemeasurable hm.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only
  rw [hβ, hglue g]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hglue g, hcg]

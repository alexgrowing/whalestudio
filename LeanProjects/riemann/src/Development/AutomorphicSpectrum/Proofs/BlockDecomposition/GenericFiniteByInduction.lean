import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl Topology Matrix GroundTheory.Automorphic
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.AffglAssembly

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem isAutForm_add {φ ψ : Sm E a} (h : IsAutForm φ) (h' : IsAutForm ψ) : IsAutForm (φ + ψ) where
  left γ g := by
    change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
    rw [h.left, h'.left]
  level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
    ((h.level.inter h'.level).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
      have h1 : finRep E a k φ = φ := hk.1
      have h2 : finRep E a k ψ = ψ := hk.2
      change finRep E a k (φ + ψ) = φ + ψ
      rw [map_add, h1, h2]
  kfin := by
    have := h.kfin
    have := h'.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) ⊔
      Submodule.span ℂ (Set.range fun k => cptRep E a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [map_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  zfin := by
    have := h.zfin
    have := h'.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) ⊔
        Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z ψ) '' Zalg E a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [map_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩) (Submodule.subset_span ⟨z, hz, rfl⟩)
  growth g := by
    obtain ⟨C, N, h1⟩ := h.growth g
    obtain ⟨C', N', h2⟩ := h'.growth g
    refine ⟨|C| + |C'|, N + N', fun y => ?_⟩
    have hy := one_le_height y
    have e1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
    have e2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
    have hp : 0 ≤ height y ^ N := by positivity
    have hp' : 0 ≤ height y ^ N' := by positivity
    calc ‖(φ + ψ).1 (g * infGL E a y)‖ ≤ ‖φ.1 (g * infGL E a y)‖ + ‖ψ.1 (g * infGL E a y)‖ := norm_add_le _ _
      _ ≤ C * height y ^ N + C' * height y ^ N' := add_le_add (h1 y) (h2 y)
      _ ≤ |C| * height y ^ (N + N') + |C'| * height y ^ (N + N') := by
        refine add_le_add ?_ ?_
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C) hp).trans
            (mul_le_mul_of_nonneg_left e1 (abs_nonneg C))
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C') hp').trans
            (mul_le_mul_of_nonneg_left e2 (abs_nonneg C'))
      _ = (|C| + |C'|) * height y ^ (N + N') := by ring

theorem isAutForm_smul (c : ℂ) {φ : Sm E a} (h : IsAutForm φ) : IsAutForm (c • φ) where
  left γ g := by
    change c • φ.1 _ = c • φ.1 _
    rw [h.left]
  level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
    (h.level.mem_nhds (by simp)) fun k hk => by
      have h1 : finRep E a k φ = φ := hk
      change finRep E a k (c • φ) = c • φ
      rw [map_smul, h1]
  kfin := by
    have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  zfin := by
    have := h.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩)
  growth g := by
    obtain ⟨C, N, h1⟩ := h.growth g
    refine ⟨‖c‖ * C, N, fun y => ?_⟩
    change ‖c * φ.1 (g * infGL E a y)‖ ≤ _
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 y) (norm_nonneg c)

def genSub (L : Subgroup (GL (Fin a) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))) : Submodule ℂ (Sm E a) where
  carrier := genSpace L ρ J
  zero_mem' := ⟨isAutForm_const (Submodule.zero_mem _), fun k _ => map_zero _, fun g => by
    have e : (fun k : Kinf E a => (cptRep E a k (0 : Sm E a)).1 g) = 0 := by
      funext k; rw [map_zero]; rfl
    rw [e]; exact Submodule.zero_mem _, fun z _ => map_zero z⟩
  add_mem' := by
    rintro φ ψ ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩
    refine ⟨isAutForm_add h1 h1', fun k hk => by rw [map_add, h2 k hk, h2' k hk], fun g => ?_,
      fun z hz => by rw [map_add, h4 z hz, h4' z hz, add_zero]⟩
    have e : (fun k : Kinf E a => (cptRep E a k (φ + ψ)).1 g) =
        (fun k : Kinf E a => (cptRep E a k φ).1 g) + fun k : Kinf E a => (cptRep E a k ψ).1 g := by
      funext k; rw [map_add]; rfl
    rw [e]; exact Submodule.add_mem _ (h3 g) (h3' g)
  smul_mem' := by
    rintro c φ ⟨h1, h2, h3, h4⟩
    refine ⟨isAutForm_smul c h1, fun k hk => by rw [map_smul, h2 k hk], fun g => ?_,
      fun z hz => by rw [map_smul, h4 z hz, smul_zero]⟩
    have e : (fun k : Kinf E a => (cptRep E a k (c • φ)).1 g) =
        c • fun k : Kinf E a => (cptRep E a k φ).1 g := by
      funext k; rw [map_smul]; rfl
    rw [e]; exact Submodule.smul_mem _ c (h3 g)

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_mapInf :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf)

theorem continuous_mapFin :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pFin)

theorem continuous_of_level {φ : Sm E a} (h : IsOpen {k | finRep E a k φ = φ}) : Continuous φ.1 := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have hc : Continuous fun g : GA E a => g₀⁻¹ * g := continuous_const.mul continuous_id
  let f : GA E a → ℂ := fun g =>
    chart φ.1 g₀ (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val)
  have e1 : ∀ᶠ g in 𝓝 g₀, f g = φ.1 g := by
    have hS : {g : GA E a | GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) ∈ {k | finRep E a k φ = φ}} ∈ 𝓝 g₀ :=
      ((continuous_mapFin.comp hc).continuousAt).preimage_mem_nhds
        (h.mem_nhds (by simp))
    filter_upwards [hS] with g hg
    have hg' : finRep E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) φ = φ := hg
    have e2 := congrFun (congrArg Subtype.val hg') (g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)))
    have e3 : g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) *
        finGL E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) = g := by
      rw [mul_assoc, infGL_mul_finGL, mul_inv_cancel_left]
    change φ.1 (_ * finGL E a _) = _ at e2
    rw [e3] at e2
    simp only [f]
    rw [chart_val, e2]
  refine ContinuousAt.congr ?_ e1
  have hx : toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g₀)).val ∈ invSet E a := val_mem_invSet _
  have h1 : ContinuousAt (chart φ.1 g₀) (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g₀)).val) :=
    (contDiffAt_chart φ.2 g₀ hx).continuousAt
  have h3 : Continuous fun g : GA E a => ((GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) : GL (Fin a) (Cinf E)) :
      Matrix (Fin a) (Fin a) (Cinf E)) := Units.continuous_val.comp (continuous_mapInf.comp hc)
  have h2 : Continuous fun g : GA E a => toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val := h3
  exact ContinuousAt.comp (f := fun g : GA E a => toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) h1 h2.continuousAt

theorem unip_eq_unipGL {R : Type} [CommRing R] {r : ℕ} (x : BlockIx a r → R) :
    unip x = AutomorphicForm.unipGL x := Units.ext rfl

theorem pi_eq_borel (r : ℕ) :
    (MeasurableSpace.pi : MeasurableSpace (BlockIx a r → Ad E)) = borel (BlockIx a r → Ad E) :=
  BorelSpace.measurable_eq

theorem isCuspidal_of_constantTerm {φ : GA E a → ℂ} (hl : ∀ γ g, φ (ratGL E a γ * g) = φ g)
    (h0 : ∀ r : ℕ, 0 < r → r < a → ∀ g, ∫ x in AutomorphicForm.unipFundamentalDomain E a r, φ (unip x * g)
      ∂AutomorphicForm.unipMeasure E a r = 0) : IsCuspidal φ := by
  intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
  obtain rfl : inst1 = MeasurableSpace.pi := inst2.measurable_eq.trans (pi_eq_borel r).symm
  have : (AutomorphicForm.unipMeasure E a r).IsAddHaarMeasure := inferInstance
  have hc := Measure.isAddLeftInvariant_eq_smul μ (AutomorphicForm.unipMeasure E a r)
  have : Countable (ratN E a r) := AutomorphicForm.countable_unipLattice (K := E) (n := a) (r := r)
  have hF0 : IsAddFundamentalDomain (ratN E a r) (AutomorphicForm.unipFundamentalDomain E a r) μ :=
    IsAddFundamentalDomain.mono AutomorphicForm.isAddFundamentalDomain_unipFundamentalDomain
      (hc ▸ Measure.smul_absolutelyContinuous)
  have hinv : ∀ (ξ : ratN E a r) (x : BlockIx a r → Ad E), φ (unip (ξ +ᵥ x) * g) = φ (unip x * g) := by
    rintro ⟨_, ξ, rfl⟩ x
    change φ (unip ((fun p => algebraMap E (Ad E) (ξ p)) + x) * g) = _
    rw [unip_add, unip_algebraMap, mul_assoc, hl]
  rw [hF.setIntegral_eq hF0 hinv, hc, Measure.restrict_smul, integral_smul_nnreal_measure, h0 r hr hr' g, smul_zero]

theorem integrableOn_unip {φ : GA E a → ℂ} (hφ : Continuous φ) (r : ℕ) (g : GA E a) :
    IntegrableOn (fun x => φ (unip x * g)) (AutomorphicForm.unipFundamentalDomain E a r)
      (AutomorphicForm.unipMeasure E a r) := by
  have e : (fun x : BlockIx a r → Ad E => φ (unip x * g)) = fun X => φ (AutomorphicForm.unipGL X * g) :=
    funext fun x => by rw [unip_eq_unipGL]
  rw [e]
  exact AutomorphicForm.integrableOn_constantTerm hφ g

def ctMap (L : Subgroup (GL (Fin a) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))) (r : ℕ) :
    genSub L ρ J →ₗ[ℂ] (GA E a → ℂ) where
  toFun ψ g := ∫ x in AutomorphicForm.unipFundamentalDomain E a r, ψ.1.1 (unip x * g)
    ∂AutomorphicForm.unipMeasure E a r
  map_add' ψ ψ' := funext fun g =>
    integral_add (integrableOn_unip (continuous_of_level ψ.2.1.level) r g)
      (integrableOn_unip (continuous_of_level ψ'.2.1.level) r g)
  map_smul' c ψ := funext fun g => integral_smul c _

theorem genFin_step (hC : CuspFin E a) (hT : ∀ r, 0 < r → r < a → CTFin E a r) : GenFin E a := by
  intro L hL W _ _ _ ρ hρ J hJ
  let R := {r : ℕ // 0 < r ∧ r < a}
  have : Finite R := Finite.of_injective (fun r : R => (⟨r.1, r.2.2⟩ : Fin a))
    fun x y h => Subtype.ext (congrArg (fun z : Fin a => z.1) h)
  have ct := fun r : R => hT r.1 r.2.1 r.2.2 L hL W ρ hρ J hJ
  choose V hVf hV using ct
  have : ∀ r, FiniteDimensional ℂ (V r) := hVf
  have hm : ∀ (r : R) (ψ : genSub L ρ J), ctMap L ρ J r.1 ψ ∈ V r := fun r ψ =>
    hV r ψ.1 ψ.2 (AutomorphicForm.unipMeasure E a r.1) (AutomorphicForm.unipFundamentalDomain E a r.1)
      inferInstance AutomorphicForm.isAddFundamentalDomain_unipFundamentalDomain
  let Φ : genSub L ρ J →ₗ[ℂ] (∀ r : R, V r) :=
    LinearMap.pi fun r => (ctMap L ρ J r.1).codRestrict (V r) (hm r)
  have hker : FiniteDimensional ℂ (LinearMap.ker Φ) := by
    have hC' := hC L hL W ρ hρ J hJ
    have hle : (LinearMap.ker Φ).map (genSub L ρ J).subtype ≤
        Submodule.span ℂ {φ | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1} := by
      rintro _ ⟨ψ, hψ, rfl⟩
      refine Submodule.subset_span ⟨ψ.2, isCuspidal_of_constantTerm ψ.2.1.left fun r h0 h1 g => ?_⟩
      exact congrFun (congrArg Subtype.val (congrFun (LinearMap.mem_ker.1 hψ) ⟨r, h0, h1⟩)) g
    have : FiniteDimensional ℂ ((LinearMap.ker Φ).map (genSub L ρ J).subtype) :=
      Submodule.finiteDimensional_of_le hle
    exact Module.Finite.equiv
      (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) (LinearMap.ker Φ)).symm
  have hfin : FiniteDimensional ℂ (genSub L ρ J) := by
    have : Module.Finite ℂ (genSub L ρ J ⧸ LinearMap.ker Φ) := Module.Finite.equiv Φ.quotKerEquivRange.symm
    exact Module.Finite.of_submodule_quotient (LinearMap.ker Φ)
  rw [show Submodule.span ℂ (genSpace L ρ J) = genSub L ρ J from Submodule.span_eq (genSub L ρ J)]
  exact hfin

theorem genFin_of_chapters :
    (∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), CuspFin E a) →
    (∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ b < a, GenFin E b) →
      ∀ r, 0 < r → r < a → CTFin E a r) →
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), GenFin E a := by
  intro hC hT E _ _ _ a
  induction a using Nat.strong_induction_on with
  | _ a ih => exact genFin_step (hC E a) (hT E a ih)

end GlobalTheory.CompanionTheory.AffglAssembly

end

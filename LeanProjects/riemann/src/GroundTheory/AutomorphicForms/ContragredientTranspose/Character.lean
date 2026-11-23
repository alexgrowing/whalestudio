import Mathlib
import GroundTheory.AutomorphicForms.HeckeIrreducible
import GroundTheory.AutomorphicForms.WhittakerCriterion
import GroundTheory.AutomorphicForms.SmoothRepContragredient
import GroundTheory.AutomorphicForms.SmoothRepSchur

noncomputable section

namespace GroundTheory.Automorphic

namespace ContragredientTranspose

open Set Filter Topology MeasureTheory Module Whittaker

section FinTrace

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def finTrace (T : V →ₗ[ℂ] V) : ℂ :=
  LinearMap.trace ℂ (LinearMap.range T) (T.restrict fun x _ => LinearMap.mem_range_self T x)

theorem finTrace_eq_trace (T : V →ₗ[ℂ] V) (E : Submodule ℂ V) [FiniteDimensional ℂ E]
    (hE : LinearMap.range T ≤ E) :
    LinearMap.trace ℂ E (T.restrict fun x _ => hE (LinearMap.mem_range_self T x)) =
      finTrace T := by
  have : FiniteDimensional ℂ (LinearMap.range T) := Submodule.finiteDimensional_of_le hE
  let A : E →ₗ[ℂ] LinearMap.range T :=
    (T ∘ₗ E.subtype).codRestrict _ fun x => LinearMap.mem_range_self T x
  let B : LinearMap.range T →ₗ[ℂ] E := Submodule.inclusion hE
  have h1 : (T.restrict fun x _ => hE (LinearMap.mem_range_self T x) : E →ₗ[ℂ] E) = B ∘ₗ A :=
    LinearMap.ext fun x => Subtype.ext rfl
  have h2 : (T.restrict fun x _ => LinearMap.mem_range_self T x :
      LinearMap.range T →ₗ[ℂ] LinearMap.range T) = A ∘ₗ B :=
    LinearMap.ext fun x => Subtype.ext rfl
  rw [finTrace, h1, h2, LinearMap.trace_comp_comm']

theorem finTrace_add (S T : V →ₗ[ℂ] V) [FiniteDimensional ℂ (LinearMap.range S)]
    [FiniteDimensional ℂ (LinearMap.range T)] :
    finTrace (S + T) = finTrace S + finTrace T := by
  set E := LinearMap.range S ⊔ LinearMap.range T
  have hS : LinearMap.range S ≤ E := le_sup_left
  have hT : LinearMap.range T ≤ E := le_sup_right
  have hST : LinearMap.range (S + T) ≤ E := by
    rintro _ ⟨x, rfl⟩
    exact E.add_mem (hS ⟨x, rfl⟩) (hT ⟨x, rfl⟩)
  rw [← finTrace_eq_trace S E hS, ← finTrace_eq_trace T E hT, ← finTrace_eq_trace (S + T) E hST,
    ← map_add]
  congr 1

theorem finTrace_smul (c : ℂ) (T : V →ₗ[ℂ] V) [FiniteDimensional ℂ (LinearMap.range T)] :
    finTrace (c • T) = c * finTrace T := by
  have h : LinearMap.range (c • T) ≤ LinearMap.range T := by
    rintro _ ⟨x, rfl⟩
    exact ⟨c • x, by simp⟩
  rw [← finTrace_eq_trace (c • T) (LinearMap.range T) h, finTrace, ← smul_eq_mul, ← map_smul]
  congr 1

theorem finTrace_conj (e : V ≃ₗ[ℂ] V) (T : V →ₗ[ℂ] V) [FiniteDimensional ℂ (LinearMap.range T)] :
    finTrace (e.conj T) = finTrace T := by
  set R := LinearMap.range T
  have hE : LinearMap.range (e.conj T) ≤ R.map (e : V →ₗ[ℂ] V) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨T (e.symm x), LinearMap.mem_range_self T _, by simp [LinearEquiv.conj_apply]⟩
  rw [← finTrace_eq_trace _ _ hE, finTrace, ← LinearMap.trace_conj' _ (e.submoduleMap R)]
  congr 1

end FinTrace

section Character

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem range_heckeLin_le (hρ : IsSmooth ρ) (f : locallyConstantCompactSupport G ℂ ℂ)
    {K : Subgroup G} (hK : ∀ k ∈ K, ∀ x, (f : G → ℂ) (k * x) = (f : G → ℂ) x) :
    LinearMap.range (heckeLin μ hρ f) ≤ fixedVectors ρ K := by
  rintro _ ⟨v, rfl⟩
  exact heckeAct_mem_fixedVectors f.2 hK (hρ v)

theorem finiteDimensional_range_heckeLin (hρ : IsAdmissible ρ)
    (f : locallyConstantCompactSupport G ℂ ℂ) :
    FiniteDimensional ℂ (LinearMap.range (heckeLin μ hρ.1 f)) := by
  obtain ⟨K, hKc, hK⟩ := exists_forall_mul_left f.2
  have := hρ.2 K hKc K.isOpen
  exact Submodule.finiteDimensional_of_le (range_heckeLin_le μ hρ.1 f (K := K) hK)

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem heckeLin_add (hρ : IsSmooth ρ) (f g : locallyConstantCompactSupport G ℂ ℂ) :
    heckeLin μ hρ (f + g) = heckeLin μ hρ f + heckeLin μ hρ g :=
  LinearMap.ext fun v => heckeAct_add_left f.2 g.2 (hρ v)

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem heckeLin_smul (hρ : IsSmooth ρ) (c : ℂ) (f : locallyConstantCompactSupport G ℂ ℂ) :
    heckeLin μ hρ (c • f) = c • heckeLin μ hρ f :=
  LinearMap.ext fun v => heckeAct_smul_left c f.2 (hρ v)

variable (ρ) in

def distChar (hρ : IsAdmissible ρ) : Module.Dual ℂ (locallyConstantCompactSupport G ℂ ℂ) where
  toFun f := finTrace (heckeLin μ hρ.1 f)
  map_add' f g := by
    have := finiteDimensional_range_heckeLin μ hρ f
    have := finiteDimensional_range_heckeLin μ hρ g
    simp only [heckeLin_add]
    exact finTrace_add _ _
  map_smul' c f := by
    have := finiteDimensional_range_heckeLin μ hρ f
    simp only [heckeLin_smul, RingHom.id_apply, smul_eq_mul]
    exact finTrace_smul c _

theorem distChar_apply (hρ : IsAdmissible ρ) (f : locallyConstantCompactSupport G ℂ ℂ) :
    distChar μ ρ hρ f = finTrace (heckeLin μ hρ.1 f) := rfl

theorem distChar_eq_trace (hρ : IsAdmissible ρ) (f : locallyConstantCompactSupport G ℂ ℂ)
    {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (hK : ∀ k ∈ K, ∀ x, (f : G → ℂ) (k * x) = (f : G → ℂ) x) :
    distChar μ ρ hρ f = LinearMap.trace ℂ (fixedVectors ρ K) ((heckeLin μ hρ.1 f).restrict
      fun x _ => range_heckeLin_le μ hρ.1 f hK (LinearMap.mem_range_self _ x)) := by
  have := hρ.2 K hKc hKo
  rw [distChar_apply, finTrace_eq_trace _ _ (range_heckeLin_le μ hρ.1 f hK)]

variable (ρ) in

def repEquiv (g : G) : V ≃ₗ[ℂ] V where
  toLinearMap := ρ g
  invFun := ρ g⁻¹
  left_inv v := by
    change (ρ g⁻¹ * ρ g) v = v
    rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  right_inv v := by
    change (ρ g * ρ g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem heckeAct_biTranslL [μ.IsMulRightInvariant] (hρ : IsSmooth ρ) (g : G)
    (f : locallyConstantCompactSupport G ℂ ℂ) (v : V) :
    heckeAct μ ρ ((biTranslL g g f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) v =
      ρ g (heckeAct μ ρ f (ρ g⁻¹ v)) := by
  have hf' : (fun x => (f : G → ℂ) (x * g⁻¹⁻¹)) ∈ locallyConstantCompactSupport G ℂ ℂ := by
    simpa using (rtransL g f).2
  rw [heckeAct_apply_act μ f.2 (hρ v) g⁻¹, heckeAct_ltrans g hf' (hρ v)]
  congr 1
  funext x
  simp [ltrans_apply, mul_assoc]

theorem distChar_biTranslL [μ.IsMulRightInvariant] (hρ : IsAdmissible ρ) (g : G)
    (f : locallyConstantCompactSupport G ℂ ℂ) :
    distChar μ ρ hρ (biTranslL g g f) = distChar μ ρ hρ f := by
  have := finiteDimensional_range_heckeLin μ hρ f
  have e : heckeLin μ hρ.1 (biTranslL g g f) = (repEquiv ρ g).conj (heckeLin μ hρ.1 f) :=
    LinearMap.ext fun v => by
      rw [LinearEquiv.conj_apply, heckeLin_apply, heckeAct_biTranslL μ hρ.1 g f v]
      rfl
  rw [distChar_apply, distChar_apply, e, finTrace_conj]

end Character

section Contragredient

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem heckeAct_contragredient_apply [μ.IsInvInvariant] (hρ : IsSmooth ρ)
    (f : locallyConstantCompactSupport G ℂ ℂ) (ξ : smoothVectors (Representation.dual ρ)) (v : V) :
    ((heckeAct μ (contragredient ρ) (f : G → ℂ) ξ : smoothVectors (Representation.dual ρ)) :
      Module.Dual ℂ V) v =
      (ξ : Module.Dual ℂ V) (heckeAct μ ρ
        ((compHomeoL (Homeomorph.inv G) f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) v) := by
  have h1 := dual_heckeAct μ f.2 (isSmooth_contragredient ρ ξ) (evalSmooth ρ v)
  have key := integral_inv_eq_self (fun g =>
    ((compHomeoL (Homeomorph.inv G) f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) g *
      (ξ : Module.Dual ℂ V) (ρ g v)) μ
  beta_reduce at key
  rw [evalSmooth_apply] at h1
  rw [h1, dual_heckeAct μ (compHomeoL (Homeomorph.inv G) f).2 (hρ v), ← key]
  congr 1
  funext g
  simp [evalSmooth_apply, contragredient_apply_apply]

theorem distChar_contragredient [μ.IsInvInvariant] (hρ : IsAdmissible ρ)
    (f : locallyConstantCompactSupport G ℂ ℂ) :
    distChar μ (contragredient ρ) (isAdmissible_contragredient hρ) f =
      distChar μ ρ hρ (compHomeoL (Homeomorph.inv G) f) := by
  obtain ⟨K, hKc, hK⟩ := exists_forall_mul_left_mul_right f.2
  have hKl : ∀ k ∈ (K : Subgroup G), ∀ x, (f : G → ℂ) (k * x) = (f : G → ℂ) x :=
    fun k hk x => by simpa using hK k hk x 1 (one_mem _)
  have hKl' : ∀ k ∈ (K : Subgroup G), ∀ x,
      ((compHomeoL (Homeomorph.inv G) f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) (k * x) =
        ((compHomeoL (Homeomorph.inv G) f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) x := by
    intro k hk x
    have := hK 1 (one_mem _) x⁻¹ k⁻¹ (inv_mem hk)
    simpa [mul_inv_rev] using this
  rw [distChar_eq_trace μ (isAdmissible_contragredient hρ) f hKc K.isOpen hKl,
    distChar_eq_trace μ hρ _ hKc K.isOpen hKl']
  have := hρ.2 K hKc K.isOpen
  have := (isAdmissible_contragredient hρ).2 K hKc K.isOpen
  set e := fixedContragredientEquiv hρ.1 hKc K.isOpen
  refine (LinearMap.trace_conj' (R := ℂ) (M := fixedVectors (contragredient ρ) K)
    (N := Module.Dual ℂ (fixedVectors ρ K)) _ e).symm.trans ?_
  rw [← LinearMap.trace_transpose' (R := ℂ) (M := fixedVectors ρ K)]
  congr 1
  refine LinearMap.ext fun l => LinearMap.ext fun v => ?_
  have hw : heckeAct μ ρ ((compHomeoL (Homeomorph.inv G) f : locallyConstantCompactSupport G ℂ ℂ) :
      G → ℂ) (v : V) ∈ fixedVectors ρ K :=
    range_heckeLin_le μ hρ.1 _ hKl' (LinearMap.mem_range_self _ (v : V))
  have key := congrArg (fun L : Module.Dual ℂ (fixedVectors ρ K) => L ⟨_, hw⟩) (e.apply_symm_apply l)
  rw [LinearEquiv.conj_apply_apply]
  change ((heckeAct μ (contragredient ρ) (f : G → ℂ)
    ((e.symm l : fixedVectors (contragredient ρ) K) : smoothVectors (Representation.dual ρ)) :
      smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) (v : V) = l ⟨_, hw⟩
  rw [heckeAct_contragredient_apply μ hρ.1]
  exact key

def mulEquivHomeo (α : G ≃* G) (hα : Continuous α) (hα' : Continuous α.symm) : G ≃ₜ G where
  toEquiv := α.toEquiv
  continuous_toFun := hα
  continuous_invFun := hα'

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] in

@[simp]
theorem mulEquivHomeo_apply (α : G ≃* G) (hα : Continuous α) (hα' : Continuous α.symm) (x : G) :
    mulEquivHomeo α hα hα' x = α x := rfl

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] in

@[simp]
theorem mulEquivHomeo_symm_apply (α : G ≃* G) (hα : Continuous α) (hα' : Continuous α.symm)
    (x : G) : (mulEquivHomeo α hα hα').symm x = α.symm x := rfl

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] in

theorem isAdmissible_comp (α : G ≃* G) (hα : Continuous α) (hα' : Continuous α.symm)
    (hρ : IsAdmissible ρ) : IsAdmissible (ρ.comp α.toMonoidHom) := by
  refine ⟨fun v => (hρ.1 v).preimage hα, fun K hKc hKo => ?_⟩
  have e : fixedVectors (ρ.comp α.toMonoidHom) K = fixedVectors ρ (K.map α.toMonoidHom) := by
    ext v
    simp only [mem_fixedVectors, Subgroup.mem_map]
    constructor
    · rintro h _ ⟨k, hk, rfl⟩
      exact h k hk
    · intro h k hk
      exact h _ ⟨k, hk, rfl⟩
  rw [e]
  refine hρ.2 _ ?_ ?_
  · rw [Subgroup.coe_map]
    exact hKc.image hα
  · rw [Subgroup.coe_map]
    exact (mulEquivHomeo α hα hα').isOpenMap _ hKo

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem heckeAct_comp (α : G ≃* G) (hα : Continuous α) (hα' : Continuous α.symm)
    (hμ : μ.map α = μ) (f : locallyConstantCompactSupport G ℂ ℂ) {v : V}
    (hv : v ∈ smoothVectors ρ) (hv' : v ∈ smoothVectors (ρ.comp α.toMonoidHom)) :
    heckeAct μ (ρ.comp α.toMonoidHom) (f : G → ℂ) v =
      heckeAct μ ρ ((compHomeoL (mulEquivHomeo α hα hα').symm f :
        locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) v := by
  refine eq_of_forall_dual fun φ => ?_
  rw [dual_heckeAct μ f.2 hv', dual_heckeAct μ (compHomeoL _ f).2 hv]
  have hmp : MeasurePreserving (mulEquivHomeo α hα hα').toMeasurableEquiv μ μ :=
    ⟨hα.measurable, hμ⟩
  have key := hmp.integral_comp' (fun g =>
    ((compHomeoL (mulEquivHomeo α hα hα').symm f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) g *
      φ (ρ g v))
  beta_reduce at key
  rw [← key]
  congr 1
  funext g
  simp

theorem distChar_comp (α : G ≃* G) (hα : Continuous α) (hα' : Continuous α.symm)
    (hμ : μ.map α = μ) (hρ : IsAdmissible ρ) (f : locallyConstantCompactSupport G ℂ ℂ) :
    distChar μ (ρ.comp α.toMonoidHom) (isAdmissible_comp α hα hα' hρ) f =
      distChar μ ρ hρ (compHomeoL (mulEquivHomeo α hα hα').symm f) := by
  rw [distChar_apply, distChar_apply]
  congr 1
  exact LinearMap.ext fun v =>
    heckeAct_comp μ α hα hα' hμ f (hρ.1 v) ((isAdmissible_comp α hα hα' hρ).1 v)

end Contragredient

section Independence

open HeckeAlgebra

theorem isSemisimpleModule_prod {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [IsSemisimpleModule R M] [IsSemisimpleModule R N] :
    IsSemisimpleModule R (M × N) := by
  have h1 : IsSemisimpleModule R (LinearMap.range (LinearMap.inl R M N)) :=
    IsSemisimpleModule.range _
  have h2 : IsSemisimpleModule R (LinearMap.range (LinearMap.inr R M N)) :=
    IsSemisimpleModule.range _
  have h := IsSemisimpleModule.sup h1 h2
  rw [LinearMap.sup_range_inl_inr] at h
  exact IsSemisimpleModule.congr (Submodule.topEquiv (R := R) (M := M × N)).symm

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

variable (ρ : Representation ℂ G V) in

def levelLin (h : HeckeAlgebraLevel μ K hKc hKo) : fixedVectors ρ K →ₗ[ℂ] fixedVectors ρ K where
  toFun v := h • v
  map_add' v w := smul_add h v w
  map_smul' c v := Subtype.ext (by
    simp only [RingHom.id_apply, HeckeAlgebraLevel.coe_smul_fixedVectors, Submodule.coe_smul]
    exact heckeAct_smul_right (h : HeckeAlgebra μ).mem c (smooth_of_mem_fixedVectors hKo v.2))

theorem levelLin_apply {ρ : Representation ℂ G V} (h : HeckeAlgebraLevel μ K hKc hKo)
    (v : fixedVectors ρ K) : levelLin hKc hKo ρ h v = h • v := rfl

theorem levelLin_one (ρ : Representation ℂ G V) :
    levelLin hKc hKo ρ (1 : HeckeAlgebraLevel μ K hKc hKo) = LinearMap.id :=
  LinearMap.ext fun v => one_smul _ v

theorem distChar_level {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
    (h : HeckeAlgebraLevel μ K hKc hKo) :
    distChar μ ρ hρ (h : HeckeAlgebra μ) = LinearMap.trace ℂ (fixedVectors ρ K) (levelLin hKc hKo ρ h) := by
  rw [distChar_eq_trace μ hρ (h : HeckeAlgebra μ) hKc hKo
    (fun k hk x => HeckeAlgebraLevel.apply_mul_left hKc hKo h hk x)]
  rfl

theorem nonempty_equiv_of_distChar_eq {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hρ : IsAdmissible ρ)
    (hσ : IsAdmissible σ) [ρ.IsIrreducible] [σ.IsIrreducible]
    (h : distChar μ ρ hρ = distChar μ σ hσ) : Nonempty (ρ.Equiv σ) := by
  classical
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := ρ)
  obtain ⟨K, hKc, hKo, hvK⟩ := (isSmooth_iff_forall_exists ρ).1 hρ.1 v
  have hVK : fixedVectors ρ K ≠ ⊥ := fun hb => hv (by
    have : v ∈ (⊥ : Submodule ℂ V) := hb ▸ hvK
    simpa using this)
  have := hρ.2 K hKc hKo
  have := hσ.2 K hKc hKo
  set H := HeckeAlgebraLevel μ K hKc hKo
  have htr : ∀ r : H, LinearMap.trace ℂ (fixedVectors ρ K) (levelLin hKc hKo ρ r) =
      LinearMap.trace ℂ (fixedVectors σ K) (levelLin hKc hKo σ r) := fun r => by
    rw [← distChar_level hKc hKo hρ r, ← distChar_level hKc hKo hσ r, h]
  have hdim : Module.finrank ℂ (fixedVectors ρ K) = Module.finrank ℂ (fixedVectors σ K) := by
    have := htr 1
    rw [levelLin_one, levelLin_one, LinearMap.trace_id, LinearMap.trace_id] at this
    exact_mod_cast this
  have hpos : 0 < Module.finrank ℂ (fixedVectors ρ K) :=
    Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 hVK)
  have hWK : fixedVectors σ K ≠ ⊥ := by
    rw [← Submodule.nontrivial_iff_ne_bot, ← Module.finrank_pos_iff (R := ℂ), ← hdim]
    exact hpos
  have := isSimpleModule_fixedVectors (μ := μ) hKc hKo hρ.1 hVK
  have := isSimpleModule_fixedVectors (μ := μ) hKc hKo hσ.1 hWK
  by_contra hne
  have hiso : ¬ Nonempty (fixedVectors ρ K ≃ₗ[H] fixedVectors σ K) := fun ⟨e⟩ =>
    hne (nonempty_equiv_of_fixedVectors_equiv hKc hKo hρ.1 hσ.1 hVK e)
  have h12 : ∀ φ : fixedVectors ρ K →ₗ[H] fixedVectors σ K, φ = 0 := fun φ =>
    (LinearMap.bijective_or_eq_zero φ).resolve_left fun hb => hiso ⟨LinearEquiv.ofBijective φ hb⟩
  have h21 : ∀ φ : fixedVectors σ K →ₗ[H] fixedVectors ρ K, φ = 0 := fun φ =>
    (LinearMap.bijective_or_eq_zero φ).resolve_left fun hb =>
      hiso ⟨(LinearEquiv.ofBijective φ hb).symm⟩
  have : IsSemisimpleModule H (fixedVectors ρ K × fixedVectors σ K) := isSemisimpleModule_prod

  let fE : Module.End (Module.End H (fixedVectors ρ K × fixedVectors σ K))
      (fixedVectors ρ K × fixedVectors σ K) :=
    { toFun := fun m => (m.1, 0)
      map_add' := fun m m' => by simp
      map_smul' := fun φ m => by
        rw [Module.End.smul_def, RingHom.id_apply, Module.End.smul_def]
        have hC : (φ (m.1, 0)).2 = 0 := by
          have := h12 (LinearMap.snd H _ _ ∘ₗ φ ∘ₗ LinearMap.inl H _ _)
          exact LinearMap.congr_fun this m.1
        have hB : (φ (0, m.2)).1 = 0 := by
          have := h21 (LinearMap.fst H _ _ ∘ₗ φ ∘ₗ LinearMap.inr H _ _)
          exact LinearMap.congr_fun this m.2
        have hm : m = (m.1, 0) + (0, m.2) := by simp
        refine Prod.ext ?_ hC.symm
        conv_lhs => rw [hm]
        rw [map_add, Prod.fst_add, hB, add_zero] }
  let b := Module.finBasis ℂ (fixedVectors ρ K × fixedVectors σ K)
  obtain ⟨r, hr⟩ := jacobson_density fE (Finset.univ.image b)

  let Lr : (fixedVectors ρ K × fixedVectors σ K) →ₗ[ℂ] (fixedVectors ρ K × fixedVectors σ K) :=
    (levelLin hKc hKo ρ r).prodMap (levelLin hKc hKo σ r)
  have hL : Lr = (LinearMap.inl ℂ _ _) ∘ₗ (LinearMap.fst ℂ _ _) := by
    refine b.ext fun i => ?_
    have := hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    exact this.symm
  have h1 : levelLin hKc hKo ρ r = LinearMap.id := LinearMap.ext fun x => by
    have := LinearMap.congr_fun hL (x, 0)
    exact congrArg Prod.fst this
  have h2 : levelLin hKc hKo σ r = 0 := LinearMap.ext fun y => by
    have := LinearMap.congr_fun hL (0, y)
    exact congrArg Prod.snd this
  have := htr r
  rw [h1, h2, LinearMap.trace_id, map_zero, Nat.cast_eq_zero] at this
  omega

end Independence

end ContragredientTranspose

end GroundTheory.Automorphic

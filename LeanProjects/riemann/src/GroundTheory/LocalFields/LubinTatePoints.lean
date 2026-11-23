import Mathlib
import GroundTheory.LocalFields.Interface
import GroundTheory.LocalFields.ExamplesLaurent
import GroundTheory.LocalFields.SeparableClosure
import GroundTheory.LocalFields.FormalGroups.LubinTateGroup

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MvPowerSeries Topology Filter

section Term

variable {K : Type*} [Field K] [ValuativeRel K] {σ M M' : Type*} [CommRing M] [Algebra K M]
  [CommRing M'] [Algebra K M']

def psTerm (f : MvPowerSeries σ 𝒪[K]) (x : σ → M) (d : σ →₀ ℕ) : M :=
  algebraMap K M ((coeff d f : 𝒪[K]) : K) * d.prod fun i k => x i ^ k

def psEval [TopologicalSpace M] (f : MvPowerSeries σ 𝒪[K]) (x : σ → M) : M :=
  ∑' d, psTerm f x d

theorem map_psTerm (ρ : M →ₐ[K] M') (f : MvPowerSeries σ 𝒪[K]) (x : σ → M) (d : σ →₀ ℕ) :
    ρ (psTerm f x d) = psTerm f (fun i => ρ (x i)) d := by
  simp only [psTerm, map_mul, AlgHom.commutes, Finsupp.prod, map_prod, map_pow]

theorem map_psEval [TopologicalSpace M] [TopologicalSpace M'] [T2Space M'] (ρ : M →ₐ[K] M')
    (hρ : Continuous ρ) {f : MvPowerSeries σ 𝒪[K]} {x : σ → M}
    (h : HasSum (psTerm f x) (psEval f x)) :
    ρ (psEval f x) = psEval f fun i => ρ (x i) := by
  have h' := h.map ρ.toRingHom.toAddMonoidHom hρ
  refine (HasSum.tsum_eq ?_).symm
  convert h' using 1
  · funext d
    exact (map_psTerm ρ f x d).symm
  · rfl

end Term

section Local

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

theorem mem_maximalIdeal_integer_iff {x : 𝒪[L]} : x ∈ 𝓂[L] ↔ valuation L (x : L) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

variable (L) in

theorem isClosed_maximalIdeal_integer : IsClosed ((𝓂[L] : Ideal 𝒪[L]) : Set 𝒪[L]) := by
  have hopen : IsOpen ((𝓂[L] : Ideal 𝒪[L]) : Set 𝒪[L]) := by
    refine (𝓂[L]).toAddSubgroup.isOpen_of_mem_nhds (g := 0) ?_
    refine (EqualChar.hasBasis_nhds_zero_integer L).mem_iff.mpr ⟨1, trivial, fun x hx => ?_⟩
    rw [SetLike.mem_coe, EqualChar.mem_ballIdeal] at hx
    exact mem_maximalIdeal_integer_iff.mpr hx
  exact AddSubgroup.isClosed_of_isOpen (𝓂[L]).toAddSubgroup hopen

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] in
theorem coe_psTerm_integer {σ : Type*} (f : MvPowerSeries σ 𝒪[K]) (a : σ → 𝒪[L]) (d : σ →₀ ℕ) :
    ((algebraMap 𝒪[K] 𝒪[L] (coeff d f) * d.prod fun s e => a s ^ e : 𝒪[L]) : L) =
      psTerm f (fun i => (a i : L)) d := by
  simp [psTerm, Finsupp.prod]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra K L] [ValuativeExtension K L] in

theorem hasEval_of_mem_maximalIdeal {σ : Type*} [Finite σ] {a : σ → 𝒪[L]} (ha : ∀ i, a i ∈ 𝓂[L]) :
    HasEval a := by
  refine ⟨fun i => ?_, ?_⟩
  · refine (EqualChar.hasBasis_nhds_zero_integer L).tendsto_right_iff.mpr fun γ _ => ?_
    obtain ⟨N, hN⟩ := exists_pow_lt₀ (mem_maximalIdeal_integer_iff.mp (ha i)) γ
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [SetLike.mem_coe, EqualChar.mem_ballIdeal, SubmonoidClass.coe_pow, map_pow]
    exact lt_of_le_of_lt (pow_le_pow_of_le_one zero_le
      (mem_maximalIdeal_integer_iff.mp (ha i)).le hn) hN
  · rw [Filter.cofinite_eq_bot]
    exact tendsto_bot

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem hasSum_psTerm_eval₂ {σ : Type*} [Finite σ] (f : MvPowerSeries σ 𝒪[K]) (a : σ → 𝒪[L])
    (ha : ∀ i, a i ∈ 𝓂[L]) :
    letI : UniformSpace 𝒪[K] := ⊥
    letI : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
    HasSum (psTerm f fun i => (a i : L))
      ((MvPowerSeries.eval₂ (algebraMap 𝒪[K] 𝒪[L]) a f : 𝒪[L]) : L) := by
  let _ : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  have _ : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  let _ : UniformSpace 𝒪[K] := ⊥
  have _ : DiscreteUniformity 𝒪[K] := ⟨rfl⟩
  have hφ : Continuous[(⊥ : UniformSpace 𝒪[K]).toTopologicalSpace, _]
      (algebraMap 𝒪[K] 𝒪[L]) := by
    rw [UniformSpace.toTopologicalSpace_bot]
    exact continuous_bot
  have hs := hasSum_eval₂ hφ (hasEval_of_mem_maximalIdeal ha) f
  have h2 : HasSum (fun d => ((algebraMap 𝒪[K] 𝒪[L] (coeff d f) *
      d.prod fun s e => a s ^ e : 𝒪[L]) : L))
      ((MvPowerSeries.eval₂ (algebraMap 𝒪[K] 𝒪[L]) a f : 𝒪[L]) : L) :=
    hs.map (AddSubmonoidClass.subtype 𝒪[L]) continuous_subtype_val
  simpa only [coe_psTerm_integer] using h2

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem hasSum_psEval {σ : Type*} [Finite σ] (f : MvPowerSeries σ 𝒪[K]) (a : σ → 𝒪[L])
    (ha : ∀ i, a i ∈ 𝓂[L]) :
    HasSum (psTerm f fun i => (a i : L)) (psEval f fun i => (a i : L)) :=
  (hasSum_psTerm_eval₂ f a ha).summable.hasSum

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem psEval_eq_eval₂ {σ : Type*} [Finite σ] (f : MvPowerSeries σ 𝒪[K]) (a : σ → 𝒪[L])
    (ha : ∀ i, a i ∈ 𝓂[L]) :
    letI : UniformSpace 𝒪[K] := ⊥
    letI : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
    psEval f (fun i => (a i : L)) =
      ((MvPowerSeries.eval₂ (algebraMap 𝒪[K] 𝒪[L]) a f : 𝒪[L]) : L) :=
  have := t2Space_of_isNonarchimedeanLocalField L
  (hasSum_psTerm_eval₂ f a ha).tsum_eq

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem psEval_mem_integer {σ : Type*} [Finite σ] (f : MvPowerSeries σ 𝒪[K]) (a : σ → 𝒪[L])
    (ha : ∀ i, a i ∈ 𝓂[L]) :
    psEval f (fun i => (a i : L)) ∈ 𝒪[L] := by
  rw [psEval_eq_eval₂ f a ha]
  exact SetLike.coe_mem _

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem valuation_psEval_lt_one {σ : Type*} [Finite σ] {f : MvPowerSeries σ 𝒪[K]}
    (hf : constantCoeff f = 0) (a : σ → 𝒪[L]) (ha : ∀ i, a i ∈ 𝓂[L]) :
    valuation L (psEval f fun i => (a i : L)) < 1 := by
  let y : 𝒪[L] := ⟨_, psEval_mem_integer f a ha⟩
  change valuation L (y : L) < 1
  refine mem_maximalIdeal_integer_iff.mp ?_
  refine (isClosed_maximalIdeal_integer L).mem_of_tendsto
    (b := (SummationFilter.unconditional (σ →₀ ℕ)).filter)
    (f := fun s : Finset (σ →₀ ℕ) => ∑ d ∈ s, (⟨psTerm f (fun i => (a i : L)) d, ?_⟩ : 𝒪[L]))
    ?_ (Eventually.of_forall fun s => ?_)
  · rw [← coe_psTerm_integer]
    exact SetLike.coe_mem _
  · have h := hasSum_psEval f a ha
    rw [HasSum] at h
    rw [(Topology.IsInducing.subtypeVal).tendsto_nhds_iff]
    convert h using 1
    funext s
    simp
  · refine Ideal.sum_mem _ fun d _ => ?_
    have he : (⟨psTerm f (fun i => (a i : L)) d, by
        rw [← coe_psTerm_integer]; exact SetLike.coe_mem _⟩ : 𝒪[L]) =
        algebraMap 𝒪[K] 𝒪[L] (coeff d f) * d.prod fun s e => a s ^ e :=
      Subtype.ext (coe_psTerm_integer f a d).symm
    rw [he]
    by_cases hd : d = 0
    · subst hd
      simp [hf]
    · obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hd
      refine Ideal.mul_mem_left _ _ ?_
      rw [Finsupp.prod]
      refine Ideal.prod_mem _ (i := i) (Finsupp.mem_support_iff.mpr hi) ?_
      exact Ideal.pow_mem_of_mem _ (ha i) _ (Nat.pos_of_ne_zero hi)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem psEval_subst {σ τ : Type*} [Finite σ] [Finite τ] {g : σ → MvPowerSeries τ 𝒪[K]}
    (hg : ∀ s, constantCoeff (g s) = 0) (f : MvPowerSeries σ 𝒪[K]) (a : τ → 𝒪[L])
    (ha : ∀ i, a i ∈ 𝓂[L]) :
    psEval (subst g f) (fun i => (a i : L)) =
      psEval f (fun s => psEval (g s) fun i => (a i : L)) := by
  let b : σ → 𝒪[L] := fun s => ⟨_, psEval_mem_integer (g s) a ha⟩
  have hb : ∀ s, b s ∈ 𝓂[L] := fun s =>
    mem_maximalIdeal_integer_iff.mpr (valuation_psEval_lt_one (hg s) a ha)
  change _ = psEval f fun s => (b s : L)
  let _ : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  have _ : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  let _ : UniformSpace 𝒪[K] := ⊥
  have _ : DiscreteUniformity 𝒪[K] := ⟨rfl⟩
  rw [psEval_eq_eval₂ f b hb, psEval_eq_eval₂ _ a ha]
  have hsub : HasSubst g := hasSubst_of_constantCoeff_zero hg
  rw [eval₂_subst hsub (hasEval_of_mem_maximalIdeal ha)]
  congr 3
  funext s
  apply Subtype.ext
  exact (psEval_eq_eval₂ (g s) a ha).symm

end Local

section Algebraic

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]

variable (Ω) in

theorem t2Space_of_isValuativeTopology : T2Space Ω := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => ?_
  refine ⟨{z | valuation Ω z < valuation Ω x}, ?_, fun h => lt_irrefl (valuation Ω x) h⟩
  exact (IsValuativeTopology.hasBasis_nhds_zero Ω).mem_of_mem
    (i := Units.mk0 _ ((valuation Ω).ne_zero_iff.mpr hx)) trivial

variable [Algebra K Ω] [ValuativeExtension K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem valuation_coe_lt_one_iff (E : IntermediateField K Ω) (x : E) :
    valuation Ω (x : Ω) < 1 ↔ valuation E x < 1 := by
  rw [← map_one (valuation Ω), ← (valuation Ω).vlt_iff_lt, ← map_one (valuation E),
    ← (valuation E).vlt_iff_lt]
  exact not_congr (by simpa using IntermediateField.coe_vle_coe_iff (1 : E) x)

variable [Algebra.IsAlgebraic K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem finiteDimensional_adjoin_range {σ : Type*} [Finite σ] (x : σ → Ω) :
    FiniteDimensional K (IntermediateField.adjoin K (Set.range x)) :=
  have : Finite (Set.range x) := Set.finite_range x
  IntermediateField.finiteDimensional_adjoin fun y _ => (Algebra.IsAlgebraic.isAlgebraic y).isIntegral

theorem hasSum_psEval_coe (E : IntermediateField K Ω) [FiniteDimensional K E] {σ : Type*}
    [Finite σ] (f : MvPowerSeries σ 𝒪[K]) (x : σ → E) (hx : ∀ i, valuation Ω (x i : Ω) < 1) :
    HasSum (psTerm f fun i => (x i : Ω)) ((psEval f x : E) : Ω) := by
  let a : σ → 𝒪[E] := fun i => ⟨x i, ((valuation_coe_lt_one_iff E (x i)).mp (hx i)).le⟩
  have ha : ∀ i, a i ∈ 𝓂[E] := fun i =>
    mem_maximalIdeal_integer_iff.mpr ((valuation_coe_lt_one_iff E (x i)).mp (hx i))
  have hE : HasSum (psTerm f x) (psEval f x) := hasSum_psEval f a ha
  have h := hE.map E.val.toRingHom.toAddMonoidHom continuous_subtype_val
  convert h using 1
  · funext d
    exact (map_psTerm E.val f x d).symm
  · rfl

theorem psEval_coe (E : IntermediateField K Ω) [FiniteDimensional K E] {σ : Type*} [Finite σ]
    (f : MvPowerSeries σ 𝒪[K]) (x : σ → E) (hx : ∀ i, valuation Ω (x i : Ω) < 1) :
    psEval f (fun i => (x i : Ω)) = ((psEval f x : E) : Ω) :=
  have := t2Space_of_isValuativeTopology Ω
  (hasSum_psEval_coe E f x hx).tsum_eq

theorem hasSum_psEval' {σ : Type*} [Finite σ] (f : MvPowerSeries σ 𝒪[K]) (x : σ → Ω)
    (hx : ∀ i, valuation Ω (x i) < 1) :
    HasSum (psTerm f x) (psEval f x) := by
  let E := IntermediateField.adjoin K (Set.range x)
  have := finiteDimensional_adjoin_range (K := K) x
  let xE : σ → E := fun i => ⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have h := hasSum_psEval_coe E f xE hx
  rwa [← psEval_coe E f xE hx] at h

theorem psEval_mem {σ : Type*} [Finite σ] (f : MvPowerSeries σ 𝒪[K]) (E : IntermediateField K Ω)
    [FiniteDimensional K E] {x : σ → Ω} (hxE : ∀ i, x i ∈ E) (hx : ∀ i, valuation Ω (x i) < 1) :
    psEval f x ∈ E := by
  have h := psEval_coe E f (fun i => ⟨x i, hxE i⟩) hx
  change psEval f x = _ at h
  rw [h]
  exact SetLike.coe_mem _

theorem valuation_psEval_lt_one' {σ : Type*} [Finite σ] {f : MvPowerSeries σ 𝒪[K]}
    (hf : constantCoeff f = 0) (x : σ → Ω) (hx : ∀ i, valuation Ω (x i) < 1) :
    valuation Ω (psEval f x) < 1 := by
  let E := IntermediateField.adjoin K (Set.range x)
  have := finiteDimensional_adjoin_range (K := K) x
  let xE : σ → E := fun i => ⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  let a : σ → 𝒪[E] := fun i => ⟨xE i, ((valuation_coe_lt_one_iff E (xE i)).mp (hx i)).le⟩
  have ha : ∀ i, a i ∈ 𝓂[E] := fun i =>
    mem_maximalIdeal_integer_iff.mpr ((valuation_coe_lt_one_iff E (xE i)).mp (hx i))
  have h := psEval_coe E f xE hx
  change psEval f x = _ at h
  rw [h, valuation_coe_lt_one_iff]
  exact valuation_psEval_lt_one hf a ha

theorem psEval_subst' {σ τ : Type*} [Finite σ] [Finite τ] {g : σ → MvPowerSeries τ 𝒪[K]}
    (hg : ∀ s, constantCoeff (g s) = 0) (f : MvPowerSeries σ 𝒪[K]) (x : τ → Ω)
    (hx : ∀ i, valuation Ω (x i) < 1) :
    psEval (subst g f) x = psEval f fun s => psEval (g s) x := by
  let E := IntermediateField.adjoin K (Set.range x)
  have := finiteDimensional_adjoin_range (K := K) x
  let xE : τ → E := fun i => ⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  let a : τ → 𝒪[E] := fun i => ⟨xE i, ((valuation_coe_lt_one_iff E (xE i)).mp (hx i)).le⟩
  have ha : ∀ i, a i ∈ 𝓂[E] := fun i =>
    mem_maximalIdeal_integer_iff.mpr ((valuation_coe_lt_one_iff E (xE i)).mp (hx i))
  have h1 : psEval (subst g f) x = _ := psEval_coe E (subst g f) xE hx
  have h2 : ∀ s, psEval (g s) x = _ := fun s => psEval_coe E (g s) xE hx
  have hy : ∀ s, valuation Ω ((psEval (g s) xE : E) : Ω) < 1 := fun s => by
    rw [valuation_coe_lt_one_iff]
    exact valuation_psEval_lt_one (hg s) a ha
  have h3 := psEval_coe E f (fun s => psEval (g s) xE) hy
  rw [h1, funext h2, h3, psEval_subst hg f a ha]

theorem algEquiv_psEval (τ : Ω ≃ₐ[K] Ω) {σ : Type*} [Finite σ] (f : MvPowerSeries σ 𝒪[K])
    (x : σ → Ω) (hx : ∀ i, valuation Ω (x i) < 1) :
    τ (psEval f x) = psEval f fun i => τ (x i) :=
  have := t2Space_of_isValuativeTopology Ω
  map_psEval (τ : Ω →ₐ[K] Ω) (continuous_algEquiv_of_isAlgebraic τ) (hasSum_psEval' f x hx)

end Algebraic

section Basic

variable {K : Type*} [Field K] [ValuativeRel K] {σ M : Type*} [CommRing M] [Algebra K M]
  [TopologicalSpace M] [T2Space M]

omit [T2Space M] in

@[simp]
theorem psEval_zero (x : σ → M) : psEval (0 : MvPowerSeries σ 𝒪[K]) x = 0 := by
  simp [psEval, psTerm]

omit [T2Space M] in

@[simp]
theorem psEval_X (x : σ → M) (i : σ) : psEval (X i : MvPowerSeries σ 𝒪[K]) x = x i := by
  classical
  rw [psEval, tsum_eq_single (Finsupp.single i 1)]
  · simp [psTerm, coeff_X]
  · intro d hd
    simp [psTerm, coeff_X, hd]

end Basic

namespace FormalGroup

section Points

variable {K : Type*} [Field K] [ValuativeRel K] {Ω : Type*} [Field Ω] [ValuativeRel Ω]

variable (Ω) in

def IdealPoint (_F : _root_.FormalGroup 𝒪[K]) : Type _ := {x : Ω // valuation Ω x < 1}

variable {F G H : _root_.FormalGroup 𝒪[K]}

namespace IdealPoint

def val (x : IdealPoint Ω F) : Ω := Subtype.val x

theorem valuation_lt_one (x : IdealPoint Ω F) : valuation Ω x.val < 1 := x.2

def mk (x : Ω) (hx : valuation Ω x < 1) : IdealPoint Ω F := ⟨x, hx⟩

@[simp]
theorem val_mk (x : Ω) (hx : valuation Ω x < 1) : (mk x hx : IdealPoint Ω F).val = x := rfl

@[ext]
theorem ext {x y : IdealPoint Ω F} (h : x.val = y.val) : x = y := Subtype.ext h

theorem val_injective : Function.Injective (val : IdealPoint Ω F → Ω) := fun _ _ => ext

end IdealPoint

instance : Zero (IdealPoint Ω F) := ⟨IdealPoint.mk 0 (by simp)⟩

@[simp]
theorem IdealPoint.val_zero : (0 : IdealPoint Ω F).val = 0 := rfl

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in
theorem constantCoeff_point_val {σ : Type*} (p : F.Point σ) : constantCoeff p.val = 0 :=
  IsNilpotent.eq_zero p.prop

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in
theorem constantCoeff_inv_mv : constantCoeff (inv F : MvPowerSeries Unit 𝒪[K]) = 0 :=
  FormalGroup.constantCoeff_inv F

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in
theorem fin_two_valuation_lt_one (x y : IdealPoint Ω F) :
    ∀ i, valuation Ω ((![x.val, y.val] : Fin 2 → Ω) i) < 1 := by
  intro i
  fin_cases i
  exacts [x.valuation_lt_one, y.valuation_lt_one]

instance : Add (IdealPoint Ω F) where
  add x y := IdealPoint.mk (psEval F.toPowerSeries ![x.val, y.val])
    (valuation_psEval_lt_one' F.zero_constantCoeff _ (fin_two_valuation_lt_one x y))

instance : Neg (IdealPoint Ω F) where
  neg x := IdealPoint.mk (psEval (inv F : MvPowerSeries Unit 𝒪[K]) fun _ => x.val)
    (valuation_psEval_lt_one' constantCoeff_inv_mv _ fun _ => x.valuation_lt_one)

theorem IdealPoint.val_add (x y : IdealPoint Ω F) :
    (x + y).val = psEval F.toPowerSeries ![x.val, y.val] := rfl

theorem IdealPoint.val_neg (x : IdealPoint Ω F) :
    (-x).val = psEval (inv F : MvPowerSeries Unit 𝒪[K]) fun _ => x.val := rfl

def evalPoint {σ : Type*} [Finite σ] (x : σ → IdealPoint Ω F) (p : F.Point σ) :
    IdealPoint Ω F :=
  IdealPoint.mk (psEval p.val fun i => (x i).val)
    (valuation_psEval_lt_one' (constantCoeff_point_val p) _ fun i => (x i).valuation_lt_one)

theorem evalPoint_val {σ : Type*} [Finite σ] (x : σ → IdealPoint Ω F) (p : F.Point σ) :
    (evalPoint x p).val = psEval p.val fun i => (x i).val := rfl

def pointVar {σ : Type*} (i : σ) : F.Point σ :=
  ⟨X i, by simp [PowerSeries.HasSubst]⟩

theorem evalPoint_pointVar {σ : Type*} [Finite σ] (x : σ → IdealPoint Ω F) (i : σ) :
    evalPoint x (pointVar i) = x i :=
  IdealPoint.ext (psEval_X _ i)

theorem evalPoint_zero {σ : Type*} [Finite σ] (x : σ → IdealPoint Ω F) :
    evalPoint x (0 : F.Point σ) = 0 :=
  IdealPoint.ext (psEval_zero _)

theorem evalPoint_add {σ : Type*} [Finite σ] (x : σ → IdealPoint Ω F) (p q : F.Point σ) :
    evalPoint x (p + q) = evalPoint x p + evalPoint x q := by
  apply IdealPoint.ext
  rw [evalPoint_val, FormalGroup.add_apply, psEval_subst' _ F.toPowerSeries _
    fun i => (x i).valuation_lt_one]
  · rw [IdealPoint.val_add]
    congr 1
    funext i
    fin_cases i <;> rfl
  · intro i
    fin_cases i
    exacts [constantCoeff_point_val p, constantCoeff_point_val q]

theorem evalPoint_neg {σ : Type*} [Finite σ] (x : σ → IdealPoint Ω F) (p : F.Point σ) :
    evalPoint x (-p) = -evalPoint x p := by
  apply IdealPoint.ext
  rw [evalPoint_val, FormalGroup.neg_point_val, PowerSeries.subst,
    psEval_subst' (fun _ => constantCoeff_point_val p) _ _ fun i => (x i).valuation_lt_one]
  rfl

theorem psEval_apply_val {σ : Type*} [Finite σ] (φ : Hom F G) (p : F.Point σ) (x : σ → Ω)
    (hx : ∀ i, valuation Ω (x i) < 1) :
    psEval (φ.apply p).val x = psEval φ.toPowerSeries fun _ => psEval p.val x := by
  rw [Hom.apply_val, PowerSeries.subst,
    psEval_subst' (fun _ => constantCoeff_point_val p) _ _ hx]

instance instAddGroup : AddGroup (IdealPoint Ω F) where
  add_assoc a b c := by
    have h := congrArg (evalPoint ![a, b, c])
      (add_assoc (pointVar 0 : F.Point (Fin 3)) (pointVar 1) (pointVar 2))
    simpa [evalPoint_add, evalPoint_pointVar] using h
  zero_add a := by
    have h := congrArg (evalPoint fun _ : Unit => a) (zero_add (pointVar () : F.Point Unit))
    simpa only [evalPoint_add, evalPoint_pointVar, evalPoint_zero] using h
  add_zero a := by
    have h := congrArg (evalPoint fun _ : Unit => a) (add_zero (pointVar () : F.Point Unit))
    simpa only [evalPoint_add, evalPoint_pointVar, evalPoint_zero] using h
  neg_add_cancel a := by
    have h := congrArg (evalPoint fun _ : Unit => a) (neg_add_cancel (pointVar () : F.Point Unit))
    simpa only [evalPoint_add, evalPoint_neg, evalPoint_pointVar, evalPoint_zero] using h
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instAddCommGroup [F.IsComm] : AddCommGroup (IdealPoint Ω F) where
  add_comm a b := by
    have h := congrArg (evalPoint ![a, b])
      (add_comm (pointVar 0 : F.Point (Fin 2)) (pointVar 1))
    simpa [evalPoint_add, evalPoint_pointVar] using h

theorem psEval_powerSeries_subst {σ : Type*} [Finite σ] {a : MvPowerSeries σ 𝒪[K]}
    (ha : constantCoeff a = 0) (φ : PowerSeries 𝒪[K]) (x : σ → Ω)
    (hx : ∀ i, valuation Ω (x i) < 1) :
    psEval (PowerSeries.subst a φ) x = psEval φ fun _ => psEval a x := by
  rw [PowerSeries.subst, psEval_subst' (fun _ => ha) _ _ hx]

def Hom.pointMap (φ : Hom F G) : IdealPoint Ω F →+ IdealPoint Ω G :=
  AddMonoidHom.mk' (fun x => IdealPoint.mk (psEval φ.toPowerSeries fun _ => x.val)
      (valuation_psEval_lt_one' φ.constantCoeff_eq_zero' _ fun _ => x.valuation_lt_one))
    fun a b => by
      apply IdealPoint.ext
      simp only [IdealPoint.val_mk, IdealPoint.val_add]
      have hx := fin_two_valuation_lt_one a b
      rw [← psEval_powerSeries_subst F.zero_constantCoeff _ _ hx, φ.map_add,
        psEval_subst' _ _ _ hx]
      · congr 1
        funext i
        fin_cases i
        · simp [psEval_powerSeries_subst (constantCoeff_X 0) _ _ hx]
        · simp [psEval_powerSeries_subst (constantCoeff_X 1) _ _ hx]
      · intro i
        fin_cases i
        · exact PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X _) _
            φ.constantCoeff_eq_zero
        · exact PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X _) _
            φ.constantCoeff_eq_zero

theorem Hom.pointMap_val (φ : Hom F G) (x : IdealPoint Ω F) :
    (φ.pointMap x).val = psEval φ.toPowerSeries fun _ => x.val := rfl

theorem Hom.pointMap_comp (g : Hom G H) (f : Hom F G) (x : IdealPoint Ω F) :
    (g.comp f).pointMap x = g.pointMap (f.pointMap x) := by
  apply IdealPoint.ext
  rw [Hom.pointMap_val, Hom.toPowerSeries_comp,
    psEval_powerSeries_subst f.constantCoeff_eq_zero' _ _ fun _ => x.valuation_lt_one]
  rfl

theorem Hom.pointMap_id (x : IdealPoint Ω F) : (Hom.id F).pointMap x = x := by
  apply IdealPoint.ext
  rw [Hom.pointMap_val, Hom.toPowerSeries_id]
  exact psEval_X _ ()

theorem Hom.pointMap_zero (x : IdealPoint Ω F) : (0 : Hom F G).pointMap x = 0 := by
  apply IdealPoint.ext
  rw [Hom.pointMap_val, Hom.toPowerSeries_zero]
  exact psEval_zero _

theorem Hom.pointMap_add [G.IsComm] (f g : Hom F G) (x : IdealPoint Ω F) :
    (f + g).pointMap x = f.pointMap x + g.pointMap x := by
  apply IdealPoint.ext
  rw [Hom.pointMap_val, Hom.toPowerSeries_add, psEval_subst' _ _ _ fun _ => x.valuation_lt_one]
  · rw [IdealPoint.val_add]
    congr 1
    funext i
    fin_cases i <;> rfl
  · intro i
    fin_cases i
    exacts [f.constantCoeff_eq_zero', g.constantCoeff_eq_zero']

variable (Ω F) in

def endPointMap [F.IsComm] : Hom F F →+* AddMonoid.End (IdealPoint Ω F) where
  toFun φ := φ.pointMap
  map_one' := AddMonoidHom.ext fun x => Hom.pointMap_id x
  map_mul' f g := AddMonoidHom.ext fun x => by
    rw [Hom.mul_def, Hom.pointMap_comp]
    rfl
  map_zero' := AddMonoidHom.ext fun x => Hom.pointMap_zero x
  map_add' f g := AddMonoidHom.ext fun x => Hom.pointMap_add f g x

theorem endPointMap_apply [F.IsComm] (φ : Hom F F) (x : IdealPoint Ω F) :
    endPointMap Ω F φ x = φ.pointMap x := rfl

def Iso.pointEquiv (e : Iso F G) : IdealPoint Ω F ≃+ IdealPoint Ω G where
  toFun := e.hom.pointMap
  invFun := e.inv.pointMap
  left_inv x := by
    rw [← Hom.pointMap_comp, e.inv_comp_hom, Hom.pointMap_id]
  right_inv x := by
    rw [← Hom.pointMap_comp, e.hom_comp_inv, Hom.pointMap_id]
  map_add' := map_add _

def galPointMap (τ : Ω ≃ₐ[K] Ω) : IdealPoint Ω F →+ IdealPoint Ω F :=
  AddMonoidHom.mk' (fun x => IdealPoint.mk (τ x.val)
      (by rw [valuation_algEquiv_apply_of_isAlgebraic]; exact x.valuation_lt_one))
    fun a b => by
      apply IdealPoint.ext
      simp only [IdealPoint.val_mk, IdealPoint.val_add]
      rw [algEquiv_psEval τ _ _ (fin_two_valuation_lt_one a b)]
      congr 1
      funext i
      fin_cases i <;> rfl

theorem galPointMap_val (τ : Ω ≃ₐ[K] Ω) (x : IdealPoint Ω F) :
    (galPointMap τ x).val = τ x.val := rfl

theorem galPointMap_pointMap (τ : Ω ≃ₐ[K] Ω) (φ : Hom F G) (x : IdealPoint Ω F) :
    galPointMap τ (φ.pointMap x) = φ.pointMap (galPointMap τ x) := by
  apply IdealPoint.ext
  rw [galPointMap_val, Hom.pointMap_val, algEquiv_psEval τ _ _ fun _ => x.valuation_lt_one]
  rfl

end Points

section LubinTate

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} {hπ : Irreducible π} {f g : PowerSeries 𝒪[K]}

noncomputable instance instModuleLubinTate {hf : IsLubinTateSeries π f} :
    Module 𝒪[K] (IdealPoint Ω (lubinTateFormalGroup hπ hf)) :=
  Module.compHom _ ((endPointMap Ω _).comp (lubinTateEndRingHom hπ hf))

theorem lubinTate_smul_eq (hf : IsLubinTateSeries π f) (a : 𝒪[K])
    (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) :
    a • x = (lubinTateHom hπ hf hf a).pointMap x := rfl

theorem lubinTate_smul_val (hf : IsLubinTateSeries π f) (a : 𝒪[K])
    (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) :
    (a • x).val = psEval (lubinTateHom hπ hf hf a).toPowerSeries fun _ => x.val := rfl

theorem lubinTate_uniformizer_smul_val (hf : IsLubinTateSeries π f)
    (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) :
    (π • x).val = psEval f fun _ => x.val := by
  rw [lubinTate_smul_val, lubinTateHom_self_uniformizer]

noncomputable def lubinTatePointEquiv (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g) :
    IdealPoint Ω (lubinTateFormalGroup hπ hg) ≃ₗ[𝒪[K]] IdealPoint Ω (lubinTateFormalGroup hπ hf) :=
  { (lubinTateIso hπ hf hg 1).pointEquiv with
    map_smul' a x := by
      change (lubinTateHom hπ hf hg 1).pointMap ((lubinTateHom hπ hg hg a).pointMap x) =
        (lubinTateHom hπ hf hf a).pointMap ((lubinTateHom hπ hf hg 1).pointMap x)
      rw [← Hom.pointMap_comp, ← Hom.pointMap_comp, ← lubinTateHom_mul hπ hf hg hg,
        ← lubinTateHom_mul hπ hf hf hg, one_mul, mul_one] }

theorem lubinTatePointEquiv_val (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g)
    (x : IdealPoint Ω (lubinTateFormalGroup hπ hg)) :
    (lubinTatePointEquiv hf hg x).val =
      psEval (lubinTateHom hπ hf hg 1).toPowerSeries fun _ => x.val := rfl

noncomputable def lubinTateGalPointMap (hf : IsLubinTateSeries π f) (τ : Ω ≃ₐ[K] Ω) :
    IdealPoint Ω (lubinTateFormalGroup hπ hf) →ₗ[𝒪[K]] IdealPoint Ω (lubinTateFormalGroup hπ hf) :=
  { galPointMap τ with
    map_smul' a x := galPointMap_pointMap τ (lubinTateHom hπ hf hf a) x }

theorem lubinTateGalPointMap_val (hf : IsLubinTateSeries π f) (τ : Ω ≃ₐ[K] Ω)
    (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) :
    (lubinTateGalPointMap hf τ x).val = τ x.val := rfl

variable (Ω) in

noncomputable def lubinTateTorsion (hf : IsLubinTateSeries π f) (n : ℕ) :
    Submodule 𝒪[K] (IdealPoint Ω (lubinTateFormalGroup hπ hf)) :=
  Submodule.torsionBy 𝒪[K] _ (π ^ n)

theorem mem_lubinTateTorsion (hf : IsLubinTateSeries π f) (n : ℕ)
    (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) :
    x ∈ lubinTateTorsion Ω hf n ↔ π ^ n • x = 0 :=
  Submodule.mem_torsionBy_iff _ _

end LubinTate

end FormalGroup

end GroundTheory.LocalField

import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.ProjVar GlobalTheory.ProjSpace Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.CutModel

theorem valAt_algebraMap {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)
    (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h, IsFractionRing.injective _ Z.functionField h.choose_spec]

theorem valAt_eq_zero_iff {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)
    {f : Z.functionField} (h : RegAt (below y) f) : valAt y f = 0 ↔ ¬ UnitAt (below y) f := by
  obtain ⟨a, rfl⟩ := h
  have := Scheme.isLocalHom_stalkClosedPointTo' (R := K) y
  rw [valAt_algebraMap, ← not_iff_not, not_not, ← ne_eq, ← isUnit_iff_ne_zero, isUnit_map_iff]
  refine ⟨fun h => ⟨a, h, rfl⟩, fun ⟨b, hb, e⟩ => ?_⟩
  exact IsFractionRing.injective _ Z.functionField e ▸ hb

theorem valAt_mul {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)
    {f g : Z.functionField} (h : RegAt (below y) f) (h' : RegAt (below y) g) :
    valAt y (f * g) = valAt y f * valAt y g := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨b, rfl⟩ := h'
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

variable {F : Type} [Field F] [NumberField F] (Y : Var F) (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (w : Fin n → Y.Fn) (c : Fin Y.dim → Fin n → 𝓞 E)

omit [NumberField F] in

theorem genAt_iff {Δ : Y.Dv} (h : Y.bpf Δ (Set.range w)) (x : Y.X) (k : Fin n) :
    GenAt Y w x k ↔ Δ.GeneratesAt x (w k) := by
  obtain ⟨_, ⟨j, rfl⟩, g, hg, hj⟩ := h.2 x
  have hr (l) : RegAt x (w l * g) := hg.regularAt_iff.1 (mem_sections.1 (h.mem _ ⟨l, rfl⟩) x)
  rw [hg.generatesAt_iff]
  constructor
  · rintro ⟨h0, hk⟩
    obtain ⟨a, ha⟩ := hk j
    obtain ⟨b, hb⟩ := hr k
    obtain ⟨u, hu, e⟩ := hj
    refine ⟨b, isUnit_of_mul_isUnit_right (x := a) ?_, hb⟩
    have : a * b = u := IsFractionRing.injective _ Y.Fn (by
      rw [map_mul, ha, hb, e, ← mul_assoc, div_mul_cancel₀ _ h0])
    rw [this]; exact hu
  · intro hk
    have h0 : w k ≠ 0 := left_ne_zero_of_mul hk.ne_zero
    refine ⟨h0, fun l => ?_⟩
    have := (hr l).mul hk.inv.regAt
    have hg0 : (g : Y.Fn) ≠ 0 := g.ne_zero
    rwa [← div_eq_mul_inv, mul_div_mul_right _ _ hg0] at this

omit [NumberField F] in
theorem exists_genAt {Δ : Y.Dv} (h : Y.bpf Δ (Set.range w)) (x : Y.X) : ∃ k, GenAt Y w x k := by
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := h.2 x
  exact ⟨j, (genAt_iff Y w h x j).2 hj⟩

omit [NumberField F] [NumberField E] in

theorem mem_cutSet_iff (y : GeomPt Y E) {k : Fin n} (hk : GenAt Y w (below y.1) k) :
    y ∈ cutSet Y E w c ↔ ∀ i, ∑ l, coef Y E c i l * valAt y.1 (w l / w k) = 0 := by
  refine ⟨fun h => h k hk, fun h k' hk' i => ?_⟩
  have e (l) : valAt y.1 (w l / w k') = valAt y.1 (w l / w k) * valAt y.1 (w k / w k') := by
    rw [← valAt_mul _ (hk.2 l) (hk'.2 k)]
    rw [div_mul_div_cancel₀ hk.1]
  rw [Finset.sum_congr rfl fun l _ => by rw [e l, ← mul_assoc], ← Finset.sum_mul, h i, zero_mul]

omit [NumberField F] [NumberField E] in

theorem le_cutOrd_iff (hS : (cutSet Y E w c).Nonempty) (Δ : Y.Dv) {f : Y.Fn} (hf : f ≠ 0)
    (hr : ∀ y ∈ cutSet Y E w c, Δ.RegularAt (below y.1) f) (a : ℕ) :
    a ≤ cutOrd Y E w c Δ f ↔ ∀ y ∈ cutSet Y E w c,
      ∃ b ∈ IsLocalRing.maximalIdeal (Y.X.presheaf.stalk (below y.1)) ^ a,
        algebraMap _ Y.Fn b = f * (eqn Δ (below y.1) : Y.Fn) := by
  have h0 : 0 ∈ {a : ℕ | ∀ y ∈ cutSet Y E w c,
      ∃ b ∈ IsLocalRing.maximalIdeal (Y.X.presheaf.stalk (below y.1)) ^ a,
        algebraMap _ Y.Fn b = f * (eqn Δ (below y.1) : Y.Fn)} := fun y hy => by
    obtain ⟨b, hb⟩ := (Δ.exists_isEqn (below y.1)).choose_spec.regularAt_iff.1 (hr y hy)
    exact ⟨b, by simp, hb⟩
  have hb : BddAbove {a : ℕ | ∀ y ∈ cutSet Y E w c,
      ∃ b ∈ IsLocalRing.maximalIdeal (Y.X.presheaf.stalk (below y.1)) ^ a,
        algebraMap _ Y.Fn b = f * (eqn Δ (below y.1) : Y.Fn)} := by
    obtain ⟨y, hy⟩ := hS
    obtain ⟨b, -, hb⟩ := h0 y hy
    have hk := Ideal.iInf_pow_eq_bot_of_isLocalRing
      (IsLocalRing.maximalIdeal (Y.X.presheaf.stalk (below y.1))) (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    have hb0 : b ≠ 0 := fun e => mul_ne_zero hf (Units.ne_zero _) (by rw [← hb, e, map_zero])
    obtain ⟨m, hm⟩ : ∃ m, b ∉ IsLocalRing.maximalIdeal (Y.X.presheaf.stalk (below y.1)) ^ m := by
      by_contra! h
      exact hb0 (Ideal.mem_bot.1 (hk ▸ Ideal.mem_iInf.2 h))
    refine ⟨m, fun a ha => ?_⟩
    by_contra! hlt
    obtain ⟨b', hb', e⟩ := ha y hy
    obtain rfl := IsFractionRing.injective _ Y.Fn (e.trans hb.symm)
    exact hm (Ideal.pow_le_pow_right hlt.le hb')
  refine ⟨fun h y hy => ?_, fun h => le_csSup hb h⟩
  obtain ⟨b, hb', e⟩ := Nat.sSup_mem ⟨0, h0⟩ hb y hy
  exact ⟨b, Ideal.pow_le_pow_right h hb', e⟩

omit [NumberField F] [NumberField E] in

theorem cutOrd_zero (Δ : Y.Dv) : cutOrd Y E w c Δ 0 = 0 := by
  refine Set.Infinite.Nat.sSup_eq_zero ?_
  refine Set.infinite_univ.mono fun a _ y _ => ⟨0, zero_mem _, by rw [map_zero, zero_mul]⟩

section Proj

variable (F) (N : ℕ)

abbrev crd : Fin (N + 1) → (proj F N).Fn := (proj F N).coordFn (proj_gen_mem F N 0)

def unitCoef (i : Fin N) (l : Fin (N + 1)) : 𝓞 E := if l = i.succ then 1 else 0

omit [NumberField F] in
theorem genAt_crd (x : (proj F N).X) (k : Fin (N + 1)) :
    GenAt (proj F N) (crd F N) x k ↔ (proj F N).ι x ∈ chart F N k :=
  (genAt_iff _ _ ((proj F N).bpf_hyp _) x k).trans ((proj F N).generatesAt_coordFn_iff _ k x)

omit [NumberField F] [NumberField E] in
theorem sum_unitCoef (i : Fin N) (v : Fin (N + 1) → AlgebraicClosure E) :
    ∑ l, coef (proj F N) E (unitCoef E N) i l * v l = v i.succ := by
  rw [Finset.sum_eq_single i.succ]
  · simp [coef, unitCoef]
  · intro l _ hl; simp [coef, unitCoef, hl]
  · simp

omit [NumberField F] [NumberField E] in
theorem mem_cutSet_unit (y : GeomPt (proj F N) E) :
    y ∈ cutSet (proj F N) E (crd F N) (unitCoef E N) ↔
      ∀ i : Fin N, (proj F N).ι (below y.1) ∉ chart F N i.succ := by
  obtain ⟨k, hk⟩ : ∃ k : Fin (N + 1), GenAt (proj F N) (crd F N) (below y.1) k :=
    exists_genAt _ _ ((proj F N).bpf_hyp (proj_gen_mem F N 0)) (below y.1)
  refine (mem_cutSet_iff _ E _ _ y hk).trans (forall_congr' fun i : Fin N => ?_)
  rw [sum_unitCoef F E N i fun l => valAt y.1 (crd F N l / crd F N k), valAt_eq_zero_iff _ (hk.2 _),
    ← genAt_crd]
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · have h0 : crd F N (Fin.succ i) ≠ 0 := fun e => h.ne_zero (by rw [e, zero_div])
    refine ⟨h0, fun l => ?_⟩
    have := (hk.2 l).mul h.inv.regAt
    rwa [inv_div, div_mul_div_cancel₀ hk.1] at this
  · obtain ⟨a, ha⟩ := hk.2 (Fin.succ i)
    obtain ⟨b, hb⟩ := h.2 k
    refine ⟨a, IsUnit.of_mul_eq_one b (IsFractionRing.injective _ (proj F N).Fn ?_), ha⟩
    rw [map_mul, ha, hb, map_one, div_mul_div_cancel₀ hk.1, div_self h.1]

def back : PSpace F N ⟶ (proj F N).X := @inv _ _ _ _ _ (isIso_proj_ι F N)

omit [NumberField F] in
theorem back_ι : back F N ≫ (proj F N).ι = 𝟙 _ := @IsIso.inv_hom_id _ _ _ _ _ (isIso_proj_ι F N)

omit [NumberField F] in
theorem back_str : back F N ≫ (proj F N).str = PSpace.str F N :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (back_ι F N)).trans (Category.id_comp _))

def ptOf (v : Fin (N + 1) → AlgebraicClosure E) (hv : v ≠ 0) : GeomPt (proj F N) E :=
  ⟨pt ((algebraMap E (AlgebraicClosure E)).comp (algebraMap F E)) v (span_range_eq_top_iff_ne_zero.2 hv) ≫
    back F N, by
      refine (Category.assoc _ _ _).trans ?_
      rw [back_str]; exact pt_str _ _ _⟩

omit [NumberField F] [NumberField E] in
theorem ptOf_ι (v : Fin (N + 1) → AlgebraicClosure E) (hv : v ≠ 0) : (ptOf F E N v hv).1 ≫ (proj F N).ι =
    pt ((algebraMap E (AlgebraicClosure E)).comp (algebraMap F E)) v (span_range_eq_top_iff_ne_zero.2 hv) := by
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (back_ι F N)).trans
    (Category.comp_id _))

omit [NumberField F] [NumberField E] in
theorem ptOf_mem_chart (v : Fin (N + 1) → AlgebraicClosure E) (hv : v ≠ 0) (j : Fin (N + 1)) :
    (proj F N).ι (below (ptOf F E N v hv).1) ∈ chart F N j ↔ v j ≠ 0 := by
  have h : (proj F N).ι (below (ptOf F E N v hv).1) ∈ chart F N j ↔
      IsLocalRing.closedPoint (AlgebraicClosure E) ∈ ((ptOf F E N v hv).1 ≫ (proj F N).ι) ⁻¹ᵁ chart F N j := Iff.rfl
  rw [h, ptOf_ι]
  refine (SetLike.ext_iff.1 (pt_preimage_chart _ v _ j) _).trans (mem_spOpen.trans ?_)
  exact (IsLocalRing.notMem_maximalIdeal).trans isUnit_iff_ne_zero

omit [NumberField F] [NumberField E] in
theorem exists_ptOf (y : GeomPt (proj F N) E) : ∃ v hv, y = ptOf F E N v hv := by
  obtain ⟨v, hv, e⟩ := exists_eq_pt (N := N) ((algebraMap E (AlgebraicClosure E)).comp (algebraMap F E))
    (y.1 ≫ (proj F N).ι) ((Category.assoc _ _ _).trans y.2)
  refine ⟨v, span_range_eq_top_iff_ne_zero.1 hv, Subtype.ext ?_⟩
  rw [← cancel_mono (proj F N).ι, ptOf_ι]; exact e

omit [NumberField F] [NumberField E] in
theorem ptOf_eq_iff (v v' : Fin (N + 1) → AlgebraicClosure E) (hv : v ≠ 0) (hv' : v' ≠ 0) :
    ptOf F E N v hv = ptOf F E N v' hv' ↔ ∃ u : (AlgebraicClosure E)ˣ, v' = u • v := by
  rw [← pt_eq_pt_iff ((algebraMap E (AlgebraicClosure E)).comp (algebraMap F E))
    (span_range_eq_top_iff_ne_zero.2 hv) (span_range_eq_top_iff_ne_zero.2 hv'), ← ptOf_ι F E N v hv,
    ← ptOf_ι F E N v' hv']
  exact Subtype.ext_iff.trans (cancel_mono _).symm

def origin : GeomPt (proj F N) E := ptOf F E N (Pi.single 0 1) (by simp)

theorem cutSet_unit : cutSet (proj F N) E (crd F N) (unitCoef E N) = {origin F E N} := by
  ext y
  rw [mem_cutSet_unit, Set.mem_singleton_iff]
  constructor
  · intro h
    obtain ⟨v, hv, rfl⟩ := exists_ptOf F E N y
    simp only [ptOf_mem_chart, not_not] at h
    have h0 : v 0 ≠ 0 := fun e => hv (funext (Fin.cases e h))
    refine ((ptOf_eq_iff F E N _ _ _ _).2 ⟨Units.mk0 _ h0, funext (Fin.cases ?_ fun i => ?_)⟩).symm
    · simp [Units.smul_def]
    · simp [Units.smul_def, h i]
  · rintro rfl i
    rw [origin, ptOf_mem_chart]
    simp

omit [NumberField F] in

theorem not_cutGood_zero (bd : (proj F (N + 1)).Cl) :
    ¬ cutGood (proj F (N + 1)) E (crd F (N + 1)) 0 bd := fun h => by
  refine Set.infinite_of_injective_forall_mem (s := cutSet (proj F (N + 1)) E (crd F (N + 1)) 0)
    (f := fun t : AlgebraicClosure E => ptOf F E (N + 1) (Fin.cons 1 fun _ => t)
      (fun e => one_ne_zero (congrFun e 0))) (fun t t' e => ?_) (fun t k _ i => ?_) h.2.1
  · obtain ⟨u, hu⟩ := (ptOf_eq_iff F E _ _ _ _ _).1 e
    have h0 := congrFun hu 0
    have h1 := congrFun hu (Fin.succ 0)
    simp only [Units.smul_def, Pi.smul_apply, Fin.cons_zero, Fin.cons_succ, smul_eq_mul, mul_one] at h0 h1
    rw [h1, ← h0, one_mul]
  · simp [coef]

omit [NumberField F] in

theorem exists_poly_quot {F : Type} [Field F] (Y : Var F) {i : Fin (Y.N + 1)}
    (hi : Y.ι (genericPoint Y.X) ∈ chart F Y.N i) {x : Y.X} (hx : Y.ι x ∈ chart F Y.N i)
    (a : Y.X.presheaf.stalk x) : ∃ p q : MvPolynomial (Fin (Y.N + 1)) F,
      UnitAt x (aeval (Y.coordFn hi) q) ∧
        algebraMap _ Y.Fn a * aeval (Y.coordFn hi) q = aeval (Y.coordFn hi) p := by
  have hU : IsAffineOpen (Y.ι ⁻¹ᵁ chart F Y.N i) := (isAffineOpen_chart F Y.N i).preimage _
  have key (s : Γ(Y.X, Y.ι ⁻¹ᵁ chart F Y.N i)) : ∃ g : MvPolynomial (Fin (Y.N + 1)) F, aeval (Y.coordFn hi) g =
      algebraMap (Y.X.presheaf.stalk x) Y.Fn (Y.X.presheaf.germ (Y.ι ⁻¹ᵁ chart F Y.N i) x hx s) := by
    obtain ⟨s, rfl⟩ := Y.ι.app_surjective _ (isAffineOpen_chart F Y.N i) s
    obtain ⟨g, rfl⟩ := aeval_ratio_surjective F Y.N i s
    have e := Y.aeval_coordFn hi g
    rw [Var.chartHom, ← LB.resG_app, fnOf_resG] at e
    exact ⟨g, e.trans (algebraMap_germ (U := Y.ι ⁻¹ᵁ chart F Y.N i) (x := x) hx _).symm⟩
  letI := Y.X.presheaf.algebra_section_stalk (⟨x, hx⟩ : (Y.ι ⁻¹ᵁ chart F Y.N i :))
  have := hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨⟨r, s⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (S := Y.X.presheaf.stalk x) a
  obtain ⟨p, hp⟩ := key r
  obtain ⟨q, hq⟩ := key s.1
  refine ⟨p, q, ⟨_, IsLocalization.map_units (Y.X.presheaf.stalk x) s, hq.symm⟩, ?_⟩
  rw [hp, hq, ← map_mul]
  exact congrArg _ e

omit [NumberField F] [NumberField E] in

theorem tangent_eq_zero {F : Type} [Field F] [Algebra F E] (Y : Var F) {i : Fin (Y.N + 1)}
    (hi : Y.ι (genericPoint Y.X) ∈ chart F Y.N i) (y : GeomPt Y E) (hx : Y.ι (below y.1) ∈ chart F Y.N i)
    (u : Fin (Y.N + 1) → Y.X.presheaf.stalk (below y.1)) (hu : ∀ l, algebraMap _ Y.Fn (u l) = Y.coordFn hi l)
    (δ : Y.X.presheaf.stalk (below y.1) →+ AlgebraicClosure E) (hδ : IsTangent Y E y δ)
    (h : ∀ l, δ (u l) = 0) : δ = 0 := by
  have key (p : MvPolynomial (Fin (Y.N + 1)) F) :
      ∃ b, algebraMap _ Y.Fn b = aeval (Y.coordFn hi) p ∧ δ b = 0 := by
    induction p using MvPolynomial.induction_on with
    | C t =>
      obtain ⟨b, hb⟩ := Y.regAt_algebraMap (below y.1) t
      exact ⟨b, by rw [algHom_C, hb], hδ.2 b t hb⟩
    | add p q hp hq =>
      obtain ⟨a, ha, ha'⟩ := hp
      obtain ⟨b, hb, hb'⟩ := hq
      exact ⟨a + b, by rw [map_add, map_add, ha, hb], by rw [map_add, ha', hb', add_zero]⟩
    | mul_X p j hp =>
      obtain ⟨a, ha, ha'⟩ := hp
      exact ⟨a * u j, by rw [map_mul, map_mul, ha, hu, aeval_X],
        by rw [hδ.1, ha', h, mul_zero, mul_zero, add_zero]⟩
  ext a
  obtain ⟨p, q, ⟨b, hb, eb⟩, e⟩ := exists_poly_quot Y hi hx a
  obtain ⟨b', eb', hb'⟩ := key q
  obtain ⟨d, ed, hd⟩ := key p
  obtain rfl := IsFractionRing.injective _ Y.Fn (eb.trans eb'.symm)
  obtain rfl : a * b = d := IsFractionRing.injective _ Y.Fn (by rw [map_mul, eb, ed, e])
  rw [hδ.1, hb', mul_zero, zero_add] at hd
  exact (mul_eq_zero.1 hd).resolve_left (hb.map _).ne_zero

theorem origin_mem_chart (j : Fin (N + 1)) :
    (proj F N).ι (below (origin F E N).1) ∈ chart F N j ↔ j = 0 := by
  rw [origin, ptOf_mem_chart]
  by_cases h : j = 0 <;> simp [h]

theorem cutGood_unit : cutGood (proj F N) E (crd F N) (unitCoef E N) ((proj F N).supp (projHyp F N)) := by
  refine ⟨exists_genAt _ _ ((proj F N).bpf_hyp (proj_gen_mem F N 0)), ?_, ?_⟩
  · rw [cutSet_unit]; exact Set.finite_singleton _
  · rw [cutSet_unit]
    rintro _ rfl
    have h0 := (origin_mem_chart F E N 0).2 rfl
    refine ⟨fun k hk u hu δ hδ h => ?_, fun h => ((proj F N).mem_supp_hyp _ _).1 h h0⟩
    obtain rfl := (origin_mem_chart F E N k).1 ((genAt_crd F N _ k).1 hk)
    have e1 : crd F N 0 = 1 := (proj F N).coordFn_self _
    simp only [e1, div_one] at hu
    refine tangent_eq_zero E (proj F N) (proj_gen_mem F N 0) _ h0 u hu δ hδ (Fin.cases ?_ fun i => ?_)
    · exact hδ.2 _ 1 (by rw [map_one]; exact (hu 0).trans e1)
    · exact (sum_unitCoef F E N i fun l => δ (u l)).symm.trans (h i)

theorem not_cutGood_unit_top : ¬ cutGood (proj F N) E (crd F N) (unitCoef E N) ⊤ := fun h =>
  (h.2.2 (origin F E N) (by rw [cutSet_unit]; rfl)).2 trivial

theorem cutHt_unit {C : CxSt F} (A : Adl C (proj F N)) :
    cutHt (proj F N) E (crd F N) (unitCoef E N) A = A.ht (below (origin F E N).1) := by
  unfold cutHt
  rw [cutSet_unit]
  exact finsum_mem_singleton

theorem one_le_cutOrd_iff (j : Fin (N + 1)) :
    1 ≤ cutOrd (proj F N) E (crd F N) (unitCoef E N) (projHyp F N) (crd F N j) ↔ j ≠ 0 := by
  have hg := ((proj F N).generatesAt_coordFn_iff (proj_gen_mem F N 0) j _).2 (proj_gen_mem F N j)
  have hr (x) : (projHyp F N).RegularAt x (crd F N j) :=
    Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 ((proj F N).coordFn_mem (proj_gen_mem F N 0) j) x
  refine (le_cutOrd_iff (proj F N) E (crd F N) (unitCoef E N)
    (by rw [cutSet_unit]; exact Set.singleton_nonempty _) _ hg.ne_zero (fun y _ => hr _) 1).trans ?_
  rw [cutSet_unit]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [pow_one, ne_eq, ← origin_mem_chart F E N j]
  refine ((projHyp F N).exists_isEqn _).choose_spec.vanishesAt_iff.symm.trans (vanishesAt_iff.trans ?_)
  exact (and_iff_right (hr _)).trans
    (not_congr ((proj F N).generatesAt_coordFn_iff (proj_gen_mem F N 0) j _))

omit [NumberField F] [NumberField E] in

theorem exists_tangent {F : Type} [Field F] [Algebra F E] (Y : Var F) (y : GeomPt Y E)
    (z : Sp (DualNumber (AlgebraicClosure E)) ⟶ Y.X)
    (hz : z ≫ Y.str = spMap ((algebraMap _ (DualNumber (AlgebraicClosure E))).comp
      ((algebraMap E (AlgebraicClosure E)).comp (algebraMap F E))))
    (hy : spMap (TrivSqZeroExt.fstHom (AlgebraicClosure E) _ _).toRingHom ≫ z = y.1)
    (hne : spMap (algebraMap _ (DualNumber (AlgebraicClosure E))) ≫ y.1 ≠ z) :
    ∃ δ, IsTangent Y E y δ ∧ δ ≠ 0 := by
  have h1 (x : Y.X) (hx : z (IsLocalRing.closedPoint _) = x) :
      ∃ φ : Y.X.presheaf.stalk x →+* DualNumber (AlgebraicClosure E), spMap φ ≫ Y.X.fromSpecStalk x = z := by
    subst hx
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of _) z⟩
  obtain ⟨φ, hφ⟩ := h1 (below y.1) (by
    rw [← hy]
    have : IsLocalHom (TrivSqZeroExt.fstHom (AlgebraicClosure E) (AlgebraicClosure E)
      (AlgebraicClosure E)).toRingHom := ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
    have e := IsLocalRing.comap_closedPoint (TrivSqZeroExt.fstHom (AlgebraicClosure E) (AlgebraicClosure E)
      (AlgebraicClosure E)).toRingHom
    exact congrArg z e.symm)
  have hy' := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of _) y.1
  have hev : (TrivSqZeroExt.fstHom (AlgebraicClosure E) _ _).toRingHom.comp φ =
      (Scheme.stalkClosedPointTo y.1).hom := by
    have e := hy.trans hy'.symm
    rw [← hφ, ← Category.assoc, ← Spec.map_comp] at e
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 e))
  have hev' (a) : (Scheme.stalkClosedPointTo y.1).hom a = (φ a).fst := (RingHom.congr_fun hev a).symm
  refine ⟨((TrivSqZeroExt.sndHom _ _).toAddMonoidHom).comp φ.toAddMonoidHom, ⟨fun a b => ?_, fun a t h => ?_⟩,
    fun h0 => hne ?_⟩
  · change (φ (a * b)).snd = _ * (φ b).snd + _ * (φ a).snd
    rw [map_mul, DualNumber.snd_mul, hev', hev', mul_comm (φ a).snd]
  · have e : Y.X.fromSpecStalk (below y.1) ≫ Y.str = Spec.map ((Scheme.ΓSpecIso (.of F)).inv ≫ Y.str.appTop ≫
        Y.X.presheaf.germ ⊤ (below y.1) trivial) := by
      rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
        ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    rw [← hφ, Category.assoc, e, ← Spec.map_comp] at hz
    have e' := RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective hz)) t
    have ea : a = Y.X.presheaf.germ ⊤ (below y.1) trivial (algebraMap F Γ(Y.X, ⊤) t) :=
      IsFractionRing.injective _ Y.Fn (h.trans ((IsScalarTower.algebraMap_apply F Γ(Y.X, ⊤) Y.Fn t).trans
        (algebraMap_germ (U := ⊤) (x := below y.1) trivial _).symm))
    change (φ a).snd = 0
    rw [ea]
    exact (congrArg TrivSqZeroExt.snd e').trans (TrivSqZeroExt.snd_inl _ _)
  · rw [← hy', ← Category.assoc, ← Spec.map_comp]
    refine Eq.trans (congrArg (fun ψ => spMap ψ ≫ _) (RingHom.ext fun a => ?_)) hφ
    have : (φ a).snd = 0 := DFunLike.congr_fun h0 a
    exact TrivSqZeroExt.ext (hev' a) this.symm

theorem exists_tangent_origin : ∃ δ, IsTangent (proj F 1) E (origin F E 1) δ ∧ δ ≠ 0 := by
  have hv : Ideal.span (Set.range (![1, DualNumber.eps] : Fin 2 → DualNumber (AlgebraicClosure E))) = ⊤ :=
    (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨0, rfl⟩)
  refine exists_tangent E _ _ (pt (N := 1) ((algebraMap _ (DualNumber (AlgebraicClosure E))).comp
      ((algebraMap E (AlgebraicClosure E)).comp (algebraMap F E))) _ hv ≫ back F 1) ?_ ?_ fun h => ?_
  · rw [Category.assoc, back_str]; exact pt_str _ _ _
  · rw [← Category.assoc, spMap_pt]
    refine congrArg (· ≫ back F 1) ?_
    congr 1
    funext i
    fin_cases i <;> simp
  · have h' := congrArg (· ≫ (proj F 1).ι) h
    simp only [Category.assoc] at h'
    rw [origin, ptOf_ι, back_ι] at h'
    obtain ⟨u, hu⟩ := (pt_eq_pt_iff _ _ _).1 ((spMap_pt _ _ _ _).symm.trans (h'.trans (Category.comp_id _)))
    have h1 := congrArg TrivSqZeroExt.snd (congrFun hu 1)
    simp [Units.smul_def] at h1

theorem not_cutGood_double (bd : (proj F 1).Cl) :
    ¬ cutGood (proj F 1) E ![1, crd F 1 1, crd F 1 1 ^ 2] (fun _ => ![0, 0, 1]) bd := fun h => by
  have h0 := (origin_mem_chart F E 1 0).2 rfl
  have e1 : crd F 1 0 = 1 := (proj F 1).coordFn_self _
  have hg := (genAt_crd F 1 _ 0).2 h0
  obtain ⟨u, hu⟩ := hg.2 1
  have hm := (mem_cutSet_iff (proj F 1) E (crd F 1) (unitCoef E 1) _ hg).1
    (by rw [cutSet_unit]; rfl) (0 : Fin 1)
  rw [sum_unitCoef F E 1 0 fun l => valAt (origin F E 1).1 (crd F 1 l / crd F 1 0)] at hm
  replace hm : valAt (origin F E 1).1 (crd F 1 1 / crd F 1 0) = 0 := hm
  rw [← hu, valAt_algebraMap] at hm
  rw [e1, div_one] at hu
  have hu' (l : Fin 3) : algebraMap _ (proj F 1).Fn (![1, u, u * u] l) =
      ![1, crd F 1 1, crd F 1 1 ^ 2] l / ![1, crd F 1 1, crd F 1 1 ^ 2] 0 := by
    fin_cases l <;> simp [hu, sq]
  have hg' : GenAt (proj F 1) ![1, crd F 1 1, crd F 1 1 ^ 2] (below (origin F E 1).1) 0 :=
    ⟨one_ne_zero, fun l => ⟨_, hu' l⟩⟩
  obtain ⟨δ, hδ, hδ0⟩ := exists_tangent_origin F E
  refine hδ0 ((h.2.2 (origin F E 1) ((mem_cutSet_iff _ E _ _ _ hg').2 fun i => ?_)).1 0 hg' _ hu' δ hδ fun i => ?_)
  · simp only [← hu', valAt_algebraMap]
    simp [coef, Fin.sum_univ_three, hm]
  · simp [coef, Fin.sum_univ_three, hδ.1, hm]

end Proj

omit [NumberField F] [NumberField E] in

theorem cutGood_empty (hd : 1 ≤ Y.dim) (bd : Y.Cl) (Δ : Y.Dv) (f : Y.Fn) :
    cutSet Y E ![1] (fun _ _ => 1) = ∅ ∧ cutGood Y E ![1] (fun _ _ => 1) bd ∧
      cutOrd Y E ![1] (fun _ _ => 1) Δ f = 0 := by
  have hg (x : Y.X) : GenAt Y ![1] x 0 := ⟨one_ne_zero, fun l => ⟨1, by fin_cases l; simp⟩⟩
  have e : cutSet Y E ![1] (fun _ _ => 1) = ∅ := Set.eq_empty_of_forall_notMem fun y hy => by
    have h := hy 0 (hg _) ⟨0, hd⟩
    have h1 := valAt_algebraMap y.1 1
    rw [map_one, map_one] at h1
    simp [coef, h1] at h
  refine ⟨e, ⟨fun x => ⟨0, hg x⟩, by rw [e]; exact Set.finite_empty, by rw [e]; exact fun _ h => h.elim⟩, ?_⟩
  refine Set.Infinite.Nat.sSup_eq_zero (Set.infinite_univ.mono fun a _ => ?_)
  rw [e]; exact fun _ h => h.elim

end GlobalTheory.TrueGeo.CutModel

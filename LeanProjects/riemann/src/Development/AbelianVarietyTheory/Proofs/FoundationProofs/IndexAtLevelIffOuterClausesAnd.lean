import Mathlib
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IndexAtLevel
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero

noncomputable section

namespace GlobalTheory.LevelIndexCompare

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

section General

theorem det_eq_algebraMap_det {R K A W : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup A] [Module R A] [Module.Free R A] [Module.Finite R A]
    [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
    (j : A →ₗ[R] W) (hj : Function.Injective j) (hs : Submodule.span K (Set.range j) = ⊤)
    (G : W →ₗ[K] W) (G₀ : A →ₗ[R] A) (h : ∀ x, G (j x) = j (G₀ x)) :
    LinearMap.det G = algebraMap R K (LinearMap.det G₀) := by
  classical
  let b := Module.Free.chooseBasis R A
  have hli : LinearIndependent K (fun i => j (b i)) :=
    (LinearIndependent.iff_fractionRing R K).1 (b.linearIndependent.map' j (LinearMap.ker_eq_bot.2 hj))
  have hx : ∀ x : A, j x = ∑ i, algebraMap R K (b.repr x i) • j (b i) := by
    intro x
    conv_lhs => rw [← b.sum_repr x, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, algebraMap_smul]
  have hsp : ⊤ ≤ Submodule.span K (Set.range fun i => j (b i)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let c := Module.Basis.mk hli hsp
  have hc : ∀ i, c i = j (b i) := fun i => Module.Basis.mk_apply hli hsp i
  rw [← LinearMap.det_toMatrix c, ← LinearMap.det_toMatrix b, RingHom.map_det]
  congr 1
  ext i k
  rw [LinearMap.toMatrix_apply, hc, h, hx]
  simp only [← hc, map_sum, map_smul, Module.Basis.repr_self, RingHom.mapMatrix_apply, Matrix.map_apply,
    LinearMap.toMatrix_apply]
  simp [Finsupp.single_apply, Algebra.algebraMap_eq_smul_one]

end General

variable (D : D7) (u : D.what₂.Word)

theorem val_ne_top (w : D.what₂.places.Pl) {x : D.what₂.LL} (hx : x ≠ 0) :
    ∃ n : ℤ, D.what₂.places.val w x = (n : WithTop ℤ) := ⟨_, D.val_eq w x hx⟩

theorem val_of_addVal (w : D.what₂.places.Pl) (r : LT.Ow D w) (n : ℕ)
    (h : (haveI := D.intW_dvr w; IsDiscreteValuationRing.addVal (LT.Ow D w) r) = (n : ℕ∞)) :
    D.what₂.places.val w (r : D.what₂.LL) = (((n : ℕ) : ℤ) : WithTop ℤ) := by
  haveI := D.intW_dvr w
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (LT.Ow D w)
  have hu : ∀ e : (LT.Ow D w)ˣ, D.what₂.places.val w ((e : LT.Ow D w) : D.what₂.LL) = 0 := by
    intro e
    have h1 : (0 : WithTop ℤ) ≤ D.what₂.places.val w ((e : LT.Ow D w) : D.what₂.LL) := (e : LT.Ow D w).2
    have h2 : (0 : WithTop ℤ) ≤ D.what₂.places.val w ((e⁻¹ : (LT.Ow D w)ˣ) : LT.Ow D w) := ((e⁻¹ : (LT.Ow D w)ˣ) : LT.Ow D w).2
    have h3 : D.what₂.places.val w ((e : LT.Ow D w) : D.what₂.LL) +
        D.what₂.places.val w ((e⁻¹ : (LT.Ow D w)ˣ) : LT.Ow D w) = 0 := by
      rw [← AddValuation.map_mul, ← Subring.coe_mul, Units.mul_inv]
      simp
    exact le_antisymm (h3 ▸ le_add_of_nonneg_right h2) h1
  have hform : ∀ (e : (LT.Ow D w)ˣ) (k : ℕ), D.what₂.places.val w (((e : LT.Ow D w) * ϖ ^ k : LT.Ow D w) : D.what₂.LL) =
      k • D.what₂.places.val w (ϖ : D.what₂.LL) := by
    intro e k
    rw [Subring.coe_mul, AddValuation.map_mul, hu, zero_add, Subring.coe_pow, AddValuation.map_pow]
  obtain ⟨p, hp⟩ := val_ne_top D w (x := (ϖ : D.what₂.LL)) (fun h0 => hϖ.ne_zero (Subtype.ext h0))
  have hp0 : 0 ≤ p := by
    have h1 : (0 : WithTop ℤ) ≤ D.what₂.places.val w (ϖ : D.what₂.LL) := ϖ.2
    rw [hp] at h1; exact_mod_cast h1
  have hp1 : p = 1 := by
    obtain ⟨x, hx⟩ := D.what₂.places.val_surj w 1
    have hxO : x ∈ LT.Ow D w := by
      show (0 : WithTop ℤ) ≤ D.what₂.places.val w x
      rw [hx]; exact_mod_cast zero_le_one
    have hx0 : (⟨x, hxO⟩ : LT.Ow D w) ≠ 0 := by
      intro h0
      have : x = 0 := congrArg Subtype.val h0
      rw [this, AddValuation.map_zero] at hx
      exact WithTop.top_ne_coe hx
    obtain ⟨k, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    have h2 := hform e k
    rw [← he, hp, ← WithTop.coe_nsmul] at h2
    have h3 : (1 : ℤ) = k • p := by
      have : ((1 : ℤ) : WithTop ℤ) = ((k • p : ℤ) : WithTop ℤ) := hx.symm.trans h2
      exact WithTop.coe_injective this
    rw [nsmul_eq_mul] at h3
    exact Int.eq_one_of_mul_eq_one_left hp0 h3.symm
  have hr : r ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨k, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  have hk : (k : ℕ∞) = n := (IsDiscreteValuationRing.addVal_def r e hϖ k he).symm.trans h
  have hk' : k = n := by exact_mod_cast hk
  rw [he, hform, hp, hp1, ← WithTop.coe_nsmul, hk']
  simp

theorem rankAll_eq : rankAll D u = D.duS u := by
  unfold rankAll D7.duS
  rw [Module.finrank_eq_card_basis ((D.fm u).lat 0).b, ← (D.fm u).Fi_zero, ← ((D.fm u).emb_basis 0).2,
    finrank_span_eq_card ((D.fm u).emb_basis 0).1]

theorem Sram_fg (w : D.what₂.places.Pl) : (LT.Sram D u w).FG := by
  rw [D.Sram_eq u w]
  obtain ⟨s, hs⟩ := D.ramL_fg u
  refine ⟨s, le_antisymm (Submodule.span_mono ?_) ?_⟩
  · rw [← hs]; exact Submodule.subset_span
  · unfold locW
    rw [Submodule.span_le, ← hs]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      have hr : (r : D.what₂.LL) ∈ LT.Ow D w := (D.val_nonneg_iff w r).2 ((D.plEq w).valuation_le_one r)
      have : r • y = (⟨r, hr⟩ : LT.Ow D w) • y := by
        rw [Subring.smul_def]; exact (algebraMap_smul D.what₂.LL r y).symm
      rw [this]
      exact Submodule.smul_mem _ _ hy

def incl (w : D.what₂.places.Pl) : LT.Sram D u w →ₗ[LT.Ow D w] (D.fm u).ramSub where
  toFun x := ⟨x.1, x.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem incl_injective (w : D.what₂.places.Pl) : Function.Injective (incl D u w) :=
  fun _ _ h => Subtype.ext (congrArg (fun y : (D.fm u).ramSub => (y : LT.Vl D u 0)) h)

theorem span_incl (w : D.what₂.places.Pl) : Submodule.span D.what₂.LL (Set.range (incl D u w)) = ⊤ := by
  haveI := D.intW_dvr w
  haveI := D.intW_frac w
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  have h1 : x ∈ Submodule.span D.what₂.LL (((D.fm u).S 0 w : Set (LT.Vl D u 0))) := by
    have h0 : x ∈ Submodule.span D.what₂.LL (((D.fm u).lat 0).L : Set (LT.Vl D u 0)) := by
      rw [((D.fm u).lat_good 0).2.2]; trivial
    exact Submodule.span_mono Submodule.subset_span h0
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (LT.Ow D w)) D.what₂.LL _ x h1
  rw [Submodule.span_eq] at ht
  have ht0 : ((t : LT.Ow D w) : D.what₂.LL) ≠ 0 := fun h0 => nonZeroDivisors.coe_ne_zero t (Subtype.ext h0)
  have hm : (t : LT.Ow D w) • x ∈ LT.Sram D u w := ⟨ht, (D.fm u).ramSub.smul_mem ((t : LT.Ow D w) : D.what₂.LL) hx⟩
  have : (⟨x, hx⟩ : (D.fm u).ramSub) = ((t : LT.Ow D w) : D.what₂.LL)⁻¹ • incl D u w ⟨_, hm⟩ := by
    apply Subtype.ext
    show x = ((t : LT.Ow D w) : D.what₂.LL)⁻¹ • (((t : LT.Ow D w) : D.what₂.LL) • x)
    rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

def URamStable (v : (D.mem u).A.vT) : Prop :=
  ∀ x ∈ (D.fm u).ramSub, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x)

theorem T_ne_zero : ((D.mem u).A.T : ℂ) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero

theorem emb_zpow_smul (n : ℤ) (x : LT.Vl D u 0) :
    (D.fm u).emb 0 ((((D.mem u).A.T : D.what₂.LL) ^ n) • x) = (((D.mem u).A.T : ℂ) ^ n) • (D.fm u).emb 0 x := by
  rw [LinearMap.map_smulₛₗ, map_zpow₀, map_natCast]

theorem exists_isScaledU_iff (w : D.what₂.places.Pl) (v : (D.mem u).A.vT) :
    (∃ g, IsScaledU D u w v g) ↔ URamStable D u v := by
  constructor
  · rintro ⟨g, hg⟩ x hx
    refine ⟨(((D.mem u).A.T : D.what₂.LL) ^ (-(D.fm u).bTop ((D.fm u).tauOf w v))) • (g ⟨x, hx⟩ : LT.Vl D u 0),
      (D.fm u).ramSub.smul_mem _ (g ⟨x, hx⟩).2, ?_⟩
    rw [emb_zpow_smul, hg, smul_smul, ← zpow_add₀ (T_ne_zero D u), neg_add_cancel, zpow_zero, one_smul]
  · intro h
    let e : (D.fm u).ramSub →ₛₗ[D.what₂.embLL] LT.Fn D u 0 := ((D.fm u).emb 0).comp (D.fm u).ramSub.subtype
    have he : Function.Injective e := ((D.fm u).emb_inj 0).comp Subtype.val_injective
    let f : LT.Fn D u 0 →ₗ[ℂ] LT.Fn D u 0 :=
      (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) • LT.Uop D u 0 v
    have hf : ∀ x, ∃ y, e y = f (e x) := by
      intro x
      obtain ⟨y, hy, hxy⟩ := h x.1 x.2
      refine ⟨⟨(((D.mem u).A.T : D.what₂.LL) ^ ((D.fm u).bTop ((D.fm u).tauOf w v))) • y,
        (D.fm u).ramSub.smul_mem _ hy⟩, ?_⟩
      exact (emb_zpow_smul D u _ y).trans (by rw [hxy]; rfl)
    exact ⟨descend e e he f hf, fun x => descend_spec e e he f hf x⟩

theorem emb_list_prod (w : D.what₂.places.Pl) (g : (D.mem u).A.vT → Module.End D.what₂.LL (D.fm u).ramSub)
    (l : List (D.mem u).A.vT) (hg : ∀ v ∈ l, IsScaledU D u w v (g v)) (x : (D.fm u).ramSub) :
    (D.fm u).emb 0 ((l.map g).prod x : LT.Vl D u 0) =
      (((D.mem u).A.T : ℂ) ^ (l.map fun v => (D.fm u).bTop ((D.fm u).tauOf w v)).sum) •
        (l.foldr (fun v f => (LT.Uop D u 0 v).comp f) LinearMap.id) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, hg v List.mem_cons_self,
      ih (fun v' hv' => hg v' (List.mem_cons_of_mem _ hv')), map_smul, smul_smul, List.map_cons, List.sum_cons,
      zpow_add₀ (T_ne_zero D u)]
    rfl

theorem emb_pow (G : Module.End D.what₂.LL (D.fm u).ramSub) (c : ℂ) (U : Module.End ℂ (LT.Fn D u 0))
    (h : ∀ x : (D.fm u).ramSub, (D.fm u).emb 0 (G x : LT.Vl D u 0) = c • U ((D.fm u).emb 0 (x : LT.Vl D u 0)))
    (n : ℕ) (x : (D.fm u).ramSub) :
    (D.fm u).emb 0 ((G ^ n) x : LT.Vl D u 0) = c ^ n • (U ^ n) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, h, ih, map_smul, smul_smul, pow_succ' c, pow_succ' U, Module.End.mul_apply]

theorem mem_Nlam_iff (w : D.what₂.places.Pl) (g : (D.mem u).A.vT → Module.End D.what₂.LL (D.fm u).ramSub)
    (hg : ∀ v ∈ LT.VVT D u w, IsScaledU D u w v (g v)) (y : LT.Vl D u 0) :
    y ∈ LT.Nlam D u w ↔ ∃ x : LT.Sram D u w,
      y = ((((LT.VVT D u w).toList.map g).prod ^ D.R.m) (incl D u w x) : (D.fm u).ramSub) := by
  have key : ∀ x : (D.fm u).ramSub,
      (D.fm u).emb 0 ((((LT.VVT D u w).toList.map g).prod ^ D.R.m) x : (D.fm u).ramSub) =
        ((((D.mem u).A.T : ℂ) ^ LT.expT D u w) • (LT.Uprod D u 0 w) ^ D.R.m) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
    intro x
    rw [emb_pow D u _ _ (LT.Uprod D u 0 w)
      (emb_list_prod D u w g _ (fun v hv => hg v (Finset.mem_toList.1 hv))), Finset.sum_map_toList,
      ← zpow_natCast, ← zpow_mul, mul_comm]
    rfl
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, (D.fm u).emb_inj 0 (hxy.trans (key (incl D u w ⟨x, hx⟩)).symm)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, key _⟩

theorem index_eq_sum_val_det (w : D.what₂.places.Pl) (g : (D.mem u).A.vT → Module.End D.what₂.LL (D.fm u).ramSub)
    (hg : ∀ v ∈ LT.VVT D u w, IsScaledU D u w v (g v)) (hle : LT.Nlam D u w ≤ LT.Sram D u w)
    (l : ℕ) (hl : lengthN_vw D u w = (l : ℕ∞)) :
    ∃ n : (D.mem u).A.vT → ℤ,
      (∀ v ∈ LT.VVT D u w, D.what₂.places.val w (LinearMap.det (g v)) = ((n v : ℤ) : WithTop ℤ)) ∧
      (l : ℤ) = (D.R.m : ℤ) * ∑ v ∈ LT.VVT D u w, n v := by
  classical
  haveI := D.intW_dvr w
  haveI := D.intW_frac w
  set G : Module.End D.what₂.LL (D.fm u).ramSub := ((LT.VVT D u w).toList.map g).prod ^ D.R.m with hG
  have hmem : ∀ x : LT.Sram D u w, (G (incl D u w x) : LT.Vl D u 0) ∈ LT.Sram D u w :=
    fun x => hle ((mem_Nlam_iff D u w g hg _).2 ⟨x, rfl⟩)
  let G₀ : LT.Sram D u w →ₗ[LT.Ow D w] LT.Sram D u w :=
    LinearMap.codRestrict _ (((D.fm u).ramSub.subtype.restrictScalars (LT.Ow D w)) ∘ₗ
      (G.restrictScalars (LT.Ow D w)) ∘ₗ incl D u w) hmem
  have hr : (LT.Nlam D u w).comap (LT.Sram D u w).subtype = LinearMap.range G₀ := by
    ext y
    rw [Submodule.mem_comap, mem_Nlam_iff D u w g hg]
    exact ⟨fun ⟨x, hx⟩ => ⟨x, Subtype.ext hx.symm⟩, fun ⟨x, hx⟩ => ⟨x, (congrArg Subtype.val hx).symm⟩⟩
  haveI : Module.Finite (LT.Ow D w) (LT.Sram D u w) := Module.Finite.iff_fg.2 (Sram_fg D u w)
  haveI : Module.IsTorsionFree (LT.Ow D w) (LT.Vl D u 0) := .of_smul_eq_zero fun r x h => by
    rw [Subring.smul_def, smul_eq_zero] at h
    exact h.imp Subtype.ext id
  haveI : Module.Free (LT.Ow D w) (LT.Sram D u w) := inferInstance
  have hdet := det_eq_algebraMap_det (incl D u w) (incl_injective D u w) (span_incl D u w) G G₀ (fun x => rfl)
  have hlen : IsDiscreteValuationRing.addVal (LT.Ow D w) (LinearMap.det G₀) = (l : ℕ∞) := by
    rw [← GlobalTheory.length_quotient_range_eq_addVal_det, ← hr]; exact hl
  have hval : D.what₂.places.val w (LinearMap.det G) = (((l : ℕ) : ℤ) : WithTop ℤ) := by
    rw [hdet]; exact val_of_addVal D w _ l hlen
  have hprod : LinearMap.det G = (∏ v ∈ LT.VVT D u w, LinearMap.det (g v)) ^ D.R.m := by
    rw [hG, map_pow, map_list_prod, List.map_map, Finset.prod_map_toList]
    rfl
  have hG0 : LinearMap.det G ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hval
    exact WithTop.top_ne_coe hval
  have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
  have hne : ∀ v ∈ LT.VVT D u w, LinearMap.det (g v) ≠ 0 := by
    rw [hprod] at hG0
    exact Finset.prod_ne_zero_iff.1 (ne_zero_pow hm hG0)
  refine ⟨fun v => vAdd (D.plEq w) (LinearMap.det (g v)), fun v hv => D.val_eq w _ (hne v hv), ?_⟩
  have hsum : ∀ s : Finset (D.mem u).A.vT, (∀ v ∈ s, LinearMap.det (g v) ≠ 0) →
      D.what₂.places.val w (∏ v ∈ s, LinearMap.det (g v)) =
        ((∑ v ∈ s, vAdd (D.plEq w) (LinearMap.det (g v)) : ℤ) : WithTop ℤ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro h
      rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul,
        ih (fun v hv => h v (Finset.mem_insert_of_mem hv)), D.val_eq w _ (h a (Finset.mem_insert_self _ _)),
        WithTop.coe_add]
  rw [hprod, AddValuation.map_pow, hsum _ hne, ← WithTop.coe_nsmul] at hval
  have := WithTop.coe_injective hval
  rw [← this, nsmul_eq_mul]

def IndexWith (bd : D.what₂.places.Pl → ℝ) : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
    LT.Nlam D u w ≤ LT.Sram D u w ∧
    ∃ l : ℕ, lengthN_vw D u w = (l : ℕ∞) ∧ (l : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * bd w

def TopsStable : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T → ∀ v ∈ LT.VVT D u w, URamStable D u v

def boundMax_vp (w : D.what₂.places.Pl) : ℝ :=
  (D.R.m : ℝ) * (rankAll D u : ℝ) * ∑ v ∈ LT.VVT D u w,
    ((product_first_zeroth_parts.amax D u : ℝ) / D.R.k + 2 * (Wtau D u ((D.fm u).tauOf w v) : ℝ) + D.R.k +
      ((D.fm u).bTop ((D.fm u).tauOf w v) : ℝ))

def boundPrice_vp (w : D.what₂.places.Pl) : ℝ :=
  (D.R.m : ℝ) * (rankAll D u : ℝ) * ∑ v ∈ LT.VVT D u w,
    ((product_first_zeroth_parts.amax D u : ℝ) / D.R.k + 3 * (Wtau D u ((D.fm u).tauOf w v) : ℝ) + D.R.k)

def OuterClauses : Prop :=
  ∀ w, product_first_zeroth_parts.OverT D u w →
    product_first_zeroth_parts.Nlam D u w ≤ product_first_zeroth_parts.Sram D u w ∧
    (∃ n : ℕ, product_first_zeroth_parts.len D u w (product_first_zeroth_parts.Sram D u w) (product_first_zeroth_parts.Nlam D u w) = n ∧
      (n : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * (D.R.m * D.duS u * ∑ v ∈ product_first_zeroth_parts.VV D u w,
        ((product_first_zeroth_parts.amax D u : ℝ) / D.R.k + 2 * product_first_zeroth_parts.Wt D u ((D.fm u).tauOf w v) + D.R.k +
          (D.fm u).bTop ((D.fm u).tauOf w v))))

def MiddleClause (C : ℝ) : Prop :=
  ∀ w, product_first_zeroth_parts.OverT D u w →
    ∃ e : ℕ, (e : ℝ) ≤ D.R.m * (4 * ∑ τ, (product_first_zeroth_parts.Wt D u τ : ℝ) + C * D.R.f * D.R.N D.R.m) +
        ∑ v ∈ product_first_zeroth_parts.VV D u w, ((D.R.t : ℝ) + 1 + 2 * product_first_zeroth_parts.Wt D u ((D.fm u).tauOf w v) + C * D.R.N D.R.m) *
          ((D.R.m : ℝ) * (D.R.m + 1) / 2) ∧
      product_first_zeroth_parts.Into D u w (fun φ => product_first_zeroth_parts.tpow D u e • product_first_zeroth_parts.colT D u φ) (product_first_zeroth_parts.Nlam D u w) ((D.fm u).S D.R.m w)

theorem aux_iff_lattice_length_bound_and_kernel_clause (C : ℝ) : product_first_zeroth_parts.Conclusion5 D u C ↔ OuterClauses D u ∧ MiddleClause D u C :=
  ⟨fun h => ⟨fun w hw => ⟨(h w hw).1, (h w hw).2.2⟩, fun w hw => (h w hw).2.1⟩,
    fun h w hw => ⟨(h.1 w hw).1, h.2 w hw, (h.1 w hw).2⟩⟩

theorem outerClauses_iff : OuterClauses D u ↔ IndexWith D u (boundMax_vp D u) := by
  unfold OuterClauses IndexWith boundMax_vp
  rw [rankAll_eq]
  rfl

theorem indexAtLevelQuoted_iff : IndexAtLevelKnown D u ↔ IndexWith D u (boundQuoted_vp D u) := Iff.rfl

theorem indexAtLevel_iff : IndexAtLevel D u ↔ TopsStable D u ∧ IndexWith D u (boundFine_vp D u) := by
  classical
  constructor
  · intro h
    refine ⟨fun w hw v hv => ?_, fun w hw => ?_⟩
    · obtain ⟨-, g, n, l, hg, -⟩ := h w hw
      exact (exists_isScaledU_iff D u w v).1 ⟨g v, (hg v hv).1⟩
    · obtain ⟨h1, g, n, l, -, hl, -, h3, -⟩ := h w hw
      exact ⟨h1, l, hl, h3⟩
  · rintro ⟨hs, h⟩ w hw
    obtain ⟨h1, l, hl, h3⟩ := h w hw
    have hex : ∀ v, ∃ g : Module.End D.what₂.LL (D.fm u).ramSub, v ∈ LT.VVT D u w → IsScaledU D u w v g := by
      intro v
      by_cases hv : v ∈ LT.VVT D u w
      · obtain ⟨g, hg⟩ := (exists_isScaledU_iff D u w v).2 (hs w hw v hv)
        exact ⟨g, fun _ => hg⟩
      · exact ⟨0, fun h => absurd h hv⟩
    choose g hg using hex
    obtain ⟨n, hn, hsum⟩ := index_eq_sum_val_det D u w g hg h1 l hl
    exact ⟨h1, g, n, l, fun v hv => ⟨hg v hv, hn v hv⟩, hl, hsum, h3, boundFine_le_boundCoarse D u w⟩

theorem IndexWith.mono {D : D7} {u : D.what₂.Word} {bd bd' : D.what₂.places.Pl → ℝ} (h : IndexWith D u bd)
    (hb : ∀ w, bd w ≤ bd' w) : IndexWith D u bd' := by
  intro w hw
  obtain ⟨h1, l, hl, h3⟩ := h w hw
  exact ⟨h1, l, hl, h3.trans (mul_le_mul_of_nonneg_left (hb w) (Nat.cast_nonneg _))⟩

theorem tauOf_mem_tops {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {v : (D.mem u).A.vT}
    (hv : v ∈ LT.VVT D u w) : (D.fm u).tauOf w v ∈ topsOf D.host D.eTau := by
  unfold LT.VVT at hv
  split_ifs at hv
  · simpa using hv
  · simp at hv

theorem aTop_le_amax {τ : D.what₂.Tau} (h : τ ∈ topsOf D.host D.eTau) : (D.fm u).aTop τ ≤ product_first_zeroth_parts.amax D u :=
  (Finset.le_fold_max _).2 (Or.inr ⟨τ, h, le_rfl⟩)

theorem natAbs_bTop_le (τ : D.what₂.Tau) : ((D.fm u).bTop τ).natAbs ≤ Wtau D u τ := by
  have hk : 3 ≤ D.R.N 0 := by have := D.R.m_add_three_le_k; rw [Ranks.N_zero]; omega
  unfold Wtau
  refine le_trans ?_ (Finset.le_sup (Finset.mem_range.2 (Nat.succ_pos D.R.m)))
  refine le_trans ?_ (Finset.le_sup (Finset.mem_univ (⟨D.R.N 0 - 1, by omega⟩ : Fin (D.R.N 0))))
  rw [if_neg (by rintro ⟨h, -⟩; simp only at h; omega)]
  simp [MemberForms.bTop, DomWeight.detShift, D.R.N_pos 0]

theorem boundMax_sub_boundQuoted (w : D.what₂.places.Pl) :
    boundMax_vp D u w - boundQuoted_vp D u w = (D.R.m : ℝ) * (rankAll D u : ℝ) * ∑ v ∈ LT.VVT D u w,
      ((product_first_zeroth_parts.amax D u : ℝ) - ((D.fm u).aTop ((D.fm u).tauOf w v) : ℝ)) / D.R.k := by
  unfold boundMax_vp boundQuoted_vp topSize
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun v _ => by ring

theorem boundQuoted_sub_boundCoarse (w : D.what₂.places.Pl) :
    boundQuoted_vp D u w - boundCoarse_vp D u w = (D.R.m : ℝ) * (rankAll D u : ℝ) * ∑ v ∈ LT.VVT D u w,
      (((D.fm u).bTop ((D.fm u).tauOf w v) : ℝ) + 1) := by
  unfold boundQuoted_vp boundCoarse_vp
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun v _ => by ring

theorem boundQuoted_le_boundMax (w : D.what₂.places.Pl) : boundQuoted_vp D u w ≤ boundMax_vp D u w := by
  rw [← sub_nonneg, boundMax_sub_boundQuoted]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun v hv => div_nonneg (sub_nonneg.2 ?_) (Nat.cast_nonneg _))
  exact_mod_cast aTop_le_amax D u (tauOf_mem_tops hv)

theorem boundQuoted_eq_boundMax (h : ∀ τ ∈ topsOf D.host D.eTau, (D.fm u).aTop τ = product_first_zeroth_parts.amax D u)
    (w : D.what₂.places.Pl) : boundQuoted_vp D u w = boundMax_vp D u w := by
  symm
  rw [← sub_eq_zero, boundMax_sub_boundQuoted, Finset.sum_eq_zero, mul_zero]
  intro v hv
  rw [h _ (tauOf_mem_tops hv), sub_self, zero_div]

theorem boundCoarse_le_boundQuoted (hb : ∀ τ ∈ topsOf D.host D.eTau, 0 ≤ (D.fm u).bTop τ)
    (w : D.what₂.places.Pl) : boundCoarse_vp D u w ≤ boundQuoted_vp D u w := by
  rw [← sub_nonneg, boundQuoted_sub_boundCoarse]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun v hv => ?_)
  have : (0 : ℝ) ≤ ((D.fm u).bTop ((D.fm u).tauOf w v) : ℝ) := by exact_mod_cast hb _ (tauOf_mem_tops hv)
  linarith

theorem boundMax_le_boundPrice (w : D.what₂.places.Pl) : boundMax_vp D u w ≤ boundPrice_vp D u w := by
  unfold boundMax_vp boundPrice_vp
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => ?_) (by positivity)
  have h1 : (D.fm u).bTop ((D.fm u).tauOf w v) ≤ (Wtau D u ((D.fm u).tauOf w v) : ℤ) :=
    Int.le_natAbs.trans (by exact_mod_cast natAbs_bTop_le D u _)
  have h2 : ((D.fm u).bTop ((D.fm u).tauOf w v) : ℝ) ≤ (Wtau D u ((D.fm u).tauOf w v) : ℝ) := by exact_mod_cast h1
  linarith

theorem boundFine_le_boundMax (hS : product_first_zeroth_parts.HidaSetting D u) (w : D.what₂.places.Pl) :
    boundFine_vp D u w ≤ boundMax_vp D u w :=
  (boundFine_le_boundCoarse D u w).trans
    ((boundCoarse_le_boundQuoted D u hS.2.2 w).trans (boundQuoted_le_boundMax D u w))

theorem tops_stable_of_level_index (h : product_first_zeroth_parts.Conclusion1 D u) : TopsStable D u :=
  fun _ _ v _ x hx => (h.2.2.2.2.2.2.1 v x hx).1

theorem outerClauses_of_indexAtLevel (hS : product_first_zeroth_parts.HidaSetting D u) (h : IndexAtLevel D u) : OuterClauses D u :=
  (outerClauses_iff D u).2 (((indexAtLevel_iff D u).1 h).2.mono (boundFine_le_boundMax D u hS))

theorem outerClauses_of_indexAtLevel₂ (h : IndexAtLevelKnown D u) : OuterClauses D u :=
  (outerClauses_iff D u).2 (((indexAtLevelQuoted_iff D u).1 h).mono (boundQuoted_le_boundMax D u))

theorem indexAtLevelQuoted_iff_outerClauses (h : ∀ τ ∈ topsOf D.host D.eTau, (D.fm u).aTop τ = product_first_zeroth_parts.amax D u) :
    IndexAtLevelKnown D u ↔ OuterClauses D u := by
  rw [outerClauses_iff, indexAtLevelQuoted_iff, funext (boundQuoted_eq_boundMax D u h)]

theorem price_of_outerClauses (h : OuterClauses D u) : IndexWith D u (boundPrice_vp D u) :=
  ((outerClauses_iff D u).1 h).mono (boundMax_le_boundPrice D u)

theorem indexAtLevel_iff_outerClauses_and (hS : product_first_zeroth_parts.HidaSetting D u) :
    IndexAtLevel D u ↔ OuterClauses D u ∧ TopsStable D u ∧
      ∀ w, product_first_zeroth_parts.OverT D u w → ∀ l : ℕ, product_first_zeroth_parts.len D u w (product_first_zeroth_parts.Sram D u w) (product_first_zeroth_parts.Nlam D u w) = l →
        (l : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * boundFine_vp D u w := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (indexAtLevel_iff D u).1 h
    refine ⟨outerClauses_of_indexAtLevel D u hS h, h1, fun w hw l hl => ?_⟩
    obtain ⟨-, l', hl', h3⟩ := h2 w hw
    have : l = l' := by exact_mod_cast (hl.symm.trans hl' : (l : ℕ∞) = l')
    exact this ▸ h3
  · rintro ⟨h1, h2, h3⟩
    refine (indexAtLevel_iff D u).2 ⟨h2, fun w hw => ?_⟩
    obtain ⟨h4, l, hl, -⟩ := h1 w hw
    exact ⟨h4, l, hl, h3 w hw l hl⟩

theorem outerClauses_of_fam {eps : ℝ} (Fm : FamP eps) (h : IndexAtLevelFam Fm) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), (Fm.L x i).TuGe →
      product_first_zeroth_parts.HidaSetting (Fm.D x i) u → OuterClauses (Fm.D x i) u := by
  obtain ⟨x0, h⟩ := h
  refine ⟨max x0 (Fm.x1 + 1), fun x hx i u hT hS => outerClauses_of_indexAtLevel _ u hS
    (h x ((le_max_left _ _).trans hx) ?_ i hT u)⟩
  have := (le_max_right _ _).trans hx
  linarith

theorem compare :
    (∀ C, product_first_zeroth_parts.Conclusion5 D u C ↔ IndexWith D u (boundMax_vp D u) ∧ MiddleClause D u C) ∧
    (OuterClauses D u ↔ IndexWith D u (boundMax_vp D u)) ∧
    (IndexAtLevelKnown D u ↔ IndexWith D u (boundQuoted_vp D u)) ∧
    (IndexAtLevel D u ↔ TopsStable D u ∧ IndexWith D u (boundFine_vp D u)) ∧
    (product_first_zeroth_parts.Conclusion1 D u → TopsStable D u) ∧
    (∀ w, boundFine_vp D u w ≤ boundCoarse_vp D u w ∧
      (product_first_zeroth_parts.HidaSetting D u → boundCoarse_vp D u w ≤ boundQuoted_vp D u w) ∧
      boundQuoted_vp D u w ≤ boundMax_vp D u w ∧ boundMax_vp D u w ≤ boundPrice_vp D u w) ∧
    (product_first_zeroth_parts.HidaSetting D u → IndexAtLevel D u → OuterClauses D u) ∧
    (IndexAtLevelKnown D u → OuterClauses D u) ∧
    ((∀ τ ∈ topsOf D.host D.eTau, (D.fm u).aTop τ = product_first_zeroth_parts.amax D u) →
      (IndexAtLevelKnown D u ↔ OuterClauses D u)) :=
  ⟨fun C => by rw [aux_iff_lattice_length_bound_and_kernel_clause, outerClauses_iff], outerClauses_iff D u, indexAtLevelQuoted_iff D u, indexAtLevel_iff D u,
    tops_stable_of_level_index D u,
    fun w => ⟨boundFine_le_boundCoarse D u w, fun hS => boundCoarse_le_boundQuoted D u hS.2.2 w,
      boundQuoted_le_boundMax D u w, boundMax_le_boundPrice D u w⟩,
    outerClauses_of_indexAtLevel D u, outerClauses_of_indexAtLevel₂ D u, indexAtLevelQuoted_iff_outerClauses D u⟩

end GlobalTheory.LevelIndexCompare

end

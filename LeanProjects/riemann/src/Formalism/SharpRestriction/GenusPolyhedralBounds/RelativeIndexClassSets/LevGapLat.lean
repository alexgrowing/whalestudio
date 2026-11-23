import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts

noncomputable section

namespace Formalism.MainNotions.Gaps.LevGap

open NumberField Formalism.UG Formalism.BasicNotions

section General

variable {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] [DecidableEq n]

def diagMap (a : n → E) : (n → 𝓞 E) →ₗ[𝓞 E] (n → E) where
  toFun x := fun i => a i * (x i : E)
  map_add' x y := by
    funext i
    simp [mul_add]
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def]
    ring

@[simp] theorem diagMap_apply (a : n → E) (x : n → 𝓞 E) (i : n) :
    diagMap a x i = a i * (x i : E) := rfl

theorem diagMap_injective {a : n → E} (ha : ∀ i, a i ≠ 0) : Function.Injective (diagMap a) := by
  intro x y h
  funext i
  have h1 := congrFun h i
  simp only [diagMap_apply] at h1
  exact RingOfIntegers.ext (mul_left_cancel₀ (ha i) h1)

def diagLat (a : n → E) : Submodule (𝓞 E) (n → E) := LinearMap.range (diagMap a)

theorem mem_diagLat {a : n → E} {x : n → E} :
    x ∈ diagLat a ↔ ∀ i, ∃ c : 𝓞 E, x i = a i * (c : E) := by
  constructor
  · rintro ⟨c, rfl⟩ i
    exact ⟨c i, rfl⟩
  · intro h
    choose c hc using h
    exact ⟨c, funext fun i => (hc i).symm⟩

theorem single_mem_diagLat (a : n → E) (i : n) : Pi.single i (a i) ∈ diagLat a := by
  refine mem_diagLat.2 fun j => ?_
  by_cases h : j = i
  · subst h
    exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h]⟩

theorem diagLat_eq_span (a : n → E) :
    diagLat a = Submodule.span (𝓞 E) (Set.range fun i => (Pi.single i (a i) : n → E)) := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    have h : diagMap a c = ∑ i, c i • (Pi.single i (a i) : n → E) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp [Algebra.smul_def, mul_comm]
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb.symm]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact single_mem_diagLat a i

theorem diagLat_finite (a : n → E) : Module.Finite (𝓞 E) (diagLat a) :=
  Module.Finite.range (diagMap a)

theorem diagLat_span {a : n → E} (ha : ∀ i, a i ≠ 0) :
    Submodule.span E (diagLat a : Set (n → E)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun E n).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have h : (Pi.basisFun E n) i = (a i)⁻¹ • (Pi.single i (a i) : n → E) := by
    rw [Pi.basisFun_apply, ← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ (ha i)]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_diagLat a i))

theorem hform_one (σ : E →+* E) (x y : n → E) : hform σ 1 x y = ∑ i, σ (x i) * y i := by
  unfold hform
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Matrix.one_apply_ne hj.symm]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

variable (σ : E →+* E)

theorem map_int_mem (c : 𝓞 E) : σ (c : E) ∈ (algebraMap (𝓞 E) E).range :=
  ⟨RingOfIntegers.mapRingHom σ c, rfl⟩

theorem mem_dualSet_diagLat {a : n → E} {y : n → E} :
    y ∈ dualSet σ 1 (diagLat a) ↔ ∀ i, σ (a i) * y i ∈ (algebraMap (𝓞 E) E).range := by
  constructor
  · intro h i
    have h1 := h _ (single_mem_diagLat a i)
    rw [hform_one, Finset.sum_eq_single i] at h1
    · simpa using h1
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · rintro h _ ⟨c, rfl⟩
    rw [hform_one]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [diagMap_apply, map_mul, mul_right_comm]
    exact Subring.mul_mem _ (h i) (map_int_mem σ (c i))

theorem dualSet_diagLat {a : n → E} (ha : ∀ i, a i ≠ 0) :
    dualSet σ 1 (diagLat a) = (diagLat fun i => (σ (a i))⁻¹ : Set (n → E)) := by
  ext y
  rw [mem_dualSet_diagLat σ, SetLike.mem_coe, mem_diagLat]
  refine forall_congr' fun i => ?_
  have h0 : σ (a i) ≠ 0 := (map_ne_zero σ).2 (ha i)
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [RingOfIntegers.coe_eq_algebraMap, hc]; field_simp⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, RingOfIntegers.coe_eq_algebraMap]; field_simp⟩

theorem relIndex_diagLat {b : n → E} (hb : ∀ i, b i ≠ 0) (c : n → 𝓞 E) :
    (diagLat fun i => b i * (c i : E)).toAddSubgroup.relIndex (diagLat b).toAddSubgroup =
      ∏ i, Ideal.absNorm (Ideal.span {c i}) := by
  have h1 : (diagLat b).toAddSubgroup = (⊤ : AddSubgroup (n → 𝓞 E)).map (diagMap b).toAddMonoidHom := by
    ext x
    simp [diagLat, LinearMap.mem_range]
  have h2 : (diagLat fun i => b i * (c i : E)).toAddSubgroup.comap (diagMap b).toAddMonoidHom =
      (Submodule.pi Set.univ fun i => Ideal.span {c i}).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, mem_diagLat, Submodule.mem_pi,
      Set.mem_univ, true_implies, Ideal.mem_span_singleton', LinearMap.toAddMonoidHom_coe,
      diagMap_apply]
    refine forall_congr' fun i => ?_
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨u, RingOfIntegers.ext ?_⟩
      rw [mul_assoc] at hu
      rw [RingOfIntegers.coe_eq_algebraMap, map_mul, mul_comm]
      exact (mul_left_cancel₀ (hb i) hu).symm
    · rintro ⟨u, hu⟩
      exact ⟨u, by rw [← hu, RingOfIntegers.coe_eq_algebraMap, map_mul]; ring⟩
  rw [h1, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right, h2]
  change Submodule.cardQuot _ = _
  rw [Submodule.cardQuot_apply, Nat.card_congr (Submodule.quotientPi _).toEquiv, Nat.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

end General

section LatT

variable {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] [DecidableEq n]

def vecAt (i0 : n) (z : E) : n → E := Function.update (fun _ => (1 : E)) i0 z

@[simp] theorem vecAt_same (i0 : n) (z : E) : vecAt i0 z i0 = z := Function.update_self ..

theorem vecAt_ne {i0 i : n} (h : i ≠ i0) (z : E) : vecAt i0 z i = 1 :=
  Function.update_of_ne h ..

theorem vecAt_ne_zero {i0 : n} {z : E} (hz : z ≠ 0) (i : n) : vecAt i0 z i ≠ 0 := by
  by_cases h : i = i0
  · subst h
    simpa using hz
  · rw [vecAt_ne h]
    exact one_ne_zero

def latT (i0 : n) (pz : 𝓞 E) : Submodule (𝓞 E) (n → E) := diagLat (vecAt i0 (pz : E))

theorem mem_latT {i0 : n} {pz : 𝓞 E} {x : n → E} :
    x ∈ latT i0 pz ↔ (∃ c : 𝓞 E, x i0 = (pz : E) * (c : E)) ∧
      ∀ i, i ≠ i0 → x i ∈ (algebraMap (𝓞 E) E).range := by
  rw [latT, mem_diagLat]
  constructor
  · intro h
    refine ⟨by simpa using h i0, fun i hi => ?_⟩
    obtain ⟨c, hc⟩ := h i
    exact ⟨c, by rw [hc, vecAt_ne hi, one_mul]⟩
  · rintro ⟨h0, h1⟩ i
    by_cases hi : i = i0
    · subst hi
      simpa using h0
    · obtain ⟨c, hc⟩ := h1 i hi
      exact ⟨c, by rw [vecAt_ne hi, one_mul, ← hc]⟩

theorem latT_eq_span (i0 : n) (pz : 𝓞 E) :
    latT i0 pz = Submodule.span (𝓞 E)
      (Set.range fun i => (Pi.single i (vecAt i0 (pz : E) i) : n → E)) :=
  diagLat_eq_span _

theorem latT_finite (i0 : n) (pz : 𝓞 E) : Module.Finite (𝓞 E) (latT i0 pz) := diagLat_finite _

variable (σ : E →+* E) {i0 : n} {pz : 𝓞 E} {T : ℕ}

theorem pz_ne_zero (hT : T ≠ 0) (hpz : (pz : E) * σ (pz : E) = (T : E)) : (pz : E) ≠ 0 := by
  intro h
  rw [h, zero_mul] at hpz
  exact hT (by exact_mod_cast hpz.symm)

theorem latT_span (hz : (pz : E) ≠ 0) :
    Submodule.span E (latT i0 pz : Set (n → E)) = ⊤ := diagLat_span (vecAt_ne_zero hz)

theorem mem_dualSet_latT {y : n → E} :
    y ∈ dualSet σ 1 (latT i0 pz) ↔ σ (pz : E) * y i0 ∈ (algebraMap (𝓞 E) E).range ∧
      ∀ i, i ≠ i0 → y i ∈ (algebraMap (𝓞 E) E).range := by
  rw [latT, mem_dualSet_diagLat]
  constructor
  · intro h
    refine ⟨by simpa using h i0, fun i hi => ?_⟩
    simpa [vecAt_ne hi] using h i
  · rintro ⟨h0, h1⟩ i
    by_cases hi : i = i0
    · subst hi
      simpa using h0
    · simpa [vecAt_ne hi] using h1 i hi

theorem dualSet_latT (hz : (pz : E) ≠ 0) :
    dualSet σ 1 (latT i0 pz) = (diagLat (vecAt i0 (σ (pz : E))⁻¹) : Set (n → E)) := by
  rw [latT, dualSet_diagLat σ (vecAt_ne_zero hz)]
  congr 2
  funext i
  by_cases hi : i = i0
  · subst hi
    simp
  · simp [vecAt_ne hi]

theorem span_dualSet_latT (hz : (pz : E) ≠ 0) :
    Submodule.span (𝓞 E) (dualSet σ 1 (latT i0 pz)) = diagLat (vecAt i0 (σ (pz : E))⁻¹) := by
  rw [dualSet_latT σ hz, Submodule.span_eq]

theorem latT_int (hpz : (pz : E) * σ (pz : E) = (T : E)) :
    ∀ x ∈ latT i0 pz, x ∈ dualSet σ 1 (latT i0 pz) := by
  intro x hx
  obtain ⟨⟨c, hc⟩, h1⟩ := mem_latT.1 hx
  refine (mem_dualSet_latT σ).2 ⟨⟨(T : 𝓞 E) * c, ?_⟩, h1⟩
  rw [hc, map_mul, map_natCast, ← hpz]
  ring

theorem latT_dual (hpz : (pz : E) * σ (pz : E) = (T : E)) :
    ∀ y ∈ dualSet σ 1 (latT i0 pz), (T : E) • y ∈ latT i0 pz := by
  intro y hy
  obtain ⟨⟨c, hc⟩, h1⟩ := (mem_dualSet_latT σ).1 hy
  refine mem_latT.2 ⟨⟨c, ?_⟩, fun i hi => ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap c, hc, ← hpz]
    ring
  · obtain ⟨d, hd⟩ := h1 i hi
    exact ⟨(T : 𝓞 E) * d, by rw [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, hd]⟩

theorem latT_index (hT : T ≠ 0) (hpz : (pz : E) * σ (pz : E) = (T : E)) :
    (latT i0 pz).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (dualSet σ 1 (latT i0 pz))).toAddSubgroup =
        T ^ Module.finrank ℚ E := by
  have hz := pz_ne_zero σ hT hpz
  have hs : σ (pz : E) ≠ 0 := (map_ne_zero σ).2 hz
  have h1 : latT i0 pz = diagLat fun i => vecAt i0 (σ (pz : E))⁻¹ i *
      ((Function.update (fun _ => (1 : 𝓞 E)) i0 (T : 𝓞 E) i : 𝓞 E) : E) := by
    rw [latT]
    congr 1
    funext i
    by_cases hi : i = i0
    · subst hi
      rw [vecAt_same, vecAt_same, Function.update_self, RingOfIntegers.coe_eq_algebraMap,
        RingOfIntegers.coe_eq_algebraMap, map_natCast, ← hpz]
      field_simp
    · rw [vecAt_ne hi, vecAt_ne hi, Function.update_of_ne hi, RingOfIntegers.coe_eq_algebraMap,
        map_one, one_mul]
  rw [span_dualSet_latT σ hz]
  conv_lhs => rw [h1]
  rw [relIndex_diagLat (vecAt_ne_zero (inv_ne_zero hs)), Finset.prod_eq_single i0]
  · rw [Function.update_self, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  · intro j _ hj
    rw [Function.update_of_ne hj, Ideal.span_singleton_one, Ideal.absNorm_top]
  · intro hi
    exact absurd (Finset.mem_univ i0) hi

end LatT

section Bridge

open Formalism.MainNotions.Gaps.LG

variable {E : Type} [Field E] [NumberField E]

theorem LbOf_eq_latT {k : ℕ} (hk : 0 < k) (pz : 𝓞 E) : LbOf k pz = latT (⟨0, hk⟩ : Fin k) pz := by
  rw [latT_eq_span, LbOf]
  congr 2
  funext i
  unfold lbVec
  congr 1
  by_cases hi : i = ⟨0, hk⟩
  · subst hi
    simp
  · have h0 : ¬ (i.1 = 0) := fun h => hi (Fin.ext h)
    rw [if_neg h0, vecAt_ne hi]

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

theorem lbOK_of {k : ℕ} (hk : 0 < k) (P : Par F E k) (hJ : P.J = 1) (hT : P.T ≠ 0)
    (hpz : (P.pz : E) * P.σ (P.pz : E) = (P.T : E)) : P.LbOK (Module.finrank ℚ E) := by
  have hL : P.Lb = latT (⟨0, hk⟩ : Fin k) P.pz := LbOf_eq_latT hk P.pz
  have hpz' : (P.pz : E) * (P.σ : E →+* E) (P.pz : E) = (P.T : E) := hpz
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hL]
    exact latT_finite _ _
  · rw [hL]
    exact latT_span (pz_ne_zero _ hT hpz')
  · rw [hL, hJ]
    exact latT_int _ hpz'
  · rw [hL, hJ]
    exact latT_dual _ hpz'
  · rw [Par.Ld, hL, hJ]
    exact latT_index _ hT hpz'

theorem mem_dualSet_Lb {k : ℕ} (hk : 0 < k) (P : Par F E k) (hJ : P.J = 1) {y : Fin k → E} :
    y ∈ dualSet (P.σ : E →+* E) P.J P.Lb ↔
      P.σ (P.pz : E) * y ⟨0, hk⟩ ∈ (algebraMap (𝓞 E) E).range ∧
        ∀ i : Fin k, i ≠ ⟨0, hk⟩ → y i ∈ (algebraMap (𝓞 E) E).range := by
  have hL : P.Lb = latT (⟨0, hk⟩ : Fin k) P.pz := LbOf_eq_latT hk P.pz
  rw [hL, hJ]
  exact mem_dualSet_latT _

theorem Ld_eq {k : ℕ} (hk : 0 < k) (P : Par F E k) (hJ : P.J = 1) (hz : (P.pz : E) ≠ 0) :
    P.Ld = diagLat (vecAt (⟨0, hk⟩ : Fin k) (P.σ (P.pz : E))⁻¹) := by
  have hL : P.Lb = latT (⟨0, hk⟩ : Fin k) P.pz := LbOf_eq_latT hk P.pz
  rw [Par.Ld, hL, hJ]
  exact span_dualSet_latT _ hz

end Bridge

section Record

open Formalism.MainNotions.Gaps.LG

theorem finrank_hostE_eq {R : Ranks} (H : Host R) : Module.finrank ℚ H.E = 2 * R.f := by
  rw [H.finrank_cmField, Ranks.f, Ranks.n]
  ring

theorem k_pos (R : Ranks) : 0 < R.k := by
  have := R.m_add_three_le_k
  omega

theorem factLb : FactLb := by
  intro R H T pz piG h
  rw [← finrank_hostE_eq H]
  exact lbOK_of (k_pos R) (hostPar H T pz piG) rfl h.T_prime.ne_zero h.pz_norm

end Record

end Formalism.MainNotions.Gaps.LevGap

end

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitMeasureFiniteCompactSupport
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta.ProdSum

open GlobalTheory.CompanionTheory.ThetaUnits

theorem unQ_eq_ordShell (v : Pl) : unQ v = ordShell (Qv v) 0 := by
  ext a
  rw [ordShell_zero, SetLike.mem_coe, mem_unitFiltrationUnits_zero_iff]
  have h3 : ValuativeRel.valuation (Qv v) (a : Qv v) *
      ValuativeRel.valuation (Qv v) ((a⁻¹ : (Qv v)ˣ) : Qv v) = 1 := by
    rw [← map_mul]; simp
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : ValuativeRel.valuation (Qv v) (a : Qv v) ≤ 1 := h1
    have h2' : ValuativeRel.valuation (Qv v) ((a⁻¹ : (Qv v)ˣ) : Qv v) ≤ 1 := h2
    refine le_antisymm h1' ?_
    calc (1 : _) = ValuativeRel.valuation (Qv v) (a : Qv v) *
          ValuativeRel.valuation (Qv v) ((a⁻¹ : (Qv v)ˣ) : Qv v) := h3.symm
      _ ≤ ValuativeRel.valuation (Qv v) (a : Qv v) * 1 := by gcongr
      _ = _ := mul_one _
  · intro h
    rw [h, one_mul] at h3
    refine ⟨?_, ?_⟩
    · show ValuativeRel.valuation (Qv v) (a : Qv v) ≤ 1
      exact h.le
    · show ValuativeRel.valuation (Qv v) ((a⁻¹ : (Qv v)ˣ) : Qv v) ≤ 1
      exact h3.le

theorem one_mem_unQ (v : Pl) : (1 : (Qv v)ˣ) ∈ unQ v := by
  rw [unQ_eq_ordShell, ordShell_zero]
  exact one_mem _

theorem multHaar_unQ (v : Pl) : multHaar (Qv v) (unQ v) = 1 := by
  rw [unQ_eq_ordShell, multHaar_ordShell]

theorem setIntegral_unQ_of_invariant {v : Pl} {F : (Qv v)ˣ → ℂ}
    (h : ∀ x, ∀ e ∈ unQ v, F (x * e) = F x) (a : (Qv v)ˣ) :
    ∫ u in unQ v, F (a * u) ∂multHaar (Qv v) = F a := by
  rw [setIntegral_congr_fun (measurableSet_unQ v) (fun u hu => h a u hu), setIntegral_const,
    measureReal_def, multHaar_unQ]
  simp

theorem integral_eq_sum_shells {v : Pl} {F : (Qv v)ˣ → ℂ} (hm : Measurable F) {C : ℝ}
    (hC : ∀ x, ‖F x‖ ≤ C) (N : ℕ)
    (h0 : ∀ k : ℤ, (N : ℤ) < |k| → ∀ u ∈ unQ v, F (unifUnit (Qv v) ^ k * u) = 0) :
    ∫ x, F x ∂multHaar (Qv v) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N, ∫ u in unQ v, F (unifUnit (Qv v) ^ k * u) ∂multHaar (Qv v) := by
  have hshell : ∀ k : ℤ, ∫ u in ordShell (Qv v) k, F u ∂multHaar (Qv v) =
      ∫ u in unQ v, F (unifUnit (Qv v) ^ k * u) ∂multHaar (Qv v) := by
    intro k
    have := setIntegral_ordShell_mul F (unifUnit (Qv v) ^ k) 0
    rwa [ord_unifUnit_zpow, add_zero, ← unQ_eq_ordShell] at this
  have hzero : ∀ x : (Qv v)ˣ, (N : ℤ) < |ord (x : Qv v)| → F x = 0 := by
    intro x hx
    have hu : unifUnit (Qv v) ^ (-ord (x : Qv v)) * x ∈ unQ v := by
      rw [unQ_eq_ordShell, mem_ordShell, ord_units_mul, ord_unifUnit_zpow]
      omega
    have := h0 _ hx _ hu
    rwa [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul] at this
  set T : Set (Qv v)ˣ := ⋃ k ∈ Finset.Icc (-(N : ℤ)) N, ordShell (Qv v) k with hT
  have hTm : MeasurableSet T :=
    Finset.measurableSet_biUnion _ fun k _ => measurableSet_ordShell k
  have hTf : multHaar (Qv v) T ≠ ⊤ := by
    refine (measure_biUnion_lt_top (Finset.finite_toSet _) fun k _ => ?_).ne
    rw [multHaar_ordShell]
    exact ENNReal.one_lt_top
  have hind : T.indicator F = F := by
    funext x
    by_cases hx : x ∈ T
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx]
      refine (hzero x ?_).symm
      by_contra hle
      refine hx (Set.mem_biUnion (x := ord (x : Qv v)) ?_ rfl)
      rw [Finset.coe_Icc, Set.mem_Icc]
      exact abs_le.mp (not_lt.mp hle)
  have hint : Integrable F (multHaar (Qv v)) := by
    rw [← hind, integrable_indicator_iff hTm]
    exact Measure.integrableOn_of_bounded hTf hm.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  have hs := hasSum_setIntegral_ordShell hint
  have hs2 : HasSum (fun k : ℤ => ∫ u in ordShell (Qv v) k, F u ∂multHaar (Qv v))
      (∑ k ∈ Finset.Icc (-(N : ℤ)) N, ∫ u in ordShell (Qv v) k, F u ∂multHaar (Qv v)) :=
    hasSum_sum_of_ne_finset_zero (fun k hk => by
      rw [hshell]
      refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => h0 k ?_ u hu
      by_contra hle
      exact hk (Finset.mem_Icc.mpr (abs_le.mp (not_lt.mp hle))))
  rw [hs.unique hs2]
  exact Finset.sum_congr rfl fun k _ => hshell k

theorem hasSum_box {P : Type} (Sp : P → Prop) (B : Finset P) (A : P → Finset ℤ)
    (hA : ∀ v, ∀ k ∈ A v, k ≠ 0 → Sp v) (G : P → ℤ → ℂ)
    (a : {m : P →₀ ℤ // ∀ v, m v ≠ 0 → Sp v} → ℂ)
    (hin : ∀ m : {m : P →₀ ℤ // ∀ v, m v ≠ 0 → Sp v}, (∀ v ∉ B, m.1 v = 0) → (∀ v ∈ B, m.1 v ∈ A v) →
      a m = ∏ v ∈ B, G v (m.1 v))
    (hout : ∀ m : {m : P →₀ ℤ // ∀ v, m v ≠ 0 → Sp v}, ¬ ((∀ v ∉ B, m.1 v = 0) ∧ (∀ v ∈ B, m.1 v ∈ A v)) →
      a m = 0) :
    HasSum a (∏ v ∈ B, ∑ k ∈ A v, G v k) := by
  classical
  rw [Finset.prod_sum]
  let ext : (∀ v ∈ B, ℤ) → (P →₀ ℤ) := fun p =>
    Finsupp.onFinset B (fun v => if h : v ∈ B then p v h else 0) (fun v hv => by
      by_contra hB
      exact hv (dif_neg hB))
  have hext : ∀ p v (h : v ∈ B), ext p v = p v h := fun p v h => by
    simp [ext, h]
  have hext0 : ∀ p v, v ∉ B → ext p v = 0 := fun p v h => by
    simp [ext, h]
  have hmem : ∀ p : {p // p ∈ B.pi A}, ∀ v, ext p.1 v ≠ 0 → Sp v := by
    intro p v hv
    by_cases h : v ∈ B
    · rw [hext p.1 v h] at hv
      exact hA v _ (Finset.mem_pi.mp p.2 v h) hv
    · exact absurd (hext0 p.1 v h) hv
  let g : {p // p ∈ B.pi A} → {m : P →₀ ℤ // ∀ v, m v ≠ 0 → Sp v} := fun p => ⟨ext p.1, hmem p⟩
  have hg : Function.Injective g := by
    intro p q hpq
    apply Subtype.ext
    funext v h
    have := congrArg (fun m : {m : P →₀ ℤ // ∀ v, m v ≠ 0 → Sp v} => m.1 v) hpq
    simpa [g, hext _ v h] using this
  have hz : ∀ m ∉ Set.range g, a m = 0 := by
    intro m hm
    refine hout m fun ⟨h1, h2⟩ => hm ?_
    refine ⟨⟨fun v _ => m.1 v, Finset.mem_pi.mpr h2⟩, ?_⟩
    apply Subtype.ext
    ext v
    by_cases h : v ∈ B
    · exact hext _ v h
    · rw [show (g _).1 v = 0 from hext0 _ v h, h1 v h]
  refine (Function.Injective.hasSum_iff hg hz).mp ?_
  have hsum := hasSum_fintype (a ∘ g)
  convert hsum using 1
  rw [← Finset.sum_coe_sort (B.pi A)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Function.comp_apply, hin (g p) (fun v h => hext0 _ v h) (fun v h => by
    rw [show (g p).1 v = p.1 v h from hext _ v h]
    exact Finset.mem_pi.mp p.2 v h), ← Finset.prod_attach B]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [show (g p).1 x.1 = p.1 x.1 x.2 from hext _ _ x.2]

open Classical in

def gL (Sv : Finset Pl) (f : ∀ v : Pl, (Qv v)ˣ → ℂ) (v : Pl) (k : ℤ) : ℂ :=
  if v ∈ Sv then ∫ u in unQ v, f v (unifUnit (Qv v) ^ k * u) ∂multHaar (Qv v)
  else f v (unifUnit (Qv v) ^ k)

theorem tu_of_mem {Sv : Finset Pl} (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) {v : Pl} (h : v ∈ Sv) :
    tu Sv m u v = unifUnit (Qv v) ^ (m v) * u ⟨v, h⟩ := by
  simp [tu, h]

theorem tu_of_notMem {Sv : Finset Pl} (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) {v : Pl} (h : v ∉ Sv) :
    tu Sv m u v = unifUnit (Qv v) ^ (m v) := by
  simp [tu, h]

theorem mulSupport_subset {Sv B : Finset Pl} {f : ∀ v : Pl, (Qv v)ˣ → ℂ}
    (hB : ∀ v ∉ B, v ∉ Sv ∧ f v 1 = 1) (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) {s : Finset Pl}
    (hs : B ⊆ s) (hm : ∀ v ∉ s, m v = 0) :
    Function.mulSupport (fun v => f v (tu Sv m u v)) ⊆ s := by
  intro v hv
  by_contra h
  have hvB : v ∉ B := fun hb => h (hs hb)
  refine hv ?_
  show f v (tu Sv m u v) = 1
  rw [tu_of_notMem m u (hB v hvB).1, hm v h, zpow_zero]
  exact (hB v hvB).2

theorem integral_term {Sv B : Finset Pl} {f : ∀ v : Pl, (Qv v)ˣ → ℂ} (hSB : Sv ⊆ B)
    (hB : ∀ v ∉ B, v ∉ Sv ∧ f v 1 = 1) (m : Pl →₀ ℤ) (hm : ∀ v ∉ B, m v = 0) :
    ∫ u, ∏ᶠ v, f v (tu Sv m u v) ∂muU Sv = ∏ v ∈ B, gL Sv f v (m v) := by
  classical
  have e : ∀ u : ∀ v : Sv, (Qv v.1)ˣ, ∏ᶠ v, f v (tu Sv m u v) =
      (∏ v ∈ B \ Sv, f v (unifUnit (Qv v) ^ (m v))) *
        ∏ v : Sv, f v.1 (unifUnit (Qv v.1) ^ (m v.1) * u v) := by
    intro u
    rw [finprod_eq_prod_of_mulSupport_subset _ (mulSupport_subset hB m u subset_rfl hm),
      ← Finset.prod_sdiff hSB]
    congr 1
    · exact Finset.prod_congr rfl fun v hv => by rw [tu_of_notMem m u (Finset.mem_sdiff.mp hv).2]
    · rw [← Finset.prod_coe_sort Sv]
      exact Finset.prod_congr rfl fun v _ => by rw [tu_of_mem m u v.2]
  simp_rw [e]
  rw [integral_const_mul]
  unfold muU
  rw [integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun v : Sv => fun x : (Qv v.1)ˣ => f v.1 (unifUnit (Qv v.1) ^ (m v.1) * x)),
    ← Finset.prod_sdiff hSB]
  congr 1
  · exact Finset.prod_congr rfl fun v hv => by
      rw [gL, if_neg (Finset.mem_sdiff.mp hv).2]
  · rw [← Finset.prod_coe_sort Sv]
    exact Finset.prod_congr rfl fun v _ => by rw [gL, if_pos v.2]

theorem integral_term_zero_off {Sp : Pl → Prop} {Sv B : Finset Pl} {f : ∀ v : Pl, (Qv v)ˣ → ℂ}
    (hB : ∀ v ∉ B, v ∉ Sv ∧ f v 1 = 1 ∧ (Sp v → ∀ k : ℤ, k ≠ 0 → f v (unifUnit (Qv v) ^ k) = 0))
    (m : Pl →₀ ℤ) (hSp : ∀ v, m v ≠ 0 → Sp v) {v : Pl} (hv : v ∉ B) (hmv : m v ≠ 0) :
    ∫ u, ∏ᶠ v, f v (tu Sv m u v) ∂muU Sv = 0 := by
  classical
  have hz : ∀ u : ∀ v : Sv, (Qv v.1)ˣ, ∏ᶠ v, f v (tu Sv m u v) = 0 := by
    intro u
    refine finprod_eq_zero _ v ?_ ((B ∪ m.support).finite_toSet.subset
      (mulSupport_subset (fun v h => ⟨(hB v h).1, (hB v h).2.1⟩) m u Finset.subset_union_left ?_))
    · rw [tu_of_notMem m u (hB v hv).1]
      exact (hB v hv).2.2 (hSp v hmv) _ hmv
    · intro w hw
      by_contra h
      exact hw (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr h))
  simp_rw [hz]
  simp

theorem integral_term_zero_big {Sv B : Finset Pl} {f : ∀ v : Pl, (Qv v)ˣ → ℂ}
    (hB : ∀ v ∉ B, v ∉ Sv ∧ f v 1 = 1) (m : Pl →₀ ℤ) {v : Pl}
    (hv : ∀ u ∈ unQ v, f v (unifUnit (Qv v) ^ (m v) * u) = 0) :
    ∫ u, ∏ᶠ v, f v (tu Sv m u v) ∂muU Sv = 0 := by
  classical
  refine integral_eq_zero_of_ae ?_
  filter_upwards [(muU_finite_units Sv).2.1] with u hu
  refine finprod_eq_zero _ v ?_ ((B ∪ m.support).finite_toSet.subset
    (mulSupport_subset hB m u Finset.subset_union_left ?_))
  · by_cases h : v ∈ Sv
    · rw [tu_of_mem m u h]
      exact hv _ (hu ⟨v, h⟩)
    · rw [tu_of_notMem m u h]
      have := hv 1 (one_mem_unQ v)
      rwa [mul_one] at this
  · intro w hw
    by_contra h
    exact hw (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr h))

theorem hasSum_integral_finprod : ∀ (Sp : Pl → Prop) (Sv : Finset Pl) (f : ∀ v : Pl, (Qv v)ˣ → ℂ), (∀ v ∈ Sv, Sp v) → (∀ v, Measurable (f v)) →
  (∀ v, ∃ C : ℝ, ∀ x, ‖f v x‖ ≤ C) → (∀ v ∉ Sv, ∀ x, ∀ e ∈ unQ v, f v (x * e) = f v x) →
  (∃ B : Finset Pl, ∀ v ∉ B, v ∉ Sv ∧ f v 1 = 1 ∧ (Sp v → ∀ k : ℤ, k ≠ 0 → f v (unifUnit (Qv v) ^ k) = 0)) →
  (∀ v, Sp v → ∃ N : ℕ, ∀ k : ℤ, (N : ℤ) < |k| → ∀ u ∈ unQ v, f v (unifUnit (Qv v) ^ k * u) = 0) →
  (Function.mulSupport (locF Sp f)).Finite ∧
    HasSum (fun m : {m : Pl →₀ ℤ // ∀ v, m v ≠ 0 → Sp v} => ∫ u, ∏ᶠ v, f v (tu Sv m.1 u v) ∂muU Sv) (∏ᶠ v, locF Sp f v) := by
  classical
  rintro Sp Sv f h1 h2 h3 h4 ⟨B, hB⟩ h6
  have hSB : Sv ⊆ B := fun v hv => by
    by_contra h
    exact (hB v h).1 hv
  have hB' : ∀ v ∉ B, v ∉ Sv ∧ f v 1 = 1 := fun v h => ⟨(hB v h).1, (hB v h).2.1⟩
  choose! N hN using h6
  let A : Pl → Finset ℤ := fun v => if Sp v then Finset.Icc (-(N v : ℤ)) (N v) else {0}
  have hA0 : ∀ v, (0 : ℤ) ∈ A v := by
    intro v
    by_cases h : Sp v
    · simp [A, h]
    · simp [A, h]
  have hloc : ∀ v, ∑ k ∈ A v, gL Sv f v k = locF Sp f v := by
    intro v
    by_cases h : Sp v
    · obtain ⟨C, hC⟩ := h3 v
      simp only [A, locF, if_pos h]
      rw [integral_eq_sum_shells (h2 v) hC (N v) (hN v h)]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hs : v ∈ Sv
      · rw [gL, if_pos hs]
      · rw [gL, if_neg hs, setIntegral_unQ_of_invariant (h4 v hs)]
    · have hs : v ∉ Sv := fun hs => h (h1 v hs)
      simp [A, locF, h, gL, hs]
  have hone : ∀ v ∉ B, locF Sp f v = 1 := by
    intro v hv
    rw [← hloc v, Finset.sum_eq_single_of_mem 0 (hA0 v)]
    · simp [gL, (hB v hv).1, (hB v hv).2.1]
    · intro k hk hk0
      have hSpv : Sp v := by
        by_contra h
        simp [A, h] at hk
        exact hk0 hk
      simp [gL, (hB v hv).1, (hB v hv).2.2 hSpv k hk0]
  have hsupp : Function.mulSupport (locF Sp f) ⊆ B := by
    intro v hv
    by_contra h
    exact hv (hone v h)
  refine ⟨B.finite_toSet.subset hsupp, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp, ← Finset.prod_congr rfl fun v _ => hloc v]
  refine hasSum_box Sp B A ?_ (gL Sv f) _ ?_ ?_
  · intro v k hk hk0
    by_contra h
    simp [A, h] at hk
    exact hk0 hk
  · intro m hm _
    exact integral_term hSB hB' m.1 hm
  · intro m hm
    by_cases hoff : ∀ v ∉ B, m.1 v = 0
    · have hex : ∃ v ∈ B, m.1 v ∉ A v := by
        by_contra hc
        push Not at hc
        exact hm ⟨hoff, hc⟩
      obtain ⟨v, -, hv⟩ := hex
      have hSpv : Sp v := by
        by_contra h
        refine hv ?_
        have h0 : m.1 v = 0 := by
          by_contra h0
          exact h (m.2 v h0)
        rw [h0]
        exact hA0 v
      refine integral_term_zero_big hB' m.1 (v := v) (hN v hSpv _ ?_)
      by_contra hle
      refine hv ?_
      simp only [A, if_pos hSpv]
      exact Finset.mem_Icc.mpr (abs_le.mp (not_lt.mp hle))
    · push Not at hoff
      obtain ⟨v, hvB, hv⟩ := hoff
      exact integral_term_zero_off hB m.1 m.2 hvB hv

end GlobalTheory.CompanionTheory.FexTheta.ProdSum

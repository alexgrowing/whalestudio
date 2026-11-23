import Mathlib

open MeasureTheory
open scoped Pointwise ENNReal

namespace GlobalTheory.RowFubini

theorem relIndex_eq_of_le_of_cover {G : Type*} [Group G] (H s t : Subgroup G) (hst : s ≤ t)
    (hcov : ∀ g ∈ t, ∃ a ∈ s, a⁻¹ * g ∈ H) : H.relIndex s = H.relIndex t := by
  unfold Subgroup.relIndex Subgroup.index
  refine Nat.card_congr (Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE H hst)
    ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE H hst).injective, ?_⟩)
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨a, ha, hg⟩ := hcov g g.2
    refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
    rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa using hg

theorem relIndex_split {G Y : Type*} [Group G] [Group Y] (π : G →* Y) (A B : Subgroup G)
    (hBA : B ≤ A) :
    B.relIndex A = B.relIndex (A ⊓ π.ker) * (B.map π).relIndex (A.map π) := by
  set S := (B ⊔ π.ker) ⊓ A with hS
  have hBS : B ≤ S := le_inf le_sup_left hBA
  have hSA : S ≤ A := inf_le_right
  have h1 : B.relIndex A = B.relIndex S * S.relIndex A :=
    (Subgroup.relIndex_mul_relIndex B S A hBS hSA).symm
  have h2 : S.relIndex A = (B.map π).relIndex (A.map π) := by
    rw [Subgroup.relIndex_map_map, hS, Subgroup.inf_relIndex_right]
    refine relIndex_eq_of_le_of_cover _ _ _ le_sup_left ?_
    intro g hg
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hg
    obtain ⟨a, ha, n, hn, rfl⟩ := hg
    exact ⟨a, ha, by simpa using (le_sup_right : π.ker ≤ B ⊔ π.ker) hn⟩
  have h3 : B.relIndex S = B.relIndex (A ⊓ π.ker) := by
    refine (relIndex_eq_of_le_of_cover _ _ _ ?_ ?_).symm
    · exact le_inf (inf_le_right.trans le_sup_right) inf_le_left
    · intro g hg
      have hgA : g ∈ A := hg.2
      have hg1 : g ∈ π.ker ⊔ B := sup_comm B π.ker ▸ hg.1
      rw [← SetLike.mem_coe, Subgroup.normal_mul] at hg1
      obtain ⟨m, hm, b, hb, rfl⟩ := hg1
      refine ⟨m, ⟨?_, hm⟩, by simpa using hb⟩
      have : m = (m * b) * b⁻¹ := by group
      rw [this]
      exact A.mul_mem hgA (A.inv_mem (hBA hb))
  rw [h1, h2, h3]

end GlobalTheory.RowFubini

namespace GlobalTheory.RowFubini

section Meas

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]

theorem finiteIndex_subgroupOf (H L : Subgroup G) (hH : IsOpen (H : Set G))
    (hL : IsCompact (L : Set G)) : (H.subgroupOf L).FiniteIndex := by
  have : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have ho : IsOpen ((H.subgroupOf L : Subgroup L) : Set L) :=
    hH.preimage continuous_subtype_val
  have : Finite (L ⧸ H.subgroupOf L) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.finiteIndex_of_finite_quotient

theorem measure_eq_relIndex_mul (μ : Measure G) [μ.IsMulLeftInvariant] (H L : Subgroup G)
    (hHL : H ≤ L) (hH : IsOpen (H : Set G)) (hL : IsCompact (L : Set G)) :
    μ L = (H.relIndex L : ℝ≥0∞) * μ H := by
  have := finiteIndex_subgroupOf H L hH hL
  obtain ⟨s, hs, -⟩ := (H.subgroupOf L).exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  have hU : (⋃ a : s, (a.val : L) • (H : Set G)) = (L : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_smul_set, SetLike.mem_coe]
    constructor
    · rintro ⟨a, h, hh, rfl⟩
      exact L.mul_mem a.val.2 (hHL hh)
    · intro hx
      obtain ⟨⟨b, h⟩, hbh, -⟩ := hs.existsUnique ⟨x, hx⟩
      refine ⟨b, (h.val : G), Subgroup.mem_subgroupOf.mp h.2, ?_⟩
      have := congrArg Subtype.val hbh
      exact this
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => (a.val : L) • (H : Set G)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨h1, hh1, rfl⟩ ⟨h2, hh2, he⟩
    apply hab
    have hh1' : (⟨h1, hHL hh1⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh1
    have hh2' : (⟨h2, hHL hh2⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh2
    have e : (a.val : L) * ⟨h1, hHL hh1⟩ = (b.val : L) * ⟨h2, hHL hh2⟩ := Subtype.ext he.symm
    have := (hs.existsUnique ((a.val : L) * ⟨h1, hHL hh1⟩)).unique
      (y₁ := (a, ⟨_, hh1'⟩)) (y₂ := (b, ⟨_, hh2'⟩)) rfl e.symm
    exact congrArg Prod.fst this
  have hHm : MeasurableSet (H : Set G) := hH.measurableSet
  symm
  calc (H.relIndex L : ℝ≥0∞) * μ H = ∑' a : s, μ ((a.val : L) • (H : Set G)) := by
        simp [measure_smul, hs.encard_left, Subgroup.relIndex]
    _ = μ (⋃ a : s, (a.val : L) • (H : Set G)) :=
        (measure_iUnion hdisj fun a => hHm.const_smul _).symm
    _ = μ L := by rw [hU]

theorem measure_pos_lt_top (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (hc : IsCompact (H : Set G)) : 0 < μ H ∧ μ H < ∞ :=
  ⟨hH.measure_pos μ ⟨1, H.one_mem⟩, hc.measure_lt_top⟩

end Meas

end GlobalTheory.RowFubini

namespace GlobalTheory.RowFubini

section Top

variable {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]

theorem comap_open_compact (R Q : Subgroup X) (hR : IsClosed (R : Set X))
    (hQo : IsOpen (Q : Set X)) (hQc : IsCompact (Q : Set X)) :
    IsOpen ((Q.comap R.subtype : Subgroup R) : Set R) ∧
      IsCompact ((Q.comap R.subtype : Subgroup R) : Set R) :=
  ⟨hQo.preimage continuous_subtype_val, hR.isClosedEmbedding_subtypeVal.isCompact_preimage hQc⟩

theorem map_open_compact {Y : Type*} [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    (A : Subgroup X) (π : X →* Y) (σ : Y →* X) (hπ : Continuous π) (hσ : Continuous σ)
    (hsec : ∀ y, π (σ y) = y) (hAo : IsOpen (A : Set X)) (hAc : IsCompact (A : Set X)) :
    IsOpen ((A.map π : Subgroup Y) : Set Y) ∧ IsCompact ((A.map π : Subgroup Y) : Set Y) := by
  refine ⟨Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_, ?_⟩
  · refine Filter.mem_of_superset ((hAo.preimage hσ).mem_nhds ?_) ?_
    · simp [A.one_mem]
    · intro y hy
      exact Subgroup.mem_map.mpr ⟨σ y, hy, hsec y⟩
  · rw [Subgroup.coe_map]
    exact hAc.image hπ

def conjSub (K : Subgroup X) (b : X) : Subgroup X := K.comap (MulAut.conj b⁻¹).toMonoidHom

omit [TopologicalSpace X] [IsTopologicalGroup X] in
theorem mem_conjSub (K : Subgroup X) (b x : X) : x ∈ conjSub K b ↔ b⁻¹ * x * b ∈ K := by
  simp [conjSub]

theorem conjSub_open_compact (K : Subgroup X) (b : X) (hKo : IsOpen (K : Set X))
    (hKc : IsCompact (K : Set X)) :
    IsOpen (conjSub K b : Set X) ∧ IsCompact (conjSub K b : Set X) := by
  let h : X ≃ₜ X := (Homeomorph.mulLeft b⁻¹).trans (Homeomorph.mulRight b)
  have e : (conjSub K b : Set X) = h ⁻¹' (K : Set X) := by
    ext x; simp [h, mem_conjSub]
  rw [e]
  exact ⟨hKo.preimage h.continuous, h.isCompact_preimage.mpr hKc⟩

end Top

end GlobalTheory.RowFubini

namespace GlobalTheory.RowFubini

theorem cross_identity {X Y : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [MeasurableSpace X] [BorelSpace X]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    (R N : Subgroup X) (π : R →* Y) (σ : Y →* R)
    (hR : IsClosed (R : Set X)) (hN : IsClosed (N : Set X)) (hNR : N ≤ R)
    (hπ : Continuous π) (hσ : Continuous σ) (hsec : ∀ y, π (σ y) = y)
    (hker : ∀ r : R, π r = 1 ↔ r.1 ∈ N)
    (ρ : Measure R) [ρ.IsMulLeftInvariant] (la : Measure N) [la.IsMulLeftInvariant]
    (ν : Measure Y) [ν.IsMulLeftInvariant] (Q₁ Q₂ : Subgroup X) (h12 : Q₁ ≤ Q₂)
    (h1o : IsOpen (Q₁ : Set X)) (h1c : IsCompact (Q₁ : Set X))
    (h2o : IsOpen (Q₂ : Set X)) (h2c : IsCompact (Q₂ : Set X)) :
    ρ.real (Q₂.comap R.subtype) * la.real (Q₁.comap N.subtype) *
        ν.real ((Q₁.comap R.subtype).map π) =
      ρ.real (Q₁.comap R.subtype) * la.real (Q₂.comap N.subtype) *
        ν.real ((Q₂.comap R.subtype).map π) := by
  obtain ⟨a1o, a1c⟩ := comap_open_compact R Q₁ hR h1o h1c
  obtain ⟨a2o, a2c⟩ := comap_open_compact R Q₂ hR h2o h2c
  obtain ⟨n1o, -⟩ := comap_open_compact N Q₁ hN h1o h1c
  obtain ⟨-, n2c⟩ := comap_open_compact N Q₂ hN h2o h2c
  obtain ⟨p1o, -⟩ := map_open_compact _ π σ hπ hσ hsec a1o a1c
  obtain ⟨-, p2c⟩ := map_open_compact _ π σ hπ hσ hsec a2o a2c
  have hA : Q₁.comap R.subtype ≤ Q₂.comap R.subtype := Subgroup.comap_mono h12
  have ea := measure_eq_relIndex_mul ρ _ _ hA a1o a2c
  have en := measure_eq_relIndex_mul la _ _ (Subgroup.comap_mono h12) n1o n2c
  have ep := measure_eq_relIndex_mul ν _ _ (Subgroup.map_mono hA) p1o p2c
  have hmap : (Q₂.comap N.subtype).map (Subgroup.inclusion hNR) = Q₂.comap R.subtype ⊓ π.ker := by
    ext r
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨hn, (hker _).2 n.2⟩
    · rintro ⟨hq, hk⟩
      exact ⟨⟨r.1, (hker r).1 hk⟩, hq, rfl⟩
  have hidx : (Q₁.comap R.subtype).relIndex (Q₂.comap R.subtype ⊓ π.ker) =
      (Q₁.comap N.subtype).relIndex (Q₂.comap N.subtype) := by
    rw [← hmap, ← Subgroup.relIndex_comap]
    rfl
  have hs := relIndex_split π _ _ hA
  rw [hidx] at hs
  simp only [measureReal_def, ← ENNReal.toReal_mul]
  rw [ea, en, ep, hs]
  congr 1
  push_cast
  ring

theorem haar_trace_conj_eq : ∀ {X Y : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X] [BorelSpace X]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    (R N K : Subgroup X) (π : R →* Y) (σ : Y →* R),
    IsClosed (R : Set X) → IsClosed (N : Set X) → N ≤ R → IsOpen (K : Set X) → IsCompact (K : Set X) →
    Continuous π → Continuous σ → (∀ y, π (σ y) = y) → (∀ r : R, π r = 1 ↔ r.1 ∈ N) →
    ∀ ρ : Measure R, ρ.IsHaarMeasure →
    ∃ (κ : ℝ) (la : Measure N) (ν : Measure Y), 0 < κ ∧ la.IsHaarMeasure ∧ ν.IsHaarMeasure ∧ ∀ b : X,
      ρ.real {r : R | b⁻¹ * r.1 * b ∈ K} = κ * la.real {n : N | b⁻¹ * n.1 * b ∈ K} * ν.real (π '' {r : R | b⁻¹ * r.1 * b ∈ K}) := by
  intro X Y _ _ _ _ _ _ _ _ _ _ R N K π σ hR hN hNR hKo hKc hπ hσ hsec hker ρ hρ
  obtain ⟨aKo, aKc⟩ := comap_open_compact R K hR hKo hKc
  obtain ⟨nKo, nKc⟩ := comap_open_compact N K hN hKo hKc
  obtain ⟨pKo, pKc⟩ := map_open_compact _ π σ hπ hσ hsec aKo aKc
  let la : Measure N := Measure.haarMeasure ⟨⟨_, nKc⟩, by
    show (interior ((K.comap N.subtype : Subgroup N) : Set N)).Nonempty
    rw [nKo.interior_eq]; exact ⟨1, Subgroup.one_mem _⟩⟩
  let ν : Measure Y := Measure.haarMeasure ⟨⟨_, pKc⟩, by
    show (interior (((K.comap R.subtype).map π : Subgroup Y) : Set Y)).Nonempty
    rw [pKo.interior_eq]; exact ⟨1, Subgroup.one_mem _⟩⟩
  have hla : la.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hν : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have pos : ∀ Q : Subgroup X, IsOpen (Q : Set X) → IsCompact (Q : Set X) →
      0 < ρ.real (Q.comap R.subtype) ∧ 0 < la.real (Q.comap N.subtype) ∧
        0 < ν.real ((Q.comap R.subtype).map π) := by
    intro Q ho hc
    obtain ⟨ao, ac⟩ := comap_open_compact R Q hR ho hc
    obtain ⟨no, nc⟩ := comap_open_compact N Q hN ho hc
    obtain ⟨po, pc⟩ := map_open_compact _ π σ hπ hσ hsec ao ac
    obtain ⟨a1, a2⟩ := measure_pos_lt_top ρ _ ao ac
    obtain ⟨n1, n2⟩ := measure_pos_lt_top la _ no nc
    obtain ⟨p1, p2⟩ := measure_pos_lt_top ν _ po pc
    exact ⟨ENNReal.toReal_pos a1.ne' a2.ne, ENNReal.toReal_pos n1.ne' n2.ne,
      ENNReal.toReal_pos p1.ne' p2.ne⟩
  obtain ⟨aK, nK, pK⟩ := pos K hKo hKc
  refine ⟨ρ.real (K.comap R.subtype) /
    (la.real (K.comap N.subtype) * ν.real ((K.comap R.subtype).map π)), la, ν,
    div_pos aK (mul_pos nK pK), hla, hν, fun b => ?_⟩
  obtain ⟨hCo, hCc⟩ := conjSub_open_compact K b hKo hKc
  have hDo : IsOpen ((conjSub K b ⊓ K : Subgroup X) : Set X) := hCo.inter hKo
  have hDc : IsCompact ((conjSub K b ⊓ K : Subgroup X) : Set X) :=
    hCc.inter_right (K.isClosed_of_isOpen hKo)
  obtain ⟨-, nD, pD⟩ := pos _ hDo hDc
  have e1 := cross_identity R N π σ hR hN hNR hπ hσ hsec hker ρ la ν _ _ inf_le_left hDo hDc
    hCo hCc
  have e2 := cross_identity R N π σ hR hN hNR hπ hσ hsec hker ρ la ν _ _ inf_le_right hDo hDc
    hKo hKc
  have sR : {r : R | b⁻¹ * r.1 * b ∈ K} = ((conjSub K b).comap R.subtype : Subgroup R) := by
    ext r; exact (mem_conjSub K b r.1).symm
  have sN : {n : N | b⁻¹ * n.1 * b ∈ K} = ((conjSub K b).comap N.subtype : Subgroup N) := by
    ext n; exact (mem_conjSub K b n.1).symm
  rw [sR, sN, ← Subgroup.coe_map, div_mul_eq_mul_div, div_mul_eq_mul_div,
    eq_div_iff (mul_pos nK pK).ne']
  apply mul_right_cancel₀ (mul_pos nD pD).ne'
  linear_combination (la.real (K.comap N.subtype) * ν.real ((K.comap R.subtype).map π)) * e1 -
    (la.real ((conjSub K b).comap N.subtype) *
      ν.real (((conjSub K b).comap R.subtype).map π)) * e2

end GlobalTheory.RowFubini

import Formalism.DoubleCosetMeasures.Statement

noncomputable section

open MeasureTheory

namespace Formalism.DoubleCosetMeasures.P

section Generic

variable {X : Type}

def cls (r : Setoid X) (q : Quotient r) : Set X := Quotient.mk r ⁻¹' {q}

theorem mem_cls {r : Setoid X} {q : Quotient r} {y : X} :
    y ∈ cls r q ↔ Quotient.mk r y = q := Iff.rfl

variable [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem support_out_finite (r : Setoid X) (hr : ∀ q, IsOpen (cls r q)) (f : X → E)
    (hc : HasCompactSupport f) :
    (Function.support (fun q : Quotient r => f q.out)).Finite := by
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (cls r) hr (by
    intro x _; exact Set.mem_iUnion.2 ⟨Quotient.mk r x, rfl⟩)
  refine t.finite_toSet.subset ?_
  intro q hq
  obtain ⟨q', hq', hm⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport f hq))
  have hqq : q = q' := (Quotient.out_eq q).symm.trans hm
  exact hqq ▸ hq'

theorem eq_sum_indicator (r : Setoid X) (f : X → E)
    (hf : ∀ x y, Quotient.mk r x = Quotient.mk r y → f x = f y)
    (t : Finset (Quotient r)) (ht : Function.support (fun q : Quotient r => f q.out) ⊆ t) :
    f = fun x => ∑ q ∈ t, (cls r q).indicator (fun _ => f q.out) x := by
  classical
  funext x
  have hx : f x = f (Quotient.mk r x).out := hf _ _ (Quotient.out_eq _).symm
  simp only [Set.indicator_apply, mem_cls]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · exact hx
  · rw [hx]
    by_contra hne
    exact h (ht hne)

theorem integral_eq_finsum (r : Setoid X) (hr : ∀ q, IsOpen (cls r q)) (μ : Measure X)
    (f : X → E) (hf : ∀ x y, Quotient.mk r x = Quotient.mk r y → f x = f y)
    (hc : HasCompactSupport f)
    (hμ : (∀ q, μ (cls r q) < ⊤) ∨ (∀ q, μ (cls r q) = ⊤)) :
    ∫ x, f x ∂μ = ∑ᶠ q : Quotient r, (μ (cls r q)).toReal • f q.out := by
  classical
  have hfin := support_out_finite r hr f hc
  have ht : Function.support (fun q : Quotient r => f q.out) ⊆ (hfin.toFinset : Set _) := by
    simp
  have hsupp : Function.support (fun q : Quotient r => (μ (cls r q)).toReal • f q.out) ⊆
      (hfin.toFinset : Set _) := fun q hq => ht (fun h => hq (by simp [h]))
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rcases hμ with hμ | hμ
  · conv_lhs => rw [eq_sum_indicator r f hf hfin.toFinset ht]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_indicator_const _ ((hr q).measurableSet)]
      rfl
    · intro q _
      exact (integrable_indicator_iff (hr q).measurableSet).2 (integrableOn_const (hμ q).ne)
  · have h0 : ∀ q, (μ (cls r q)).toReal • f q.out = 0 := fun q => by simp [hμ q]
    simp only [h0, Finset.sum_const_zero]
    by_cases hz : ∀ q : Quotient r, f q.out = 0
    · have : f = 0 := funext fun x => (hf _ _ (Quotient.out_eq _).symm).trans (hz _)
      simp [this]
    · push Not at hz
      obtain ⟨q, hq⟩ := hz
      apply integral_undef
      intro hint
      have hlt := hint.measure_norm_ge_lt_top (ε := ‖f q.out‖) (norm_pos_iff.2 hq)
      have hsub : cls r q ⊆ {x | ‖f q.out‖ ≤ ‖f x‖} := fun x hx => by
        show ‖f q.out‖ ≤ ‖f x‖
        rw [hf x q.out (hx.trans (Quotient.out_eq q).symm)]
      exact absurd (hμ q) ((measure_mono hsub).trans_lt hlt).ne

end Generic

section Left

variable {G : Type} [Group G]

theorem cls_leftRel (K₀ : Subgroup G) (q : G ⧸ K₀) :
    cls (QuotientGroup.leftRel K₀) q = (fun z => q.out⁻¹ * z) ⁻¹' (K₀ : Set G) := by
  ext y
  simp only [Set.mem_preimage, SetLike.mem_coe]
  rw [mem_cls]
  constructor
  · intro h
    have h' : (y : G ⧸ K₀) = ((q.out : G) : G ⧸ K₀) := h.trans (Quotient.out_eq q).symm
    rw [QuotientGroup.eq] at h'
    simpa using K₀.inv_mem h'
  · intro h
    have h' : ((q.out : G) : G ⧸ K₀) = (y : G ⧸ K₀) := by
      rw [QuotientGroup.eq]; exact h
    exact h'.symm.trans (Quotient.out_eq q)

end Left

theorem intRightInv : Formalism.DoubleCosetMeasures.IntRightInv := by
  intro G _ _ _ _ _ μ _ K₀ hK E _ _ _ f hf hc
  have hr : ∀ q, IsOpen (cls (QuotientGroup.leftRel K₀) q) := fun q => by
    rw [cls_leftRel]; exact hK.preimage (continuous_const.mul continuous_id)
  have hμq : ∀ q : G ⧸ K₀, μ (cls (QuotientGroup.leftRel K₀) q) = μ (K₀ : Set G) := fun q => by
    rw [cls_leftRel, measure_preimage_mul]
  have hf' : ∀ x y : G, Quotient.mk (QuotientGroup.leftRel K₀) x =
      Quotient.mk (QuotientGroup.leftRel K₀) y → f x = f y := by
    intro x y h
    have h' : (x : G ⧸ K₀) = (y : G ⧸ K₀) := h
    rw [QuotientGroup.eq] at h'
    have := hf x _ h'
    rw [mul_inv_cancel_left] at this
    exact this.symm
  refine ⟨support_out_finite _ hr f hc, ?_⟩
  rw [integral_eq_finsum _ hr μ f hf' hc]
  · exact finsum_congr fun q => by rw [hμq]
  · by_cases h : μ (K₀ : Set G) < ⊤
    · exact Or.inl fun q => (hμq q).symm ▸ h
    · exact Or.inr fun q => (hμq q).trans (not_lt_top_iff.1 h)

section Doset

variable {G : Type} [Group G]

def dcMap (K₀ : Subgroup G) (g : G) (k : K₀) : G ⧸ K₀ := ((k : G) * g : G)

theorem doubleCoset_eq_preimage (K₀ : Subgroup G) (g : G) :
    DoubleCoset.doubleCoset g (K₀ : Set G) K₀ =
      (QuotientGroup.mk : G → G ⧸ K₀) ⁻¹' Set.range (dcMap K₀ g) := by
  ext y
  rw [DoubleCoset.mem_doubleCoset]
  simp only [Set.mem_preimage, Set.mem_range, dcMap, SetLike.mem_coe]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using hb
  · rintro ⟨k, hk⟩
    rw [QuotientGroup.eq] at hk
    exact ⟨k, k.2, _, hk, by group⟩

theorem dcMap_eq_iff (K₀ : Subgroup G) (g : G) (k k' : K₀) :
    dcMap K₀ g k = dcMap K₀ g k' ↔
      k⁻¹ * k' ∈ (K₀.map (MulAut.conj g).toMonoidHom).subgroupOf K₀ := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  simp only [dcMap, QuotientGroup.eq]
  simp [mul_assoc]

theorem card_range_dcMap (K₀ : Subgroup G) (g : G) :
    Nat.card (Set.range (dcMap K₀ g)) = (K₀.map (MulAut.conj g).toMonoidHom).relIndex K₀ := by
  have hker : Setoid.ker (dcMap K₀ g) =
      QuotientGroup.leftRel ((K₀.map (MulAut.conj g).toMonoidHom).subgroupOf K₀) := by
    ext k k'
    rw [Setoid.ker_def, QuotientGroup.leftRel_apply]
    exact dcMap_eq_iff K₀ g k k'
  rw [Subgroup.relIndex, Subgroup.index,
    ← Nat.card_congr (Setoid.quotientKerEquivRange (dcMap K₀ g)), hker]
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem relIndex_conj_ne_zero (K₀ : Subgroup G) (hK : IsOpen (K₀ : Set G))
    (hc : IsCompact (K₀ : Set G)) (g : G) :
    (K₀.map (MulAut.conj g).toMonoidHom).relIndex K₀ ≠ 0 := by
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 hc
  have hopen : IsOpen (((K₀.map (MulAut.conj g).toMonoidHom).subgroupOf K₀ : Subgroup K₀) :
      Set K₀) := by
    have : (((K₀.map (MulAut.conj g).toMonoidHom).subgroupOf K₀ : Subgroup K₀) : Set K₀) =
        Subtype.val ⁻¹' ((fun x => g⁻¹ * x * g) ⁻¹' (K₀ : Set G)) := by
      ext k
      simp only [Set.mem_preimage, SetLike.mem_coe]
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    rw [this]
    exact (hK.preimage (by fun_prop)).preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ hopen
  exact Subgroup.index_ne_zero_of_finite

theorem isOpen_cls_leftRel (K₀ : Subgroup G) (hK : IsOpen (K₀ : Set G)) (q : G ⧸ K₀) :
    IsOpen (cls (QuotientGroup.leftRel K₀) q) := by
  rw [cls_leftRel]; exact hK.preimage (continuous_const.mul continuous_id)

variable [MeasurableSpace G] [BorelSpace G]

theorem measure_preimage_mk (μ : Measure G) [μ.IsMulLeftInvariant] (K₀ : Subgroup G)
    (hK : IsOpen (K₀ : Set G)) (S : Set (G ⧸ K₀)) (hS : S.Finite) :
    μ ((QuotientGroup.mk : G → G ⧸ K₀) ⁻¹' S) = (Nat.card S : ENNReal) * μ (K₀ : Set G) := by
  classical
  have hU : (QuotientGroup.mk : G → G ⧸ K₀) ⁻¹' S =
      ⋃ q ∈ hS.toFinset, cls (QuotientGroup.leftRel K₀) q := by
    ext y
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.Finite.mem_toFinset, mem_cls,
      exists_prop, exists_eq_right']
  rw [hU, measure_biUnion_finset]
  · simp_rw [cls_leftRel, measure_preimage_mul]
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card S hS]
  · intro q _ q' _ hne
    exact Set.disjoint_left.2 fun x hx hx' => hne (hx.symm.trans hx')
  · exact fun q _ => (isOpen_cls_leftRel K₀ hK q).measurableSet

end Doset

theorem dosetVol : Formalism.DoubleCosetMeasures.DosetVol := by
  intro G _ _ _ _ _ μ _ K₀ hK hc g
  have hne := relIndex_conj_ne_zero K₀ hK hc g
  refine ⟨hne, ?_⟩
  have hfin : (Set.range (dcMap K₀ g)).Finite := by
    have : Finite (Set.range (dcMap K₀ g)) := Nat.finite_of_card_ne_zero (by
      rw [card_range_dcMap]; exact hne)
    exact Set.toFinite _
  rw [doubleCoset_eq_preimage, measure_preimage_mk μ K₀ hK _ hfin, card_range_dcMap]

theorem cls_double {G : Type} [Group G] (K₀ : Subgroup G)
    (q : Quotient (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G))) :
    cls (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G)) q =
      DoubleCoset.doubleCoset (Quotient.out q) (K₀ : Set G) K₀ := by
  ext y
  rw [mem_cls]
  exact (DoubleCoset.mem_quotToDoubleCoset_iff (H := K₀) (K := K₀) q y).symm

theorem intBiInv : Formalism.DoubleCosetMeasures.IntBiInv := by
  intro G _ _ _ _ _ μ _ K₀ hK hc E _ _ _ f hf hcs
  have hr : ∀ q, IsOpen (cls (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G)) q) := fun q => by
    rw [cls_double]
    exact hK.mul_left
  have hμq : ∀ q, μ (cls (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G)) q) =
      ((K₀.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex K₀ : ENNReal) *
        μ (K₀ : Set G) := fun q => by
    rw [cls_double]; exact (dosetVol G μ K₀ hK hc _).2
  have hf' : ∀ x y : G, Quotient.mk (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G)) x =
      Quotient.mk (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G)) y → f x = f y := by
    intro x y h
    obtain ⟨a, ha, b, hb, rfl⟩ := (DoubleCoset.eq K₀ K₀ x y).1 h
    exact (hf a ha b hb x).symm
  refine ⟨support_out_finite _ hr f hcs, ?_⟩
  rw [integral_eq_finsum _ hr μ f hf' hcs]
  · exact finsum_congr fun q => by rw [hμq, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  · by_cases h : μ (K₀ : Set G) < ⊤
    · exact Or.inl fun q => (hμq q).symm ▸ ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) h
    · refine Or.inr fun q => ?_
      rw [hμq, not_lt_top_iff.1 h]
      exact ENNReal.mul_top (Nat.cast_ne_zero.2 (relIndex_conj_ne_zero K₀ hK hc _))

end Formalism.DoubleCosetMeasures.P

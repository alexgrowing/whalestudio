import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3
open scoped Topology Pointwise

noncomputable section

namespace PositivityTheory.Rg.Ming.GermX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valSet_eq (a : k) (c : kˣ) :
    {y : k | valuation k (y - a) ≤ valuation k (c : k)} = (fun y => -a + y) ⁻¹' (c • (𝒪[k] : Set k)) := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  change _ ↔ valuation k (((c⁻¹ : kˣ) : k) * (-a + y)) ≤ 1
  have hc : (0 : ValueGroupWithZero k) < valuation k (c : k) := by
    rw [zero_lt_iff, ne_eq, map_eq_zero]
    exact c.ne_zero
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, neg_add_eq_sub, inv_mul_le_iff₀ hc, mul_one]

theorem isOpen_valSet (a : k) (c : kˣ) : IsOpen {y : k | valuation k (y - a) ≤ valuation k (c : k)} := by
  rw [valSet_eq]
  exact (continuous_add_left (-a)).isOpen_preimage _ ((GlobalTheory.SplitWeil.isOpen_int k).smul c)

private theorem vol_valSet_lemma : SigmaCompactSpace k := by
  obtain ⟨t, ht0, ht1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hpos : (0 : ValueGroupWithZero k) < valuation k t := by
    rw [zero_lt_iff, ne_eq, map_eq_zero]
    exact ht0
  have hs : 1 < valuation k t⁻¹ := by
    rw [map_inv₀]
    exact (one_lt_inv₀ hpos).2 ht1
  refine SigmaCompactSpace.of_countable
    (Set.range fun n : ℕ => {x : k | valuation k x ≤ valuation k t⁻¹ ^ n}) (Set.countable_range _) ?_ ?_
  · rintro _ ⟨n, rfl⟩
    exact IsNonarchimedeanLocalField.isCompact_closedBall k _
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := MulArchimedean.arch (valuation k x) hs
    exact Set.mem_sUnion.2 ⟨_, ⟨n, rfl⟩, hn⟩

theorem vol_valSet [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (a : k) (c : kˣ) :
    ν {y : k | valuation k (y - a) ≤ valuation k (c : k)} = ENNReal.ofReal (nabs k c) := by
  haveI := hν.1
  rw [valSet_eq, measure_preimage_add]
  exact GlobalTheory.SplitWeil.Model.nabs_vol ν hν c

variable {n r : ℕ}

theorem ballM_eq_pi (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) :
    (ballM c x₀ : Set (Matrix (Fin n) (Fin r) k)) =
      (Set.univ.pi fun i => Set.univ.pi fun l => {y : k | valuation k (y - x₀ i l) ≤ valuation k (c : k)} :
        Set (Fin n → Fin r → k)) := by
  ext x
  simp only [ballM, Set.mem_setOf_eq]
  exact ⟨fun h i _ l _ => h i l, fun h i l => h i (Set.mem_univ _) l (Set.mem_univ _)⟩

theorem measurableSet_ballM [MeasurableSpace k] [BorelSpace k] (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) :
    MeasurableSet (ballM c x₀) := by
  rw [ballM_eq_pi]
  exact MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun l => (isOpen_valSet _ c).measurableSet

theorem volM_ballM [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (c : kˣ)
    (x₀ : Matrix (Fin n) (Fin r) k) :
    volM ν (Fin n) (Fin r) (ballM c x₀) = ∏ _i : Fin n, ∏ _l : Fin r, ENNReal.ofReal (nabs k c) := by
  haveI := hν.1
  haveI := vol_valSet_lemma (k := k)
  have h1 : (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin r => ν)
      (Set.univ.pi fun i => Set.univ.pi fun l => {y : k | valuation k (y - x₀ i l) ≤ valuation k (c : k)}) =
      ∏ _i : Fin n, ∏ _l : Fin r, ENNReal.ofReal (nabs k c) := by
    rw [Measure.pi_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Measure.pi_pi]
    exact Finset.prod_congr rfl fun l _ => vol_valSet ν hν _ c
  rw [← h1, ballM_eq_pi]
  rfl

theorem volM_ballM_ne_zero [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (c : kˣ)
    (x₀ : Matrix (Fin n) (Fin r) k) : (volM ν (Fin n) (Fin r) (ballM c x₀)).toReal ≠ 0 := by
  rw [volM_ballM ν hν c x₀, ENNReal.toReal_prod]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rw [ENNReal.toReal_prod]
  refine Finset.prod_ne_zero_iff.2 fun l _ => ?_
  rw [ENNReal.toReal_ofReal (GlobalTheory.SplitWeil.nabs_pos k c).le]
  exact (GlobalTheory.SplitWeil.nabs_pos k c).ne'

theorem volM_ballM_eq [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (c : kˣ)
    (x₀ x₁ : Matrix (Fin n) (Fin r) k) :
    volM ν (Fin n) (Fin r) (ballM c x₀) = volM ν (Fin n) (Fin r) (ballM c x₁) := by
  rw [volM_ballM ν hν, volM_ballM ν hν]

theorem integral_ind [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) :
    ∫ x, (ballM c x₀).indicator (fun _ => (1 : ℂ)) x ∂volM ν (Fin n) (Fin r) =
      ((volM ν (Fin n) (Fin r) (ballM c x₀)).toReal : ℂ) := by
  rw [integral_indicator_const _ (measurableSet_ballM c x₀)]
  simp [Measure.real]

theorem integrable_ind [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (c : kˣ)
    (x₀ : Matrix (Fin n) (Fin r) k) :
    Integrable ((ballM c x₀).indicator (fun _ => (1 : ℂ))) (volM ν (Fin n) (Fin r)) := by
  have hfin : volM ν (Fin n) (Fin r) (ballM c x₀) ≠ ⊤ := by
    intro h
    exact volM_ballM_ne_zero ν hν c x₀ (by rw [h]; rfl)
  exact (integrable_indicator_iff (measurableSet_ballM c x₀)).2 (integrableOn_const hfin)

end PositivityTheory.Rg.Ming.GermX

namespace PositivityTheory.Rg.Ming.GermX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ballM_mono {n r : ℕ} {c c' : kˣ} (hle : valuation k (c : k) ≤ valuation k (c' : k))
    {x₀ : Matrix (Fin n) (Fin r) k} : ballM c x₀ ⊆ ballM c' x₀ :=
  fun _ hx i l => (hx i l).trans hle

theorem KO_entry {N : ℕ} {h : GL (Fin N) k} (hh : h ∈ KO k (Fin N)) (i j : Fin N) :
    valuation k (h.val i j) ≤ 1 := by
  obtain ⟨H, rfl⟩ := hh
  exact (H.val i j).2

theorem KO_det {N : ℕ} {h : GL (Fin N) k} (hh : h ∈ KO k (Fin N)) :
    valuation k ((Matrix.GeneralLinearGroup.det h : kˣ) : k) = 1 := by
  obtain ⟨g, rfl⟩ := hh
  have h1 : valuation k ((Matrix.GeneralLinearGroup.det g : (𝒪[k])ˣ) : 𝒪[k]) ≤ 1 :=
    ((Matrix.GeneralLinearGroup.det g : (𝒪[k])ˣ) : 𝒪[k]).2
  have h3 : valuation k ((Matrix.GeneralLinearGroup.det g : (𝒪[k])ˣ) : 𝒪[k]) *
      valuation k (((Matrix.GeneralLinearGroup.det g)⁻¹ : (𝒪[k])ˣ) : 𝒪[k]) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]
    simp
  have h4 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
      ((Matrix.GeneralLinearGroup.det g : (𝒪[k])ˣ) : 𝒪[k]) := by
    simp only [Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.val_det_apply]
    exact (RingHom.map_det (algebraMap 𝒪[k] k) g.val).symm
  rw [h4]
  refine le_antisymm h1 ?_
  calc (1 : ValueGroupWithZero k) = _ := h3.symm
    _ ≤ valuation k ((Matrix.GeneralLinearGroup.det g : (𝒪[k])ˣ) : 𝒪[k]) * 1 := by
      gcongr
      exact (((Matrix.GeneralLinearGroup.det g)⁻¹ : (𝒪[k])ˣ) : 𝒪[k]).2
    _ = _ := mul_one _

theorem inv_close {N : ℕ} {h : GL (Fin N) k} (hh : h ∈ KO k (Fin N)) {c : kˣ}
    (hc : h.val ∈ ballM c (1 : Matrix (Fin N) (Fin N) k)) : (h⁻¹).val ∈ ballM c (1 : Matrix (Fin N) (Fin N) k) := by
  intro i j
  have hinv : h⁻¹ ∈ KO k (Fin N) := inv_mem hh
  have key : (h⁻¹).val - 1 = (h⁻¹).val * (1 - h.val) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Units.inv_mul]
  have e : (h⁻¹).val i j - (1 : Matrix (Fin N) (Fin N) k) i j = ((h⁻¹).val * (1 - h.val)) i j := by
    rw [← key]
    rfl
  rw [e, Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  have hb : valuation k ((1 - h.val) l j) ≤ valuation k (c : k) := by
    rw [Matrix.sub_apply, Valuation.map_sub_swap]
    exact hc l j
  exact (mul_le_mul' (KO_entry hinv i l) hb).trans_eq (one_mul _)

theorem transport {r t : ℕ} {c : kˣ} (hc : valuation k (c : k) < 1) {x : Matrix (Fin (r + t)) (Fin r) k}
    (hx : x ∈ ballM c (GlobalTheory.GodementJacquet.eMat k r t)) :
    ∃ h : GL (Fin (r + t)) k, h ∈ KO k (Fin (r + t)) ∧ h.val ∈ ballM c (1 : Matrix (Fin (r + t)) (Fin (r + t)) k) ∧
      h.val * GlobalTheory.GodementJacquet.eMat k r t = x := by
  set e := GlobalTheory.GodementJacquet.eMat k r t with he_def
  set D : Matrix (Fin (r + t)) (Fin (r + t)) k := (x - e) * e.transpose with hD
  have he01 : ∀ i j, valuation k (e i j) ≤ 1 := by
    intro i j
    simp only [he_def, GlobalTheory.GodementJacquet.eMat, Matrix.of_apply]
    split_ifs <;> simp
  have hDc : ∀ i j, valuation k (D i j) ≤ valuation k (c : k) := by
    intro i j
    rw [hD, Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul, Matrix.sub_apply, Matrix.transpose_apply]
    exact (mul_le_mul' (hx i l) (he01 j l)).trans_eq (mul_one _)
  have hD1 : ∀ i j, valuation k (D i j) ≤ 1 := fun i j => (hDc i j).trans hc.le
  have heTe : e.transpose * e = 1 := by
    ext j j'
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply, he_def, GlobalTheory.GodementJacquet.eMat, Matrix.of_apply]
    rw [Finset.sum_eq_single (Fin.castAdd t j)]
    · simp [Fin.ext_iff]
    · intro b _ hb
      have hbj : (b : ℕ) ≠ j := fun h => hb (Fin.ext h)
      simp [hbj]
    · simp
  let D' : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k] := fun i j => ⟨D i j, hD1 i j⟩
  let M : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k] := 1 + D'
  have hres : M.map (IsLocalRing.residue 𝒪[k]) = 1 := by
    ext i j
    simp only [M, Matrix.map_apply, Matrix.add_apply, map_add]
    have h0 : IsLocalRing.residue 𝒪[k] (D' i j) = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      exact (hDc i j).trans_lt hc
    rw [h0, add_zero]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  have hdet : IsUnit M.det := by
    apply isUnit_of_map_unit (IsLocalRing.residue 𝒪[k])
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hres, Matrix.det_one]
    exact isUnit_one
  let g : GL (Fin (r + t)) 𝒪[k] := ((Matrix.isUnit_iff_isUnit_det M).2 hdet).unit
  have hgv : (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g).val = 1 + D := by
    ext i j
    change algebraMap 𝒪[k] k ((1 + D') i j) = (1 + D) i j
    rw [Matrix.add_apply, Matrix.add_apply, map_add]
    congr 1
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g, ⟨g, rfl⟩, ?_, ?_⟩
  · rw [hgv]
    intro i j
    simpa [Matrix.add_apply] using hDc i j
  · rw [hgv, Matrix.add_mul, Matrix.one_mul, hD, Matrix.mul_assoc, heTe, Matrix.mul_one, add_sub_cancel]

theorem nbhd (hb : BallSt) {N : ℕ} (S : Set (GL (Fin N) k)) (hS : S ∈ 𝓝 (1 : GL (Fin N) k)) :
    ∃ c : kˣ, valuation k (c : k) < 1 ∧ ∀ h ∈ KO k (Fin N),
      h.val ∈ ballM c (1 : Matrix (Fin N) (Fin N) k) → h ∈ S := by
  have hemb := Units.isEmbedding_embedProduct (M := Matrix (Fin N) (Fin N) k)
  rw [hemb.isInducing.nhds_eq_comap, Filter.mem_comap] at hS
  obtain ⟨t, ht, hts⟩ := hS
  rw [map_one] at ht
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 ht
  have hV' : MulOpposite.op ⁻¹' V ∈ 𝓝 (1 : Matrix (Fin N) (Fin N) k) :=
    MulOpposite.continuous_op.continuousAt hV
  obtain ⟨c₁, hc₁, hb₁⟩ := (hb k N N).2.1 1 U hU
  obtain ⟨c₂, hc₂, hb₂⟩ := (hb k N N).2.1 1 _ hV'
  have fin : ∀ c : kˣ, valuation k (c : k) < 1 → valuation k (c : k) ≤ valuation k (c₁ : k) →
      valuation k (c : k) ≤ valuation k (c₂ : k) → ∃ c : kˣ, valuation k (c : k) < 1 ∧ ∀ h ∈ KO k (Fin N),
      h.val ∈ ballM c (1 : Matrix (Fin N) (Fin N) k) → h ∈ S := by
    intro c hc h1 h2
    refine ⟨c, hc, fun h hh hx => hts ?_⟩
    show Units.embedProduct _ h ∈ t
    rw [Units.embedProduct_apply]
    exact hUV ⟨hb₁ (ballM_mono h1 hx), hb₂ (ballM_mono h2 (inv_close hh hx))⟩
  rcases le_total (valuation k (c₁ : k)) (valuation k (c₂ : k)) with h12 | h12
  · exact fin c₁ hc₁ le_rfl h12
  · exact fin c₂ hc₂ h12 le_rfl

end PositivityTheory.Rg.Ming.GermX

namespace PositivityTheory.Rg.Ming.GermX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem nabs_eq_one {u : kˣ} (hu : valuation k (u : k) = 1) : nabs k u = 1 := by
  have hinv : valuation k ((u⁻¹ : kˣ) : k) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  apply le_antisymm
  · have := GlobalTheory.SplitWeil.nabs_le_of_valuation_le (k := k) (x := u) (y := 1) (by simp [hu])
    simpa [GlobalTheory.SplitWeil.nabs_one] using this
  · have := GlobalTheory.SplitWeil.nabs_le_of_valuation_le (k := k) (x := 1) (y := u) (by simp [hu])
    simpa [GlobalTheory.SplitWeil.nabs_one] using this

omit [MeasurableSpace k] [BorelSpace k] in
theorem om_one_left {N M : ℕ} (μ : kˣ →* ℂˣ) (h : GL (Fin N) k)
    (hμ : μ (Matrix.GeneralLinearGroup.det h) = 1) (hn : nabs k (Matrix.GeneralLinearGroup.det h) = 1)
    (Φ : Matrix (Fin N) (Fin M) k → ℂ) (x : Matrix (Fin N) (Fin M) k) :
    om μ (1 : GL (Fin M) k) h Φ x = Φ ((h⁻¹ : GL (Fin N) k).val * x) := by
  simp [om, hμ, hn, GlobalTheory.SplitWeil.Model.nabs_one]

omit [MeasurableSpace k] [BorelSpace k] in
theorem mem_ballM_self {n r : ℕ} (c : kˣ) (x : Matrix (Fin n) (Fin r) k) : x ∈ ballM c x :=
  fun i l => by simp

theorem inv_ball (hb : BallSt) {r t : ℕ} (μ : kˣ →* ℂˣ) {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V)
    (π : Representation ℂ (GL (Fin (r + t)) k) W)
    (B : SB (Matrix (Fin (r + t)) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V) (hE : Equi μ σ π B) (w : W)
    (I : kˣ → Matrix (Fin (r + t)) (Fin r) k → SB (Matrix (Fin (r + t)) (Fin r) k))
    (hI : ∀ c x, (I c x).1 = (ballM c x).indicator (fun _ => (1 : ℂ)))
    {c : kˣ} (hc : valuation k (c : k) < 1)
    (hcS : ∀ h ∈ KO k (Fin (r + t)), h.val ∈ ballM c (1 : Matrix (Fin (r + t)) (Fin (r + t)) k) →
      h ∈ {h : GL (Fin (r + t)) k | π h w = w} ∩ {h | μ (Matrix.GeneralLinearGroup.det h) = 1})
    (c' : kˣ) (x : Matrix (Fin (r + t)) (Fin r) k) (hx : x ∈ ballM c (GlobalTheory.GodementJacquet.eMat k r t)) :
    B (I c' x) w = B (I c' (GlobalTheory.GodementJacquet.eMat k r t)) w := by
  obtain ⟨h, hK, hb1, hhe⟩ := transport hc hx
  have hmem := hcS h hK hb1
  have hw : π h w = w := hmem.1
  have hμh : μ (Matrix.GeneralLinearGroup.det h) = 1 := hmem.2
  have hn : nabs k (Matrix.GeneralLinearGroup.det h) = 1 := nabs_eq_one (KO_det hK)
  have hx' : (h⁻¹ : GL (Fin (r + t)) k).val * x = GlobalTheory.GodementJacquet.eMat k r t := by
    rw [← hhe, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hom : (I c' x).1 = om μ (1 : GL (Fin r) k) h (I c' (GlobalTheory.GodementJacquet.eMat k r t)).1 := by
    funext y
    rw [om_one_left μ h hμh hn, hI, hI]
    have hiff : (h⁻¹ : GL (Fin (r + t)) k).val * y ∈ ballM c' (GlobalTheory.GodementJacquet.eMat k r t) ↔
        y ∈ ballM c' x := by
      have key := ((hb k (r + t) r).1 c' x).2.2.2.2 h⁻¹ (inv_mem hK) 1 (one_mem _) y
      rw [Units.val_one, Matrix.mul_one, Matrix.mul_one, hx'] at key
      exact key
    by_cases hy : y ∈ ballM c' x
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hiff.2 hy)]
    · have hy' : (h⁻¹ : GL (Fin (r + t)) k).val * y ∉ ballM c' (GlobalTheory.GodementJacquet.eMat k r t) :=
        fun h' => hy (hiff.1 h')
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy']
  have key := hE 1 h (I c' (GlobalTheory.GodementJacquet.eMat k r t)) (I c' x) hom w
  rw [hw] at key
  simpa using key

theorem decomp_smul (ν : Measure k) (hν : IsUnitVol ν) {n r : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V) (w : W)
    (I : kˣ → Matrix (Fin n) (Fin r) k → SB (Matrix (Fin n) (Fin r) k))
    (hI : ∀ c x, (I c x).1 = (ballM c x).indicator (fun _ => (1 : ℂ)))
    (c' : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) (R : Set (Matrix (Fin n) (Fin r) k))
    (hA : ∀ x ∈ R, B (I c' x) w = B (I c' x₀) w)
    (Ψ : SB (Matrix (Fin n) (Fin r) k)) (S : Finset (Matrix (Fin n) (Fin r) k)) (hS : ∀ x ∈ S, x ∈ R)
    (hsum : Ψ.1 = ∑ x ∈ S, Ψ.1 x • (ballM c' x).indicator (fun _ => (1 : ℂ))) :
    (((volM ν (Fin n) (Fin r) (ballM c' x₀)).toReal : ℂ)) • B Ψ w = (∫ y, Ψ.1 y ∂volM ν (Fin n) (Fin r)) • B (I c' x₀) w := by
  haveI := hν.1
  have hΨ : Ψ = ∑ x ∈ S, Ψ.1 x • I c' x := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    conv_lhs => rw [hsum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Submodule.coe_smul, hI]
  have hB : B Ψ w = (∑ x ∈ S, Ψ.1 x) • B (I c' x₀) w := by
    conv_lhs => rw [hΨ]
    rw [map_sum, LinearMap.sum_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [map_smul, LinearMap.smul_apply, hA x (hS x hx)]
  have hfun : ∀ y, Ψ.1 y = ∑ x ∈ S, Ψ.1 x • (ballM c' x).indicator (fun _ => (1 : ℂ)) y := by
    intro y
    conv_lhs => rw [hsum]
    simp only [Finset.sum_apply, Pi.smul_apply]
  have hint : ∫ y, Ψ.1 y ∂volM ν (Fin n) (Fin r) =
      (∑ x ∈ S, Ψ.1 x) * ((volM ν (Fin n) (Fin r) (ballM c' x₀)).toReal : ℂ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hfun),
      integral_finset_sum S (f := fun x a => Ψ.1 x • (ballM c' x).indicator (fun _ => (1 : ℂ)) a)
        (fun x _ => (integrable_ind ν hν c' x).smul (Ψ.1 x)), Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_smul, integral_ind, volM_ballM_eq ν hν c' x x₀, smul_eq_mul]
  rw [hB, hint, smul_smul, mul_comm (∑ x ∈ S, Ψ.1 x)]

end PositivityTheory.Rg.Ming.GermX

namespace PositivityTheory.Rg.Ming

open PositivityTheory.Rg.Ming.GermX

theorem germ (hb : BallSt) : GermSt := by
  intro k _ _ _ _ _ _ ν hν r t μ V _ _ W _ _ σ π B hμ hπ hE w
  set e := GlobalTheory.GodementJacquet.eMat k r t with he
  have hdet : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin (r + t)) k → kˣ) := by
    rw [Units.continuous_iff]
    constructor
    · exact Units.continuous_val.matrix_det
    · exact Units.continuous_coe_inv.matrix_det
  have hopen : IsOpen {h : GL (Fin (r + t)) k | μ (Matrix.GeneralLinearGroup.det h) = 1} := by
    have h0 := hμ.preimage hdet
    convert h0 using 1
    ext h
    simp [MonoidHom.mem_ker]
  have hS : ({h : GL (Fin (r + t)) k | π h w = w} ∩ {h | μ (Matrix.GeneralLinearGroup.det h) = 1}) ∈
      𝓝 (1 : GL (Fin (r + t)) k) :=
    Filter.inter_mem ((hπ w).mem_nhds (by simp)) (hopen.mem_nhds (by simp))
  obtain ⟨c, hc, hcS⟩ := nbhd hb _ hS
  let I : kˣ → Matrix (Fin (r + t)) (Fin r) k → SB (Matrix (Fin (r + t)) (Fin r) k) :=
    fun c x => ⟨(ballM c x).indicator (fun _ => (1 : ℂ)), ((hb k (r + t) r).1 c x).2.2.1⟩
  have hI : ∀ c x, (I c x).1 = (ballM c x).indicator (fun _ => (1 : ℂ)) := fun _ _ => rfl
  have hmin : ∀ a b : kˣ, ∃ d : kˣ, valuation k (d : k) ≤ valuation k (a : k) ∧
      valuation k (d : k) ≤ valuation k (b : k) := by
    intro a b
    rcases le_total (valuation k (a : k)) (valuation k (b : k)) with hab | hab
    · exact ⟨a, le_rfl, hab⟩
    · exact ⟨b, hab, le_rfl⟩
  refine ⟨(((volM ν (Fin (r + t)) (Fin r) (ballM c e)).toReal : ℂ))⁻¹ • B (I c e) w, c, fun Φ hΦ => ?_⟩
  obtain ⟨c₀, hc₀⟩ := (hb k (r + t) r).2.2 Φ
  obtain ⟨c₁, hc₁⟩ := (hb k (r + t) r).2.2 (I c e)
  obtain ⟨c', hc'a, hc'b⟩ := hmin c₀ c₁
  obtain ⟨S, hS1, hS2⟩ := hc₀ c' hc'a
  obtain ⟨S', hS1', hS2'⟩ := hc₁ c' hc'b
  have hA : ∀ x ∈ ballM c e, B (I c' x) w = B (I c' e) w :=
    fun x hx => inv_ball hb μ σ π B hE w I hI hc hcS c' x hx
  have hSR : ∀ x ∈ S, x ∈ ballM c e := fun x hx => hΦ x (hS1 x hx x (mem_ballM_self c' x)).2
  have hSR' : ∀ x ∈ S', x ∈ ballM c e := by
    intro x hx
    have hne := (hS1' x hx x (mem_ballM_self c' x)).2
    by_contra hn
    apply hne
    rw [hI, Set.indicator_of_notMem hn]
  have h1 := decomp_smul ν hν B w I hI c' e (ballM c e) hA Φ S hSR hS2
  have h2 := decomp_smul ν hν B w I hI c' e (ballM c e) hA (I c e) S' hSR' hS2'
  have h3 : ∫ y, (I c e).1 y ∂volM ν (Fin (r + t)) (Fin r) =
      ((volM ν (Fin (r + t)) (Fin r) (ballM c e)).toReal : ℂ) := integral_ind ν c e
  rw [h3] at h2
  have hv' : ((volM ν (Fin (r + t)) (Fin r) (ballM c' e)).toReal : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (volM_ballM_ne_zero ν hν c' e)
  have hvc : ((volM ν (Fin (r + t)) (Fin r) (ballM c e)).toReal : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (volM_ballM_ne_zero ν hν c e)
  have hBce : B (I c e) w = (((volM ν (Fin (r + t)) (Fin r) (ballM c' e)).toReal : ℂ)⁻¹ *
      ((volM ν (Fin (r + t)) (Fin r) (ballM c e)).toReal : ℂ)) • B (I c' e) w := by
    rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hv', one_smul]
  have hBΦ : B Φ w = (((volM ν (Fin (r + t)) (Fin r) (ballM c' e)).toReal : ℂ)⁻¹ *
      ∫ y, Φ.1 y ∂volM ν (Fin (r + t)) (Fin r)) • B (I c' e) w := by
    rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hv', one_smul]
  rw [hBΦ, hBce, smul_smul, smul_smul]
  congr 1
  field_simp

end PositivityTheory.Rg.Ming

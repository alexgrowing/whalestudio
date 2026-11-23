import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChLApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslationInvariantSchwartzBruhatMapFactorsInte
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology

noncomputable section
namespace GlobalTheory.PartRed.IntEntry

theorem fill_entry {k : Type} [Field k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]
    (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) (e : R × Q)
    (hI : e ∉ I) (hE : e ∉ E) : fillAt β E I x y e.1 e.2 = x e.1 e.2 := by
  obtain ⟨r, q⟩ := e
  simp [fillAt, hI, hE]

theorem fill_add_single {k : Type} [Field k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]
    (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) (e : R × Q)
    (hI : e ∉ I) (hE : e ∉ E) (a : k) :
    fillAt β E I (x + Matrix.single e.1 e.2 a) y = fillAt β E I x y + Matrix.single e.1 e.2 a := by
  obtain ⟨r₀, q₀⟩ := e
  ext r q
  by_cases h1 : (r, q) ∈ I
  · have : ¬ (r₀ = r ∧ q₀ = q) := by rintro ⟨rfl, rfl⟩; exact hI h1
    simp [fillAt, h1, Matrix.single_apply, this]
  · by_cases h2 : (r, q) ∈ E
    · have : ¬ (r₀ = r ∧ q₀ = q) := by rintro ⟨rfl, rfl⟩; exact hE h2
      simp [fillAt, h1, h2, Matrix.single_apply, this]
    · simp [fillAt, h1, h2]

theorem measurePreserving_adjoin {ι X : Type} [DecidableEq ι] [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν]
    (I : Finset ι) (e : ι) (he : e ∉ I) :
    MeasurePreserving
      (fun (p : X × (I → X)) (i : ↥(insert e I : Finset ι)) => if h : i.1 ∈ I then p.2 ⟨i.1, h⟩ else p.1)
      (ν.prod (Measure.pi fun _ : I => ν)) (Measure.pi fun _ : ↥(insert e I : Finset ι) => ν) := by
  have hm : Measurable
      (fun (p : X × (I → X)) (i : ↥(insert e I : Finset ι)) => if h : i.1 ∈ I then p.2 ⟨i.1, h⟩ else p.1) := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases h : i.1 ∈ I
    · simp only [dif_pos h]; fun_prop
    · simp only [dif_neg h]; fun_prop
  refine ⟨hm, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (p : X × (I → X)) (i : ↥(insert e I : Finset ι)) =>
      if h : i.1 ∈ I then p.2 ⟨i.1, h⟩ else p.1) ⁻¹' Set.univ.pi s =
      s ⟨e, Finset.mem_insert_self e I⟩ ×ˢ Set.univ.pi fun i : I => s ⟨i.1, Finset.mem_insert_of_mem i.2⟩ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_prod]
    constructor
    · intro h
      refine ⟨by simpa [he] using h ⟨e, Finset.mem_insert_self e I⟩, fun i => ?_⟩
      simpa [i.2] using h ⟨i.1, Finset.mem_insert_of_mem i.2⟩
    · rintro ⟨h1, h2⟩ ⟨i, hi⟩
      by_cases h : i ∈ I
      · simpa [h] using h2 ⟨i, h⟩
      · obtain rfl : i = e := (Finset.mem_insert.1 hi).resolve_right h
        simpa [h] using h1
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Finset.univ_eq_attach (insert e I), Finset.attach_insert,
    Finset.prod_insert, Finset.prod_image, Finset.univ_eq_attach]
  · intro a _ b _ hab
    exact Subtype.ext (congrArg (fun z : ↥(insert e I : Finset ι) => z.1) hab)
  · intro h
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h
    have : a.1 = e := congrArg (fun z : ↥(insert e I : Finset ι) => z.1) ha
    exact he (this ▸ a.2)

theorem integrable_red : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → ∀ x : Matrix R Q k, Integrable (fun y : I → k => Φ (fillAt β E I x y) * (ψ (-w (fillAt β E I x y)) : ℂ)) (Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ ψ ν hψ hν R Q _ _ _ _ w β E I Φ hΦ x
  haveI := secondCountable k
  haveI := t2Space k
  haveI : LocallyCompactSpace k := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : (Measure.pi fun _ : I => ν).IsAddHaarMeasure := inferInstance
  have hf : Continuous (fillAt β E I x) := by
    refine continuous_matrix fun r q => ?_
    simp only [fillAt, Matrix.of_apply]
    by_cases h : (r, q) ∈ I
    · simp only [dif_pos h]; fun_prop
    · simp only [dif_neg h]; fun_prop
  have hw : Continuous w := by
    have : (w : Matrix R Q k → k) = fun t => ∑ r, ∑ q, t r q * w (Matrix.single r q 1) := by
      funext t
      conv_lhs => rw [Matrix.matrix_eq_sum_single t]
      simp only [map_sum]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun q _ => ?_
      rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this]
    fun_prop
  have hc : Continuous fun y : I → k => Φ (fillAt β E I x y) * (ψ (-w (fillAt β E I x y)) : ℂ) :=
    (hΦ.1.continuous.comp hf).mul (continuous_subtype_val.comp (hψ.comp (hw.comp hf).neg))
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro
    (K := Set.univ.pi fun i : I => (fun t : Matrix R Q k => t i.1.1 i.1.2) '' tsupport Φ)
    (isCompact_univ_pi fun i => hΦ.2.image (by fun_prop)) fun y hy => ?_)
  rw [image_eq_zero_of_notMem_tsupport (f := Φ) fun h => hy fun i _ => ⟨_, h, ?_⟩, zero_mul]
  simp [fillAt, i.2]

theorem red_insert : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → e ∉ I → ∀ (Φ : Matrix R Q k → ℂ) (x : Matrix R Q k), Integrable (fun y : ↥(insert e I : Finset (R × Q)) → k => Φ (fillAt β E (insert e I) x y) * (ψ (-w (fillAt β E (insert e I) x y)) : ℂ)) (Measure.pi fun _ => ν) → red ψ ν w β E (insert e I) Φ x = ∫ s, red ψ ν w β E I Φ (x + Matrix.single e.1 e.2 (s - x e.1 e.2)) ∂ν := by
  intro k _ _ _ _ _ _ ψ ν hψ hν R Q _ _ _ _ w β E I e hE hI Φ x hint
  haveI := secondCountable k
  haveI := t2Space k
  haveI : LocallyCompactSpace k := inferInstance
  haveI : SigmaFinite ν := inferInstance
  have hmp := measurePreserving_adjoin ν I e hI
  have hfill : ∀ p : k × (I → k), fillAt β E (insert e I) x
      (fun i => if h : i.1 ∈ I then p.2 ⟨i.1, h⟩ else p.1) =
      fillAt β E I (x + Matrix.single e.1 e.2 (p.1 - x e.1 e.2)) p.2 := by
    intro p
    obtain ⟨r₀, q₀⟩ := e
    ext r q
    by_cases h1 : (r, q) ∈ I
    · simp [fillAt, h1]
    · by_cases h2 : (r, q) = (r₀, q₀)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
        simp [fillAt, h1, hE]
      · have h3 : (r, q) ∉ insert (r₀, q₀) I := by
          rw [Finset.mem_insert, not_or]; exact ⟨h2, h1⟩
        have h4 : ¬ (r₀ = r ∧ q₀ = q) := by rintro ⟨rfl, rfl⟩; exact h2 rfl
        simp only [fillAt, Matrix.of_apply, dif_neg h1, dif_neg h3, Matrix.add_apply, Matrix.single_apply,
          if_neg h4, add_zero]
  have h1 := hmp.integrable_comp_of_integrable hint
  unfold red
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hint.1)]
  refine (integral_prod _ h1).trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  exact congrArg (fun t => Φ t * (ψ (-w t) : ℂ)) (hfill (s, y))

theorem exists_subgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → ∀ (e : R × Q) (c : k), ∃ U : AddSubgroup k, IsOpen (U : Set k) ∧ IsCompact (U : Set k) ∧ ∀ u ∈ U, ψ (u * c) = 1 ∧ ∀ t, Φ (t + Matrix.single e.1 e.2 u) = Φ t := by
  intro k _ _ _ _ ψ hψ R Q _ _ _ _ Φ hΦ e c
  have hs : Continuous fun u : k => Matrix.single e.1 e.2 u := by
    refine continuous_matrix fun r q => ?_
    simp only [Matrix.single_apply]
    by_cases h : e.1 = r ∧ e.2 = q
    · simp only [if_pos h]; fun_prop
    · simp only [if_neg h]; fun_prop
  have h1 : ∀ᶠ u in 𝓝 (0 : k), ∀ z ∈ tsupport Φ, Φ (z + Matrix.single e.1 e.2 u) = Φ z := by
    refine IsCompact.eventually_forall_of_forall_eventually hΦ.2 fun z _ => ?_
    have h2 : IsLocallyConstant fun q : k × Matrix R Q k => (Φ (q.2 + Matrix.single e.1 e.2 q.1), Φ q.2) :=
      (hΦ.1.comp_continuous (continuous_snd.add (hs.comp continuous_fst))).prodMk
        (hΦ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, z)] with q hq
    simp only [Prod.mk.injEq, Matrix.single_zero, add_zero] at hq
    rw [hq.1, hq.2]
  obtain ⟨s₀, hs₀⟩ := exists_cball_addChar_eq_one ψ hψ
  have h3 : ∀ᶠ u in 𝓝 (0 : k), ψ (u * c) = 1 := by
    have : (fun u : k => u * c) ⁻¹' cball s₀ ∈ 𝓝 (0 : k) :=
      ((isOpen_cball s₀).preimage (by fun_prop)).mem_nhds (by simp [cball])
    filter_upwards [this] with u hu using hs₀ _ hu
  obtain ⟨s, hUs⟩ := exists_cball_subset (h1.and h3)
  refine ⟨HaarFactor.cballSub s, isOpen_cball s, isCompact_cball s, fun u hu => ⟨(hUs hu).2, fun z => ?_⟩⟩
  by_cases hz : z ∈ tsupport Φ
  · exact (hUs hu).1 z hz
  by_cases hz' : z + Matrix.single e.1 e.2 u ∈ tsupport Φ
  · have := (hUs (neg_mem_cball hu)).1 _ hz'
    rw [add_assoc, ← Matrix.single_add, add_neg_cancel, Matrix.single_zero, add_zero] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']

theorem exists_representatives : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R Q : Type) [Fintype R] [Fintype Q] (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → ∀ (U : AddSubgroup k), IsOpen (U : Set k) → ∀ e : R × Q, ∃ S : Finset k, (∀ a ∈ S, ∀ b ∈ S, a - b ∈ U → a = b) ∧ ∀ t : Matrix R Q k, Φ t ≠ 0 → ∃ a ∈ S, t e.1 e.2 - a ∈ U := by
  intro k _ _ _ _ R Q _ _ Φ hΦ U hU e
  classical
  have hK : IsCompact ((fun t : Matrix R Q k => t e.1 e.2) '' tsupport Φ) := hΦ.2.image (by fun_prop)
  obtain ⟨T, -, hT⟩ := hK.elim_nhds_subcover (fun a => (fun b => b - a) ⁻¹' (U : Set k))
    (fun a _ => (hU.preimage (by fun_prop)).mem_nhds (by simp))
  refine ⟨T.image fun a : k => (a : k ⧸ U).out, ?_, fun t ht => ?_⟩
  · intro a ha b hb hab
    obtain ⟨a', -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨b', -, rfl⟩ := Finset.mem_image.1 hb
    have := QuotientAddGroup.eq_iff_sub_mem.mpr hab
    rw [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at this
    rw [this]
  · obtain ⟨a, ha, hta⟩ := Set.mem_iUnion₂.mp (hT ⟨t, subset_tsupport Φ ht, rfl⟩)
    refine ⟨_, Finset.mem_image.mpr ⟨a, ha, rfl⟩, QuotientAddGroup.eq_iff_sub_mem.mp ?_⟩
    rw [QuotientAddGroup.out_eq']
    exact QuotientAddGroup.eq_iff_sub_mem.mpr hta

theorem integral_cosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (U : AddSubgroup k), IsOpen (U : Set k) → IsCompact (U : Set k) → ∀ (S : Finset k), (∀ a ∈ S, ∀ b ∈ S, a - b ∈ U → a = b) → ∀ h : k → ℂ, (∀ s u, u ∈ U → h (s + u) = h s) → (∀ s, h s ≠ 0 → ∃ a ∈ S, s - a ∈ U) → ∫ s, h s ∂ν = ((ν (U : Set k)).toReal : ℂ) * ∑ a ∈ S, h a := by
  intro k _ _ _ _ _ _ ν hν U hUo hUc S hS h hinv hsupp
  haveI := secondCountable k
  haveI := t2Space k
  have he := HaarFactor.integrable_of_SB ν (HaarFactor.ind_mem hUo hUc)
  have hshift : ∀ c : k, ∫ a, (U : Set k).indicator (fun _ => (1 : ℂ)) (a - c) ∂ν = (ν.real (U : Set k) : ℂ) := by
    intro c
    rw [integral_sub_right_eq_self (fun a => (U : Set k).indicator (fun _ => (1 : ℂ)) a) c,
      integral_indicator_const _ hUo.measurableSet]
    simp
  have hT : ∀ s, h s = ∑ a ∈ S, h a * (U : Set k).indicator (fun _ => (1 : ℂ)) (s - a) := by
    intro s
    have hv : ∀ a, s - a ∈ U → h s = h a := fun a ha => by rw [← hinv a _ ha, add_sub_cancel]
    by_cases hs : h s = 0
    · rw [hs]
      refine (Finset.sum_eq_zero fun a _ => ?_).symm
      by_cases ha : s - a ∈ U
      · rw [← hv a ha, hs, zero_mul]
      · rw [Set.indicator_of_notMem (show s - a ∉ (U : Set k) from ha), mul_zero]
    · obtain ⟨a, ha, hsa⟩ := hsupp s hs
      rw [Finset.sum_eq_single a]
      · rw [Set.indicator_of_mem (show s - a ∈ (U : Set k) from hsa), mul_one, hv a hsa]
      · intro b hb hba
        rw [Set.indicator_of_notMem, mul_zero]
        intro hsb
        have hm := U.sub_mem hsa hsb
        rw [sub_sub_sub_cancel_left] at hm
        exact hba (hS b hb a ha hm)
      · exact fun ha' => absurd ha ha'
  rw [integral_congr_ae (Filter.Eventually.of_forall hT),
    integral_finset_sum _ fun q _ => (he.comp_sub_right _).const_mul _]
  simp only [integral_const_mul, hshift, ← Finset.sum_mul]
  rw [mul_comm]
  rfl

theorem indicator_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R Q : Type) [Fintype R] [Fintype Q] (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → ∀ (U : AddSubgroup k), IsOpen (U : Set k) → ∀ (e : R × Q) (a : k), Set.indicator {t : Matrix R Q k | t e.1 e.2 - a ∈ U} Φ ∈ SB (Matrix R Q k) := by
  intro k _ _ _ _ R Q _ _ Φ hΦ U hU e a
  have hc : Continuous fun t : Matrix R Q k => t e.1 e.2 - a := by fun_prop
  have hcl : IsClopen {t : Matrix R Q k | t e.1 e.2 - a ∈ U} :=
    ⟨(U.isClosed_of_isOpen hU).preimage hc, hU.preimage hc⟩
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
    HasCompactSupport.intro hΦ.2 fun y hy => ?_⟩
  · by_cases hx : x ∈ {t : Matrix R Q k | t e.1 e.2 - a ∈ U}
    · filter_upwards [hcl.isOpen.mem_nhds hx, hΦ.1.eventually_eq x] with z hz hz'
      exact (Set.indicator_of_mem (s := {t : Matrix R Q k | t e.1 e.2 - a ∈ U}) hz Φ).trans
        (hz'.trans (Set.indicator_of_mem hx Φ).symm)
    · filter_upwards [hcl.compl.isOpen.mem_nhds hx] with z hz
      exact (Set.indicator_of_notMem (s := {t : Matrix R Q k | t e.1 e.2 - a ∈ U}) hz Φ).trans
        (Set.indicator_of_notMem hx Φ).symm
  · exact Set.indicator_apply_eq_zero.mpr fun _ => image_eq_zero_of_notMem_tsupport hy

theorem red_shift : ∀ (k : Type) [Field k] [TopologicalSpace k] [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → e ∉ I → ∀ (Φ : Matrix R Q k → ℂ) (u : k), (∀ t, Φ (t + Matrix.single e.1 e.2 u) = Φ t) → ψ (u * w (Matrix.single e.1 e.2 1)) = 1 → ∀ x, red ψ ν w β E I Φ (x + Matrix.single e.1 e.2 u) = red ψ ν w β E I Φ x := by
  intro k _ _ _ ψ ν R Q _ _ _ _ w β E I e hE hI Φ u hΦ hψ x
  have hw : w (Matrix.single e.1 e.2 u) = u * w (Matrix.single e.1 e.2 1) := by
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have h1 : ψ (-w (Matrix.single e.1 e.2 u)) = 1 := by rw [AddChar.map_neg_eq_inv, hw, hψ, inv_one]
  unfold red
  simp only [fill_add_single β E I x _ e hI hE u, hΦ, map_add, neg_add, AddChar.map_add_eq_mul, h1, mul_one]

theorem red_indicator : ∀ (k : Type) [Field k] [TopologicalSpace k] [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → e ∉ I → ∀ (Φ : Matrix R Q k → ℂ) (A : Set k) (x : Matrix R Q k), red ψ ν w β E I (Set.indicator {t : Matrix R Q k | t e.1 e.2 ∈ A} Φ) x = Set.indicator {z : Matrix R Q k | z e.1 e.2 ∈ A} (red ψ ν w β E I Φ) x := by
  intro k _ _ _ ψ ν R Q _ _ _ _ w β E I e hE hI Φ A x
  by_cases hx : x e.1 e.2 ∈ A
  · rw [Set.indicator_of_mem (show x ∈ {z : Matrix R Q k | z e.1 e.2 ∈ A} from hx)]
    unfold red
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [Set.indicator_of_mem]
    show fillAt β E I x y e.1 e.2 ∈ A
    rwa [fill_entry β E I x y e hI hE]
  · rw [Set.indicator_of_notMem (show x ∉ {z : Matrix R Q k | z e.1 e.2 ∈ A} from hx)]
    unfold red
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [Set.indicator_of_notMem, zero_mul, Pi.zero_apply]
    show ¬ fillAt β E I x y e.1 e.2 ∈ A
    rwa [fill_entry β E I x y e hI hE]

theorem red_support : ∀ (k : Type) [Field k] [TopologicalSpace k] [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → e ∉ I → ∀ (Φ : Matrix R Q k → ℂ) (x : Matrix R Q k), red ψ ν w β E I Φ x ≠ 0 → ∃ t, Φ t ≠ 0 ∧ t e.1 e.2 = x e.1 e.2 := by
  intro k _ _ _ ψ ν R Q _ _ _ _ w β E I e hE hI Φ x hx
  by_contra hne
  refine hx (integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_))
  have : Φ (fillAt β E I x y) = 0 := by
    by_contra h
    exact hne ⟨_, h, fill_entry β E I x y e hI hE⟩
  simp [this]

theorem integrate_entry : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → GlobalTheory.PartRed.Kills L ψ ν w β E I → GlobalTheory.PartRed.IntLaw L ψ ν w β E I e → GlobalTheory.PartRed.Kills L ψ ν w β E (insert e I) := by
  intro k _ _ _ _ _ _ ψ ν hψ hν R Q _ _ _ _ M _ _ L w β E I e heE hK hInt
  by_cases heI : e ∈ I
  · rwa [Finset.insert_eq_of_mem heI]
  intro Φ hΦ
  obtain ⟨U, hUo, hUc, hU⟩ := exists_subgroup k ψ hψ R Q Φ.1 Φ.2 e (w (Matrix.single e.1 e.2 1))
  obtain ⟨S, hSd, hS⟩ := exists_representatives k R Q Φ.1 Φ.2 U hUo e
  have hsh : ∀ x (u : k), u ∈ U → red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 u) = red ψ ν w β E I Φ.1 x :=
    fun x u hu => red_shift k ψ ν R Q w β E I e heE heI Φ.1 u (hU u hu).2 (hU u hu).1 x
  have hlin : ∀ (f : k → Matrix R Q k → ℂ), (∀ a, f a ∈ SB (Matrix R Q k)) → ∀ x,
      red ψ ν w β E I (∑ a ∈ S, f a) x = ∑ a ∈ S, red ψ ν w β E I (f a) x := by
    intro f hf x
    unfold red
    simp only [Finset.sum_apply, Finset.sum_mul]
    exact integral_finset_sum S fun a _ => integrable_red k ψ ν hψ hν R Q w β E I (f a) (hf a) x
  have hsum : ∀ x, ∑ a ∈ S, red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 (a - x e.1 e.2)) = 0 := by
    intro x
    have h0 : red ψ ν w β E (insert e I) Φ.1 x = 0 := congrFun hΦ x
    rw [red_insert k ψ ν hψ hν R Q w β E I e heE heI Φ.1 x
      (integrable_red k ψ ν hψ hν R Q w β E (insert e I) Φ.1 Φ.2 x)] at h0
    rw [integral_cosets k ν hν U hUo hUc S hSd
      (fun s => red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 (s - x e.1 e.2))) ?_ ?_] at h0
    · have h1 : ν (U : Set k) ≠ 0 := hUo.measure_ne_zero ν ⟨0, U.zero_mem⟩
      have h2 : ν (U : Set k) ≠ ⊤ := hUc.measure_lt_top.ne
      have hpos : ((ν (U : Set k)).toReal : ℂ) ≠ 0 := by
        exact_mod_cast (ENNReal.toReal_pos h1 h2).ne'
      exact (mul_eq_zero.1 h0).resolve_left hpos
    · intro s u hu
      rw [show s + u - x e.1 e.2 = (s - x e.1 e.2) + u by ring, Matrix.single_add, ← add_assoc]
      exact hsh _ u hu
    · intro s hs
      obtain ⟨t, ht, hte⟩ := red_support k ψ ν R Q w β E I e heE heI Φ.1 _ hs
      obtain ⟨a, ha, hta⟩ := hS t ht
      refine ⟨a, ha, ?_⟩
      have hxe : (x + Matrix.single e.1 e.2 (s - x e.1 e.2)) e.1 e.2 = s := by
        rw [Matrix.add_apply, Matrix.single_apply_same, add_sub_cancel]
      rw [hte, hxe] at hta
      exact hta
  let Φc : k → SB (Matrix R Q k) := fun a =>
    ⟨Set.indicator {t : Matrix R Q k | t e.1 e.2 - a ∈ U} Φ.1, indicator_mem k R Q Φ.1 Φ.2 U hUo e a⟩
  have hcov : ∑ a ∈ S, Φc a = Φ := by
    apply Subtype.ext
    funext t
    rw [Submodule.coe_sum, Finset.sum_apply]
    by_cases ht : Φ.1 t = 0
    · rw [ht]
      exact Finset.sum_eq_zero fun a _ => Set.indicator_apply_eq_zero.mpr fun _ => ht
    · obtain ⟨a, ha, hta⟩ := hS t ht
      rw [Finset.sum_eq_single a]
      · exact Set.indicator_of_mem (s := {t : Matrix R Q k | t e.1 e.2 - a ∈ U}) hta Φ.1
      · intro b hb hba
        refine Set.indicator_of_notMem (s := {t : Matrix R Q k | t e.1 e.2 - b ∈ U}) ?_ Φ.1
        intro htb
        have hm := U.sub_mem hta htb
        rw [sub_sub_sub_cancel_left] at hm
        exact hba (hSd b hb a ha hm)
      · intro ha'
        exact absurd ha ha'
  choose Φ' hΦ'L hΦ'r using fun a => hInt a (Φc a)
  have hred' : ∀ a x, red ψ ν w β E I (Φ' a).1 x =
      Set.indicator {z : Matrix R Q k | z e.1 e.2 ∈ (U : Set k)}
        (fun z => red ψ ν w β E I Φ.1 (z + Matrix.single e.1 e.2 (a - z e.1 e.2))) x := by
    intro a x
    rw [hΦ'r a x]
    have h8 := red_indicator k ψ ν R Q w β E I e heE heI Φ.1 {s : k | s - a ∈ U} (x + Matrix.single e.1 e.2 a)
    have hxe : (x + Matrix.single e.1 e.2 a) e.1 e.2 - a = x e.1 e.2 := by
      simp [Matrix.add_apply, Matrix.single_apply]
    change red ψ ν w β E I (Set.indicator {t : Matrix R Q k | t e.1 e.2 ∈ {s : k | s - a ∈ U}} Φ.1) _ = _
    rw [h8]
    by_cases hx : x e.1 e.2 ∈ U
    · rw [Set.indicator_of_mem (show (x + Matrix.single e.1 e.2 a) ∈ {z : Matrix R Q k | z e.1 e.2 ∈ {s : k | s - a ∈ U}} by
          show (x + Matrix.single e.1 e.2 a) e.1 e.2 - a ∈ U
          rw [hxe]; exact hx),
        Set.indicator_of_mem (show x ∈ {z : Matrix R Q k | z e.1 e.2 ∈ (U : Set k)} from hx)]
      rw [← hsh (x + Matrix.single e.1 e.2 (a - x e.1 e.2)) (x e.1 e.2) hx, add_assoc, ← Matrix.single_add,
        sub_add_cancel]
    · rw [Set.indicator_of_notMem (show (x + Matrix.single e.1 e.2 a) ∉ {z : Matrix R Q k | z e.1 e.2 ∈ {s : k | s - a ∈ U}} by
          show ¬ ((x + Matrix.single e.1 e.2 a) e.1 e.2 - a ∈ U)
          rw [hxe]; exact hx),
        Set.indicator_of_notMem (show x ∉ {z : Matrix R Q k | z e.1 e.2 ∈ (U : Set k)} from hx)]
  have hΞ : red ψ ν w β E I (∑ a ∈ S, Φ' a).1 = 0 := by
    funext x
    rw [Submodule.coe_sum, hlin (fun a => (Φ' a).1) (fun a => (Φ' a).2) x]
    simp only [hred']
    by_cases hx : x e.1 e.2 ∈ U
    · simp only [Set.indicator_of_mem (show x ∈ {z : Matrix R Q k | z e.1 e.2 ∈ (U : Set k)} from hx)]
      exact hsum x
    · simp only [Set.indicator_of_notMem (show x ∉ {z : Matrix R Q k | z e.1 e.2 ∈ (U : Set k)} from hx),
        Finset.sum_const_zero, Pi.zero_apply]
  have hL := hK (∑ a ∈ S, Φ' a) hΞ
  rw [← hcov, map_sum]
  rw [map_sum] at hL
  rw [← hL]
  exact Finset.sum_congr rfl fun a _ => (hΦ'L a).symm

end GlobalTheory.PartRed.IntEntry

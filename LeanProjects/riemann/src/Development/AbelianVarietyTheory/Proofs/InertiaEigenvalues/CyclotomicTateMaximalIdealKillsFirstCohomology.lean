import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerTraceAlmostSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplexStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsRest
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc.AveragingRankOne

theorem exists_reps {G : Type*} [Group G] (H U V : Subgroup G) [U.FiniteIndex]
    (hV : ∀ g ∈ H, g ∈ V ↔ g ∈ U) :
    ∃ S : Finset G, (∀ s ∈ S, s ∈ H) ∧ ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ V := by
  classical
  letI : Fintype (H ⧸ U.subgroupOf H) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : H ⧸ U.subgroupOf H => (q.out : G)), ?_, ?_⟩
  · intro s hs
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
    exact q.out.2
  · intro h hh
    have key : ∀ q : H ⧸ U.subgroupOf H, (q.out : G)⁻¹ * h ∈ V ↔ q = ((⟨h, hh⟩ : H) : H ⧸ U.subgroupOf H) := by
      intro q
      rw [hV _ (H.mul_mem (H.inv_mem q.out.2) hh)]
      conv_rhs => rw [← q.out_eq']
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      rfl
    refine ⟨(((⟨h, hh⟩ : H) : H ⧸ U.subgroupOf H).out : G),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (key _).2 rfl⟩, ?_⟩
    rintro s ⟨hs, hs'⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
    rw [(key q).1 hs']

variable {l : ℕ} [Fact l.Prime]

theorem exists_field (F : IntermediateField ℚ_[l] (Om l)) (W : Set (GQ l)) (hW : W ∈ nhds (1 : GQ l)) :
    ∃ (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)), F ≤ L ∧
      (∀ h ∈ F.fixingSubgroup, ∀ x ∈ L, h x ∈ L) ∧ (∀ s ∈ S, s ∈ F.fixingSubgroup) ∧
      (∀ h ∈ F.fixingSubgroup, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) ∧
      ∀ g ∈ L.fixingSubgroup, g ∈ W := by
  obtain ⟨E, hfd, hN, hE⟩ := (krullTopology_mem_nhds_one_iff_of_normal ℚ_[l] (Om l) W).1 hW
  haveI : E.fixingSubgroup.FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen E.fixingSubgroup E.fixingSubgroup_isOpen
    exact Subgroup.finiteIndex_of_finite_quotient
  have hsup : (F ⊔ E).fixingSubgroup = F.fixingSubgroup ⊓ E.fixingSubgroup :=
    IntermediateField.fixingSubgroup_sup
  obtain ⟨S, hS, hS'⟩ := exists_reps F.fixingSubgroup E.fixingSubgroup (F ⊔ E).fixingSubgroup
    (fun g hg => by rw [hsup, Subgroup.mem_inf]; exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩)
  refine ⟨F ⊔ E, S, le_sup_left, ?_, hS, hS', fun g hg => hE ?_⟩
  · intro h hh
    have : F ⊔ E ≤ (F ⊔ E).comap (h : Om l →ₐ[ℚ_[l]] Om l) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · have h1 : h x = x := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x hx
        change h x ∈ F ⊔ E
        rw [h1]; exact (le_sup_left : F ≤ F ⊔ E) hx
      · change h x ∈ F ⊔ E
        have h1 := AlgEquiv.restrictNormal_commutes h E ⟨x, hx⟩
        have h2 : h x ∈ E := by
          have : h x = (h.restrictNormal E ⟨x, hx⟩ : E) := h1.symm
          rw [this]; exact Subtype.property _
        exact (le_sup_right : E ≤ F ⊔ E) h2
    exact fun x hx => this hx
  · rw [hsup] at hg; exact hg.2

theorem average {G C : Type*} [Group G] [NormedField C] [IsUltrametricDist C]
    (act : G →* (C ≃+* C)) (hn : ∀ g y, ‖act g y‖ = ‖y‖) (H V : Subgroup G) (S : Finset G)
    (hS : ∀ s ∈ S, s ∈ H) (hS' : ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ V)
    (a b : C) (hb : ‖b‖ ≤ 1) (hbV : ∀ g ∈ V, act g b = b) (hab : ∑ s ∈ S, act s b = a)
    (c : G → C) (hc : ∀ g ∈ H, ∀ h ∈ H, c (g * h) = c g + act g (c h))
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε : 0 ≤ ε) (ht : ∀ g ∈ H, ‖c g‖ ≤ t)
    (hV : ∀ g ∈ H, g ∈ V → ‖c g‖ ≤ ε) :
    ∃ x : C, ‖x‖ ≤ t ∧ ∀ h ∈ H, ‖a * c h - (act h x - x)‖ ≤ ε := by
  first
  | exact @_root_.GlobalTheory.PermutationExistence.main
  | exact _root_.GlobalTheory.PermutationExistence.main
  | (apply _root_.GlobalTheory.PermutationExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PermutationExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PermutationExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PermutationExistence.main ..)

theorem step (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (hact : IsActC act) (K : FinExt l)
    (a : PadicComplex l) (ha : a ∈ inC (Kinf K)) (ha1 : ‖a‖ < 1) (c : GQ l → PadicComplex l)
    (hcont : ContinuousOn c (Hinf K))
    (hc : ∀ g ∈ Hinf K, ∀ h ∈ Hinf K, c (g * h) = c g + act g (c h))
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε : 0 < ε) (ht : ∀ g ∈ Hinf K, ‖c g‖ ≤ t) :
    ∃ x : PadicComplex l, ‖x‖ ≤ t ∧ ∀ h ∈ Hinf K, ‖a * c h - (act h x - x)‖ ≤ ε := by
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  have hc1 : c 1 = 0 := by
    have := hc 1 (one_mem _) 1 (one_mem _)
    simpa using this
  have hev : ∀ᶠ g in nhdsWithin (1 : GQ l) (Hinf K), ‖c g‖ < ε := by
    have := (hcont 1 (one_mem _)).norm
    refine this.eventually (p := fun r => r < ε) (gt_mem_nhds ?_)
    simpa [hc1] using hε
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨L, S, hL, hst, hS, hS', hW⟩ := exists_field (Kinf K) _ hev
  obtain ⟨b, hbL, hb1, hb⟩ := GlobalTheory.T.cyclotomicTower_trace_almost_surjective l K L S hL hst hS hS' a₀ ha₀ (by simpa using ha1)
  refine average act hact.2 (Hinf K) L.fixingSubgroup S hS hS' _ (b : PadicComplex l)
    (by simpa using hb1) (fun g hg => ?_) ?_ c hc t ε ht0 hε.le ht (fun g hg hg' => (hW g hg' hg).le)
  · rw [hact.1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg b hbL]
  · simp only [hact.1, ← hb]
    exact (map_sum (algebraMap (Om l) (PadicComplex l)) _ _).symm

theorem rank_one (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (hact : IsActC act)
    (K : FinExt l) (a : PadicComplex l) (ha : a ∈ inC (Kinf K)) (ha1 : ‖a‖ < 1)
    (c : GQ l → PadicComplex l) (hcont : ContinuousOn c (Hinf K))
    (hc : ∀ g ∈ Hinf K, ∀ h ∈ Hinf K, c (g * h) = c g + act g (c h))
    (ht : ∀ g ∈ Hinf K, ‖c g‖ ≤ 1) :
    ∃ x : PadicComplex l, ‖x‖ ≤ 1 ∧ ∀ h ∈ Hinf K, a * c h = act h x - x := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact ⟨0, by simp, by simp⟩
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hfix : ∀ g ∈ Hinf K, act g a = a := by
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    intro g hg
    rw [hact.1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg a₀ ha₀]
  let Q : ℕ → PadicComplex l → Prop := fun n y =>
    ‖y‖ ≤ 1 ∧ ∀ h ∈ Hinf K, ‖a * c h - (act h y - y)‖ ≤ ‖a‖ * (1 / 2) ^ n
  have hstep : ∀ n y, Q n y → ∃ y', Q (n + 1) y' ∧ dist y y' ≤ 1 * (1 / 2 : ℝ) ^ n := by
    rintro n y ⟨hy1, hy⟩
    obtain ⟨x, hx, hx'⟩ := step act hact K a ha ha1 (fun g => c g - a⁻¹ * (act g y - y))
      (hcont.sub (continuousOn_const.mul
        ((GlobalTheory.T.continuous_orbit_padicComplex l act hact y).continuousOn.sub continuousOn_const)))
      (fun g hg h hh => by
        simp only [hc g hg h hh, map_mul, map_sub, map_inv₀, hfix g hg, RingAut.mul_apply]
        ring)
      ((1 / 2) ^ n) (‖a‖ * (1 / 2) ^ (n + 1)) (by positivity) (by positivity)
      (fun g hg => by
        have e : c g - a⁻¹ * (act g y - y) = a⁻¹ * (a * c g - (act g y - y)) := by
          field_simp
        rw [e, norm_mul, norm_inv, inv_mul_le_iff₀ hapos]
        exact hy g hg)
    refine ⟨y + x, ⟨?_, fun h hh => ?_⟩, ?_⟩
    · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy1 (hx.trans ?_))
      exact pow_le_one₀ (by norm_num) (by norm_num)
    · have e : a * c h - (act h (y + x) - (y + x)) =
          a * (c h - a⁻¹ * (act h y - y)) - (act h x - x) := by
        rw [map_add]; field_simp; ring
      rw [e]; exact hx' h hh
    · simpa [dist_eq_norm] using hx
  choose! f hfQ hfd using hstep
  let y : ℕ → PadicComplex l := fun n => Nat.rec 0 f n
  have hQ : ∀ n, Q n (y n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [y], fun h hh => ?_⟩
      simpa [y] using mul_le_mul_of_nonneg_left (ht h hh) hapos.le
    | succ n ih => exact hfQ n _ ih
  have hcau : CauchySeq y :=
    cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num) fun n => hfd n _ (hQ n)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨x, le_of_tendsto' hx.norm fun n => (hQ n).1, fun h hh => ?_⟩
  have hiso : Continuous (act h) :=
    (AddMonoidHomClass.isometry_of_norm (act h) (hact.2 h)).continuous
  have h1 : Filter.Tendsto (fun n => ‖a * c h - (act h (y n) - y n)‖) Filter.atTop
      (nhds ‖a * c h - (act h x - x)‖) :=
    (tendsto_const_nhds.sub (((hiso.tendsto x).comp hx).sub hx)).norm
  have h2 : Filter.Tendsto (fun n : ℕ => ‖a‖ * (1 / 2 : ℝ) ^ n) Filter.atTop (nhds (‖a‖ * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
  have := le_of_tendsto_of_tendsto' h1 h2 fun n => (hQ n).2 h hh
  rw [mul_zero, norm_le_zero_iff, sub_eq_zero] at this
  exact this

theorem cyclotomic_maximalIdeal_smul_cocycle_isCoboundary : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ (K : FinExt l) (r : ℕ) (a : PadicComplex l), a ∈ inC (Kinf K) → ‖a‖ < 1 → ∀ c : GQ l → Fin r → PadicComplex l, CocOn (Hinf K) (fun g y k => act g (y k)) (ball l r) c → CobOn (Hinf K) (fun g y k => act g (y k)) (ball l r) (fun g => a • c g) := by
  intro l _ act hact K r a ha ha1 c ⟨h1, h2, h3⟩
  choose x hx hx' using fun k : Fin r => rank_one act hact K a ha ha1 (fun g => c g k)
    ((continuous_apply k).comp_continuousOn h1)
    (fun g hg h hh => congrFun (h3 g hg h hh) k) (fun g hg => h2 g hg k)
  exact ⟨x, hx, fun g hg => funext fun k => hx' k g hg⟩

end GlobalTheory.Cyc.AveragingRankOne

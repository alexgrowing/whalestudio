import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.SchrCyclic

variable {F : Type} [Field F] [NumberField F]

theorem psiLoc_add (ψ : AddChar (AF F) ℂ) (v : Pl F) (a b : Fv F v) :
    psiLoc ψ v (a + b) = psiLoc ψ v a * psiLoc ψ v b := by
  rw [psiLoc, psiLoc, psiLoc, map_add, map_add]; exact AddChar.map_add_eq_mul ψ _ _

theorem psiLoc_zero (ψ : AddChar (AF F) ℂ) (v : Pl F) : psiLoc ψ v 0 = 1 := by
  rw [psiLoc, map_zero, map_zero]; exact AddChar.map_zero_eq_one ψ

theorem mem_of_sep {V Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    (e : Y → V → ℂ) (he : ∀ y a b, e y (a + b) = e y a * e y b)
    (S : Submodule ℂ (V → ℂ)) (hS : ∀ y, ∀ h ∈ S, (fun x => e y x * h x) ∈ S)
    (U : AddSubgroup V) (hU : IsOpen (U : Set V))
    (hsep : ∀ x ∉ U, ∃ y, (∀ u ∈ U, e y u = 1) ∧ e y x ≠ 1)
    {f : V → ℂ} (hf : f ∈ S) (hfc : HasCompactSupport f) :
    (fun x => if x ∈ U then f x else 0) ∈ S := by
  classical
  by_cases hY : Nonempty Y
  swap
  · have hall : ∀ x, x ∈ U := fun x => by
      by_contra h
      obtain ⟨y, -⟩ := hsep x h
      exact hY ⟨y⟩
    convert hf using 1
    funext x
    simp [hall x]
  have := QuotientAddGroup.discreteTopology hU
  have hfin : ((QuotientAddGroup.mk : V → V ⧸ U) '' tsupport f).Finite :=
    (hfc.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  have hsep' : ∀ q : V ⧸ U, ∃ y, q ≠ 0 → (∀ u ∈ U, e y u = 1) ∧ e y q.out ≠ 1 := by
    intro q
    by_cases hq : q = 0
    · exact ⟨Classical.arbitrary _, fun h => (h hq).elim⟩
    · have : q.out ∉ U := fun h => hq (by rw [← QuotientAddGroup.out_eq' q]; exact (QuotientAddGroup.eq_zero_iff _).2 h)
      obtain ⟨y, hy⟩ := hsep _ this
      exact ⟨y, fun _ => hy⟩
  choose y hy using hsep'
  set c : V ⧸ U → ℂ := fun q => e (y q) q.out with hcdef
  set Q := hfin.toFinset.filter (· ≠ 0) with hQ
  have key : ∀ s : Finset (V ⧸ U), (fun x => (∏ q ∈ s, (e (y q) x - c q) / (1 - c q)) * f x) ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hf
    | insert q s hq ih =>
      have h2 := hS (y q) _ ih
      have : (fun x => (∏ r ∈ insert q s, (e (y r) x - c r) / (1 - c r)) * f x) =
          (1 - c q)⁻¹ • (fun x => e (y q) x * ((∏ r ∈ s, (e (y r) x - c r) / (1 - c r)) * f x)) +
          (-(c q) * (1 - c q)⁻¹) • (fun x => (∏ r ∈ s, (e (y r) x - c r) / (1 - c r)) * f x) := by
        funext x
        simp only [Finset.prod_insert hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [this]
      exact S.add_mem (S.smul_mem _ h2) (S.smul_mem _ ih)
  convert key Q using 1
  funext x
  by_cases hx : x ∈ tsupport f
  · by_cases hxU : x ∈ U
    · rw [if_pos hxU, Finset.prod_eq_one, one_mul]
      intro q hq
      have hq0 : q ≠ 0 := (Finset.mem_filter.1 hq).2
      rw [(hy q hq0).1 x hxU, div_self (sub_ne_zero.2 (Ne.symm (hy q hq0).2))]
    · have hq0 : (QuotientAddGroup.mk x : V ⧸ U) ≠ 0 := fun h => hxU ((QuotientAddGroup.eq_zero_iff _).1 h)
      rw [if_neg hxU, Finset.prod_eq_zero (i := (QuotientAddGroup.mk x : V ⧸ U)), zero_mul]
      · exact Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨x, hx, rfl⟩, hq0⟩
      · have hw : -(QuotientAddGroup.mk x : V ⧸ U).out + x ∈ U :=
          QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
        have : e (y (QuotientAddGroup.mk x)) x = c (QuotientAddGroup.mk x) := by
          have h5 : e (y (QuotientAddGroup.mk x)) ((QuotientAddGroup.mk x : V ⧸ U).out +
              (-(QuotientAddGroup.mk x : V ⧸ U).out + x)) = e (y (QuotientAddGroup.mk x)) (QuotientAddGroup.mk x : V ⧸ U).out := by
            rw [he, (hy _ hq0).1 _ hw, mul_one]
          rw [add_neg_cancel_left] at h5
          exact h5
        rw [this, sub_self, zero_div]
  · rw [image_eq_zero_of_notMem_tsupport hx]
    simp

theorem exists_periodic {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    (hB : ∀ N ∈ 𝓝 (0 : V), ∃ W : AddSubgroup V, IsOpen (W : Set V) ∧ (W : Set V) ⊆ N)
    {φ : V → ℂ} (hφ : IsLocallyConstant φ) (hc : HasCompactSupport φ) :
    ∃ N ∈ 𝓝 (0 : V), ∀ W : AddSubgroup V, (W : Set V) ⊆ N → ∀ x, ∀ w ∈ W, φ (x + w) = φ x := by
  classical
  have hK : IsCompact (tsupport φ) := hc
  have hloc : ∀ z : V, ∃ W : AddSubgroup V, IsOpen (W : Set V) ∧ ∀ w ∈ W, φ (z + w) = φ z := by
    intro z
    have ho : IsOpen {u : V | φ (z + u) = φ z} :=
      (hφ.comp_continuous (continuous_const.add continuous_id)).isOpen_fiber (φ z)
    obtain ⟨W, hWo, hWs⟩ := hB _ (ho.mem_nhds (by simp))
    exact ⟨W, hWo, fun w hw => hWs hw⟩
  choose W hWo hW using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z => (fun x => -z + x) ⁻¹' (W z : Set V))
    (fun z => (hWo z).preimage (continuous_const.add continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [(W x).zero_mem]⟩)
  refine ⟨⋂ z ∈ t, (W z : Set V), (Filter.biInter_finset_mem t).2 fun z _ => (hWo z).mem_nhds (W z).zero_mem,
    fun W' hW' => ?_⟩
  have hin : ∀ x ∈ tsupport φ, ∀ w ∈ W', φ (x + w) = φ x := by
    intro x hx w hw
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (ht hx)
    have hwz : w ∈ W z := Set.mem_iInter₂.1 (hW' hw) z hz
    have hxz' : -z + x ∈ W z := hxz
    have e1 := hW z _ ((W z).add_mem hxz' hwz)
    have e2 := hW z _ hxz'
    rw [← add_assoc, add_neg_cancel_left] at e1
    rw [add_neg_cancel_left] at e2
    rw [e1, e2]
  intro x w hw
  by_cases hx : x ∈ tsupport φ
  · exact hin x hx w hw
  · by_cases hxw : x + w ∈ tsupport φ
    · have := hin _ hxw (-w) (W'.neg_mem hw)
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxw]

theorem eq_one_of_pow_near {u : ℂ} (hu : ∀ n : ℕ, ‖u ^ n - 1‖ < 1 / 2) : u = 1 := by
  have key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖u - 1‖ ≤ ‖u ^ 2 ^ k - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : u ^ 2 ^ (k + 1) - 1 = (u ^ 2 ^ k - 1) * (2 + (u ^ 2 ^ k - 1)) := by rw [pow_succ, pow_mul]; ring
      have h2 : (3 / 2 : ℝ) ≤ ‖2 + (u ^ 2 ^ k - 1)‖ := by
        have := norm_sub_norm_le (2 : ℂ) (-(u ^ 2 ^ k - 1))
        rw [norm_neg, sub_neg_eq_add, Complex.norm_two] at this
        linarith [hu (2 ^ k)]
      rw [h1, norm_mul, pow_succ, mul_right_comm]
      exact mul_le_mul ih h2 (by norm_num) (norm_nonneg _)
  by_contra hne
  have hpos : 0 < ‖u - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖u - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ hpos] at hk
  linarith [key k, hu (2 ^ k)]

theorem exists_cond (ψ : AddChar (AF F) ℂ) (v : Pl F) (hc : Continuous (psiLoc ψ v))
    (hn : ∃ x : Fv F v, psiLoc ψ v x ≠ 1) :
    ∃ z : Fv F v, psiLoc ψ v z ≠ 1 ∧ ∀ s : Fv F v, Valued.v s < Valued.v z → psiLoc ψ v s = 1 := by
  classical
  let χA : AddChar (Fv F v) ℂ :=
    { toFun := psiLoc ψ v, map_zero_eq_one' := psiLoc_zero ψ v, map_add_eq_mul' := psiLoc_add ψ v }
  have hsmall : ∃ N ∈ 𝓝 (0 : Fv F v), ∀ s ∈ N, psiLoc ψ v s = 1 := by
    have hc' : Continuous fun s => ‖psiLoc ψ v s - 1‖ := by fun_prop
    have h1 : {s : Fv F v | ‖psiLoc ψ v s - 1‖ < 1 / 2} ∈ 𝓝 0 :=
      (isOpen_lt hc' continuous_const).mem_nhds (by simp [psiLoc_zero])
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 h1
    refine ⟨{x | (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict x < γ},
      (Valued.isClopen_ball _ _).isOpen.mem_nhds (by simp [zero_lt_iff]), fun s hs => ?_⟩
    have hn : ∀ n : ℕ, (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict (n • s) < γ := by
      intro n
      induction n with
      | zero => simp [zero_lt_iff]
      | succ n ih =>
        rw [succ_nsmul]
        exact Valuation.map_add_lt _ ih hs
    refine eq_one_of_pow_near fun n => ?_
    rw [show psiLoc ψ v s ^ n = psiLoc ψ v (n • s) from (AddChar.map_nsmul_eq_pow χA n s).symm]
    exact hγ (hn n)
  obtain ⟨N, hN, hNχ⟩ := hsmall
  have hopen : IsOpen {s : Fv F v | psiLoc ψ v s = 1} := by
    refine isOpen_iff_mem_nhds.2 fun s hs => ?_
    rw [← map_add_left_nhds_zero]
    exact Filter.mem_map.2 (Filter.mem_of_superset hN fun u hu => by
      show psiLoc ψ v (s + u) = 1
      rw [psiLoc_add, show psiLoc ψ v s = 1 from hs, hNχ u hu, one_mul])
  obtain ⟨w, hw⟩ := hn
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hw (psiLoc_zero ψ v)
  have hball : IsCompact {s : Fv F v | Valued.v s ≤ Valued.v w} := by
    have : {s : Fv F v | Valued.v s ≤ Valued.v w} =
        (fun o => w * o) '' (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext s
      constructor
      · intro hs
        refine ⟨s / w, ?_, by field_simp⟩
        rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
        exact div_le_one_of_le₀ hs zero_le'
      · rintro ⟨o, ho, rfl⟩
        show Valued.v (w * o) ≤ Valued.v w
        rw [map_mul]
        exact mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ho)
    rw [this]
    exact (isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)).image
      (continuous_mul_left w)
  set C := {s : Fv F v | Valued.v s ≤ Valued.v w} ∩ {s | psiLoc ψ v s ≠ 1} with hC
  have hCc : IsCompact C := hball.inter_right (show IsClosed {s : Fv F v | psiLoc ψ v s ≠ 1} from hopen.isClosed_compl)
  have hloc : ∀ s ∈ C, {t : Fv F v | Valued.v t = Valued.v s} ∈ 𝓝 s := by
    intro s hs
    have hs0 : s ≠ 0 := fun h => hs.2 (h ▸ psiLoc_zero ψ v)
    have hr : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict s ≠ 0 :=
      (Valuation.ne_zero_iff _).2 hs0
    refine Valued.mem_nhds.2 ⟨Units.mk0 _ hr, fun t ht => ?_⟩
    have h1 : Valued.v (t - s) < Valued.v s := (Valuation.restrict_lt_iff _).1 ht
    exact Valuation.map_eq_of_sub_lt _ h1
  obtain ⟨t, htC, hcov⟩ := hCc.elim_nhds_subcover _ hloc
  have hwC : w ∈ C := ⟨show Valued.v w ≤ Valued.v w from le_rfl, hw⟩
  have htne : t.Nonempty := by
    obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.1 (hcov hwC)
    exact ⟨x, hx⟩
  obtain ⟨z, hzt, hzmin⟩ := t.exists_min_image (fun x => Valued.v x) htne
  refine ⟨z, (htC z hzt).2, fun s hs => ?_⟩
  by_contra hχs
  by_cases hsw : Valued.v s ≤ Valued.v w
  · obtain ⟨x, hx, hsx⟩ := Set.mem_iUnion₂.1 (hcov ⟨hsw, hχs⟩)
    have h1 : Valued.v z ≤ Valued.v x := hzmin x hx
    have h2 : Valued.v s = Valued.v x := hsx
    rw [← h2] at h1
    exact absurd hs (not_lt.2 h1)
  · exact hsw (le_trans hs.le (htC z hzt).1)

theorem exists_sub (ψ : AddChar (AF F) ℂ) (v : Pl F) {z : Fv F v} (hz : psiLoc ψ v z ≠ 1)
    (hzs : ∀ s : Fv F v, Valued.v s < Valued.v z → psiLoc ψ v s = 1) {κ : Type} [Fintype κ]
    {N : Set (κ → Fv F v)} (hN : N ∈ 𝓝 (0 : κ → Fv F v)) :
    ∃ U : AddSubgroup (κ → Fv F v), IsOpen (U : Set (κ → Fv F v)) ∧ (U : Set (κ → Fv F v)) ⊆ N ∧
      ∀ x ∉ U, ∃ t, (∀ u ∈ U, psiLoc ψ v (u ⬝ᵥ t) = 1) ∧ psiLoc ψ v (x ⬝ᵥ t) ≠ 1 := by
  have hN' : N ∈ Filter.pi fun _ : κ => 𝓝 (0 : Fv F v) := by simpa [nhds_pi] using hN
  obtain ⟨⟨I, γ⟩, -, hsub⟩ := (Filter.hasBasis_pi fun _ : κ => Valued.hasBasis_nhds_zero (Fv F v) (WithZero (Multiplicative ℤ))).mem_iff.1 hN'
  have hz0 : z ≠ 0 := by rintro rfl; exact hz (psiLoc_zero ψ v)
  let U : AddSubgroup (κ → Fv F v) :=
    { carrier := {x | ∀ i, (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict (x i) < ((γ i : _) : _)}
      zero_mem' := fun i => by
        simp only [Pi.zero_apply, map_zero]
        exact zero_lt_iff.2 (γ i).ne_zero
      add_mem' := fun hx hy i => Valuation.map_add_lt _ (hx i) (hy i)
      neg_mem' := fun hx i => by simpa only [Pi.neg_apply, Valuation.map_neg] using hx i }
  refine ⟨U, ?_, fun x hx => hsub fun i _ => hx i, fun x hx => ?_⟩
  · have : (U : Set (κ → Fv F v)) = Set.univ.pi fun i => {y | (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict y < ((γ i : _) : _)} := by
      ext x; simp [U]
    rw [this]
    exact isOpen_set_pi Set.finite_univ fun i _ => (Valued.isClopen_ball _ _).isOpen
  · have hx' : ∃ i, ((γ i : _) : _) ≤ (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict (x i) := by
      by_contra h
      push_neg at h
      exact hx h
    obtain ⟨i, hi⟩ := hx'
    have hxi : x i ≠ 0 := by
      intro h
      rw [h, map_zero] at hi
      exact (γ i).ne_zero (le_antisymm hi zero_le')
    refine ⟨Pi.single i (z / x i), fun u hu => ?_, ?_⟩
    · rw [dotProduct_single]
      apply hzs
      have h1 : Valued.v (u i) < Valued.v (x i) := (Valuation.restrict_lt_iff _).1 (lt_of_lt_of_le (hu i) hi)
      have h2 : Valued.v (u i / x i) < 1 := by
        rw [map_div₀]
        exact (div_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hxi))).2 h1
      rw [show u i * (z / x i) = (u i / x i) * z by ring, map_mul]
      exact mul_lt_of_lt_one_left (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hz0)) h2
    · rw [dotProduct_single, mul_div_cancel₀ _ hxi]
      exact hz

theorem mem_span_locOp : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : Pl F), Continuous (psiLoc ψ v) →
    (∃ x : Fv F v, psiLoc ψ v x ≠ 1) → ∀ {κ : Type} [Fintype κ] (φ₀ φ : (κ → Fv F v) → ℂ), φ₀ ∈ SB _ → φ₀ ≠ 0 →
    φ ∈ SB _ → φ ∈ Submodule.span ℂ (Set.range fun p => GlobalTheory.FinComm.locOp ψ v p φ₀) := by
  intro F _ _ ψ v hc hn κ _ φ₀ φ h0 hne hφ
  set S := Submodule.span ℂ (Set.range fun p => GlobalTheory.FinComm.locOp ψ v p φ₀) with hS
  have htr : ∀ a, ∀ h ∈ S, (fun x => h (x + a)) ∈ S := by
    intro a h hh
    induction hh using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨⟨x₁, y⟩, rfl⟩ := hg
      have : (fun x => GlobalTheory.FinComm.locOp ψ v (x₁, y) φ₀ (x + a)) =
          psiLoc ψ v (a ⬝ᵥ y / 2) • GlobalTheory.FinComm.locOp ψ v (x₁ + a, y) φ₀ := by
        funext x
        simp only [GlobalTheory.FinComm.locOp, Pi.smul_apply, smul_eq_mul]
        rw [← mul_assoc, ← psiLoc_add]
        congr 1
        · congr 1
          simp only [add_dotProduct]
          have h2 : (2 : Fv F v) ≠ 0 := by
            have := (map_ne_zero (algebraMap F (Fv F v))).2 (two_ne_zero (α := F))
            rwa [map_ofNat] at this
          linear_combination (-(a ⬝ᵥ y)) * inv_mul_cancel₀ h2
        · congr 1
          abel
      rw [this]
      exact S.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
    | zero => exact S.zero_mem
    | add g₁ g₂ _ _ ih₁ ih₂ => exact S.add_mem ih₁ ih₂
    | smul c g _ ih => exact S.smul_mem c ih
  have hmod : ∀ t, ∀ h ∈ S, (fun x => psiLoc ψ v (x ⬝ᵥ t) * h x) ∈ S := by
    intro t h hh
    induction hh using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨⟨x₁, y⟩, rfl⟩ := hg
      have : (fun x => psiLoc ψ v (x ⬝ᵥ t) * GlobalTheory.FinComm.locOp ψ v (x₁, y) φ₀ x) =
          psiLoc ψ v (-(x₁ ⬝ᵥ t) / 2) • GlobalTheory.FinComm.locOp ψ v (x₁, y + t) φ₀ := by
        funext x
        simp only [GlobalTheory.FinComm.locOp, Pi.smul_apply, smul_eq_mul]
        rw [← mul_assoc, ← mul_assoc, ← psiLoc_add, ← psiLoc_add]
        congr 2
        simp only [dotProduct_add]
        ring
      rw [this]
      exact S.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
    | zero =>
      convert S.zero_mem using 1
      funext x
      simp
    | add g₁ g₂ _ _ ih₁ ih₂ =>
      convert S.add_mem ih₁ ih₂ using 1
      funext x
      simp [mul_add]
    | smul c g _ ih =>
      convert S.smul_mem c ih using 1
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  obtain ⟨z, hz, hzs⟩ := exists_cond ψ v hc hn
  have hB : ∀ N ∈ 𝓝 (0 : κ → Fv F v), ∃ W : AddSubgroup (κ → Fv F v), IsOpen (W : Set (κ → Fv F v)) ∧ (W : Set (κ → Fv F v)) ⊆ N := by
    intro N hN
    obtain ⟨U, h1, h2, -⟩ := exists_sub ψ v hz hzs hN
    exact ⟨U, h1, h2⟩
  obtain ⟨c, hc0⟩ : ∃ c, φ₀ c ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  set f : (κ → Fv F v) → ℂ := fun x => φ₀ (x + c) with hfdef
  have hfS : f ∈ S := by
    have : f = GlobalTheory.FinComm.locOp ψ v (c, 0) φ₀ := by
      funext x
      simp [f, GlobalTheory.FinComm.locOp, psiLoc_zero]
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩
  have hfc : HasCompactSupport f := h0.2.comp_homeomorph (Homeomorph.addRight c)
  have hfl : IsLocallyConstant f := h0.1.comp_continuous (continuous_add_right c)
  have hf0 : f 0 ≠ 0 := by simpa [f] using hc0
  have hN1 : {u | f u = f 0} ∈ 𝓝 (0 : κ → Fv F v) := (hfl.isOpen_fiber (f 0)).mem_nhds rfl
  obtain ⟨N2, hN2, hper⟩ := exists_periodic hB hφ.1 hφ.2
  obtain ⟨U, hUo, hUs, hsep⟩ := exists_sub ψ v hz hzs (Filter.inter_mem hN1 hN2)
  have h1U : (fun x => if x ∈ U then f x else 0) ∈ S :=
    mem_of_sep (fun t x => psiLoc ψ v (x ⬝ᵥ t)) (fun t a b => by rw [add_dotProduct, psiLoc_add]) S hmod U hUo
      hsep hfS hfc
  have hind : ∀ a : κ → Fv F v, (fun x => if x + a ∈ U then (1 : ℂ) else 0) ∈ S := by
    intro a
    have h2 : (fun x => if x ∈ U then (1 : ℂ) else 0) ∈ S := by
      have : (fun x => if x ∈ U then (1 : ℂ) else 0) = (f 0)⁻¹ • (fun x => if x ∈ U then f x else 0) := by
        funext x
        by_cases hx : x ∈ U
        · have : f x = f 0 := (hUs hx).1
          simp only [hx, if_true, Pi.smul_apply, smul_eq_mul, this, inv_mul_cancel₀ hf0]
        · simp [hx]
      rw [this]
      exact S.smul_mem _ h1U
    exact htr a _ h2
  have hper' : ∀ x, ∀ w ∈ U, φ (x + w) = φ x := hper U fun y hy => (hUs hy).2
  have := QuotientAddGroup.discreteTopology hUo
  have hfin : ((QuotientAddGroup.mk : (κ → Fv F v) → (κ → Fv F v) ⧸ U) '' tsupport φ).Finite :=
    (hφ.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  have hsum : φ = ∑ q ∈ hfin.toFinset, φ q.out • (fun x => if x + -q.out ∈ U then (1 : ℂ) else 0) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    have hmem : ∀ q : (κ → Fv F v) ⧸ U, x + -q.out ∈ U ↔ q = QuotientAddGroup.mk x := by
      intro q
      rw [add_comm, ← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
    have hval : φ (QuotientAddGroup.mk x : (κ → Fv F v) ⧸ U).out = φ x := by
      have h3 : x + -(QuotientAddGroup.mk x : (κ → Fv F v) ⧸ U).out ∈ U := (hmem _).2 rfl
      have h4 := hper' x _ (U.neg_mem h3)
      rw [neg_add, neg_neg, add_neg_cancel_left] at h4
      exact h4
    rw [Finset.sum_eq_single (QuotientAddGroup.mk x)]
    · rw [if_pos ((hmem _).2 rfl), hval]
    · intro q _ hq
      rw [if_neg fun h => hq ((hmem q).1 h)]
    · intro hx
      have hx' : x ∉ tsupport φ := fun h => hx (hfin.mem_toFinset.2 ⟨x, h, rfl⟩)
      split_ifs
      · rw [hval, image_eq_zero_of_notMem_tsupport hx']
      · rfl
  rw [hsum]
  exact S.sum_mem fun q _ => S.smul_mem _ (hind _)

end GlobalTheory.SchrCyclic

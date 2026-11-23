import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveHomogeneousOperatorLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergInnerPreserving
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLinearOperatorL2Isometry
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompactOpenLattice

open Filter Topology GlobalTheory.SchurLin ComplexConjugate

section Lat

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {κ : Type} [Fintype κ]

def vlat (ψ : AddChar K ℂ) (t : K) : AddSubgroup (κ → K) where
  carrier := {x | ∀ i, x i ∈ dualBall ψ t}
  zero_mem' := fun _ => (dualBall ψ t).zero_mem
  add_mem' := fun ha hb i => (dualBall ψ t).add_mem (ha i) (hb i)
  neg_mem' := fun ha i => (dualBall ψ t).neg_mem (ha i)

theorem mem_vlat {ψ : AddChar K ℂ} {t : K} {x : κ → K} : x ∈ vlat ψ t ↔ ∀ i, x i ∈ dualBall ψ t := Iff.rfl

theorem vlat_mem_nhds {ψ : AddChar K ℂ} (hψc : Continuous ψ) (t : K) :
    ((vlat (κ := κ) ψ t : AddSubgroup (κ → K)) : Set (κ → K)) ∈ 𝓝 0 := by
  have h : ∀ i, ∀ᶠ x in 𝓝 (0 : κ → K), x i ∈ dualBall ψ t := fun i =>
    ((continuous_apply i).tendsto (0 : κ → K)).eventually (dualBall_mem_nhds hψc t)
  filter_upwards [Filter.eventually_all.2 h] with x hx using hx

theorem vlat_isOpen {ψ : AddChar K ℂ} (hψc : Continuous ψ) (t : K) : IsOpen ((vlat (κ := κ) ψ t : AddSubgroup (κ → K)) : Set (κ → K)) :=
  AddSubgroup.isOpen_of_mem_nhds _ (vlat_mem_nhds hψc t)

theorem vlat_isCompact {ψ : AddChar K ℂ} (hψc : Continuous ψ) {x₀ : K} (hx₀ : ψ x₀ ≠ 1) {t : K} (ht : t ≠ 0) :
    IsCompact ((vlat (κ := κ) ψ t : AddSubgroup (κ → K)) : Set (κ → K)) := by
  refine (isCompact_univ_pi (fun _ : κ =>
    IsNonarchimedeanLocalField.isCompact_closedBall K (ValuativeRel.valuation K (x₀ / t)))).of_isClosed_subset
    (AddSubgroup.isClosed_of_isOpen _ (vlat_isOpen hψc t)) ?_
  intro x hx i _
  exact dualBall_subset hx₀ ht (hx i)

theorem vlat_small {ψ : AddChar K ℂ} {x₀ : K} (hx₀ : ψ x₀ ≠ 1) {W : Set (κ → K)} (hW : W ∈ 𝓝 0) :
    ∃ t : K, t ≠ 0 ∧ ((vlat (κ := κ) ψ t : AddSubgroup (κ → K)) : Set (κ → K)) ⊆ W := by
  set B : Set (κ → K) := Set.univ.pi fun _ => {x : K | ValuativeRel.valuation K x ≤ 1}
  have hB : IsCompact B := isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall K 1
  have h : ∀ᶠ s in 𝓝 (0 : K), ∀ Y ∈ B, s • Y ∈ W := by
    apply hB.eventually_forall_of_forall_eventually
    intro Y _
    have hc : Continuous (fun z : K × (κ → K) => z.1 • z.2) := continuous_fst.smul continuous_snd
    have h2 : Tendsto (fun z : K × (κ → K) => z.1 • z.2) (𝓝 ((0 : K), Y)) (𝓝 0) := by
      convert hc.tendsto ((0 : K), Y) using 2
      simp
    exact h2.eventually hW
  obtain ⟨γ, hγ, hsub⟩ := (IsValuativeTopology.hasBasis_nhds_zero' K).mem_iff.1 h
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation K)
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective γ
  have hx00 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one ψ)
  set s := r * a with hs
  have hvs : ValuativeRel.valuation K s < γ := by
    rw [hs, map_mul, ha]
    exact mul_lt_of_lt_one_left (zero_lt_iff.2 hγ) hr1
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvs
    have : ValuativeRel.valuation K r * γ = 0 := by
      rw [← ha, ← map_mul, ← hs, h0, map_zero]
    rcases mul_eq_zero.1 this with h | h
    · exact hr0 (by simpa using h)
    · exact hγ h
  refine ⟨x₀ / s, div_ne_zero hx00 hs0, ?_⟩
  intro Y hY
  have hxs : x₀ / (x₀ / s) = s := by field_simp
  have hYs : ∀ i, ValuativeRel.valuation K (Y i) ≤ ValuativeRel.valuation K s := by
    intro i
    have := dualBall_subset hx₀ (div_ne_zero hx00 hs0) (hY i)
    rwa [Set.mem_setOf_eq, hxs] at this
  have hmem : s⁻¹ • Y ∈ B := by
    intro i _
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    have hv0 : ValuativeRel.valuation K s ≠ 0 := by simpa using hs0
    rw [inv_mul_le_iff₀ (zero_lt_iff.2 hv0), mul_one]
    exact hYs i
  have := hsub hvs (s⁻¹ • Y) hmem
  rwa [smul_smul, mul_inv_cancel₀ hs0, one_smul] at this

theorem vlat_sep {ψ : AddChar K ℂ} (t : K) (x : κ → K) (hx : x ∉ vlat ψ t) :
    ∃ y : κ → K, ψ (x ⬝ᵥ y) ≠ 1 ∧ ∀ u ∈ vlat ψ t, ψ (u ⬝ᵥ y) = 1 := by
  classical
  rw [mem_vlat] at hx
  push_neg at hx
  obtain ⟨i, hi⟩ := hx
  rw [mem_dualBall] at hi
  push_neg at hi
  obtain ⟨o, ho, hne⟩ := hi
  have hsum : ∀ z : κ → K, z ⬝ᵥ Pi.single i (o * t) = o * (t * z i) := by
    intro z
    rw [dotProduct_single]
    ring
  exact ⟨Pi.single i (o * t), by rw [hsum]; exact hne,
    fun u hu => by rw [hsum]; exact (mem_vlat.1 hu i) o ho⟩

end Lat

section Gen

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem exists_cover (U : AddSubgroup V) (hU : IsOpen (U : Set V)) {f : V → ℂ} (hf : HasCompactSupport f) :
    ∃ S : Finset (V ⧸ U), ∀ Y, f Y ≠ 0 → (QuotientAddGroup.mk Y : V ⧸ U) ∈ S := by
  haveI := QuotientAddGroup.discreteTopology hU
  have hfin : ((QuotientAddGroup.mk : V → V ⧸ U) '' tsupport f).Finite :=
    (hf.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  exact ⟨hfin.toFinset, fun Y hY => hfin.mem_toFinset.2 ⟨Y, subset_tsupport f hY, rfl⟩⟩

def cosetInd (U : AddSubgroup V) (q : V ⧸ U) : V → ℂ := fun Y => (U : Set V).indicator 1 (Y + -q.out)

open Classical in
theorem cosetInd_apply (U : AddSubgroup V) (q : V ⧸ U) (Y : V) :
    cosetInd U q Y = if (QuotientAddGroup.mk Y : V ⧸ U) = q then 1 else 0 := by
  classical
  have : (QuotientAddGroup.mk Y : V ⧸ U) = q ↔ Y + -q.out ∈ U := by
    conv_lhs => rw [← Quotient.out_eq' q]
    rw [eq_comm]
    show (QuotientAddGroup.mk q.out : V ⧸ U) = QuotientAddGroup.mk Y ↔ _
    rw [QuotientAddGroup.eq, show Y + -q.out = -q.out + Y by abel]
  simp only [cosetInd, Set.indicator_apply, SetLike.mem_coe, Pi.one_apply, this]

theorem decomp (U : AddSubgroup V) {f : V → ℂ} (hinv : ∀ Y, ∀ u ∈ U, f (Y + u) = f Y)
    (S : Finset (V ⧸ U)) (hS : ∀ Y, f Y ≠ 0 → (QuotientAddGroup.mk Y : V ⧸ U) ∈ S) :
    f = ∑ q ∈ S, f q.out • cosetInd U q := by
  classical
  funext Y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cosetInd_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq]
  split_ifs with h
  · have h1 : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk Y : V ⧸ U)) : V ⧸ U)
        = QuotientAddGroup.mk Y := Quotient.out_eq' _
    rw [QuotientAddGroup.eq] at h1
    have := hinv (Quotient.out (QuotientAddGroup.mk Y : V ⧸ U)) _ h1
    rw [add_neg_cancel_left] at this
    exact this
  · by_contra hne
    exact h (hS Y hne)

variable (Q : (V → ℂ) → (V → ℂ) → ℂ)

theorem sum_left (hadd : ∀ f ∈ SB V, ∀ f' ∈ SB V, ∀ g ∈ SB V, Q (f + f') g = Q f g + Q f' g)
    (hsmul : ∀ (c : ℂ), ∀ f ∈ SB V, ∀ g ∈ SB V, Q (c • f) g = c * Q f g)
    {ι : Type} (S : Finset ι) (a : ι → ℂ) (k : ι → V → ℂ) (hk : ∀ i, k i ∈ SB V) {g : V → ℂ}
    (hg : g ∈ SB V) : Q (∑ i ∈ S, a i • k i) g = ∑ i ∈ S, a i * Q (k i) g := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := hsmul 0 0 (SB V).zero_mem g hg
    simpa using this
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      hadd _ ((SB V).smul_mem _ (hk j)) _ ((SB V).sum_mem fun i _ => (SB V).smul_mem _ (hk i)) g hg,
      hsmul _ _ (hk j) g hg, ih]

theorem sum_right (hadd : ∀ f ∈ SB V, ∀ g ∈ SB V, ∀ g' ∈ SB V, Q f (g + g') = Q f g + Q f g')
    (hsmul : ∀ (c : ℂ), ∀ f ∈ SB V, ∀ g ∈ SB V, Q f (c • g) = conj c * Q f g)
    {ι : Type} (S : Finset ι) (a : ι → ℂ) (k : ι → V → ℂ) (hk : ∀ i, k i ∈ SB V) {f : V → ℂ}
    (hf : f ∈ SB V) : Q f (∑ i ∈ S, a i • k i) = ∑ i ∈ S, conj (a i) * Q f (k i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := hsmul 0 f hf 0 (SB V).zero_mem
    simpa using this
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      hadd f hf _ ((SB V).smul_mem _ (hk j)) _ ((SB V).sum_mem fun i _ => (SB V).smul_mem _ (hk i)),
      hsmul _ f hf _ (hk j), ih]

theorem form_eq (U : AddSubgroup V) (hUo : IsOpen (U : Set V)) (hUc : IsCompact (U : Set V))
    (hadd : ∀ f ∈ SB V, ∀ f' ∈ SB V, ∀ g ∈ SB V, Q (f + f') g = Q f g + Q f' g)
    (hsmul : ∀ (c : ℂ), ∀ f ∈ SB V, ∀ g ∈ SB V, Q (c • f) g = c * Q f g)
    (hadd' : ∀ f ∈ SB V, ∀ g ∈ SB V, ∀ g' ∈ SB V, Q f (g + g') = Q f g + Q f g')
    (hsmul' : ∀ (c : ℂ), ∀ f ∈ SB V, ∀ g ∈ SB V, Q f (c • g) = conj c * Q f g)
    (htr : ∀ Z : V, ∀ f ∈ SB V, ∀ g ∈ SB V, Q (fun Y => f (Y + Z)) (fun Y => g (Y + Z)) = Q f g)
    (χ : V → V → ℂ)
    (hχ : ∀ Z : V, ∀ f ∈ SB V, ∀ g ∈ SB V, Q (fun Y => χ Z Y * f Y) (fun Y => χ Z Y * g Y) = Q f g)
    (hχadd : ∀ Z Y Y', χ Z (Y + Y') = χ Z Y * χ Z Y')
    (hχn : ∀ Z Y, χ Z Y * conj (χ Z Y) = 1)
    (hsep : ∀ Y ∉ U, ∃ Z, χ Z Y ≠ 1 ∧ ∀ u ∈ U, χ Z u = 1)
    {f g : V → ℂ} (hf : f ∈ SB V) (hg : g ∈ SB V)
    (hfi : ∀ Y, ∀ u ∈ U, f (Y + u) = f Y) (hgi : ∀ Y, ∀ u ∈ U, g (Y + u) = g Y)
    (S : Finset (V ⧸ U)) (hSf : ∀ Y, f Y ≠ 0 → (QuotientAddGroup.mk Y : V ⧸ U) ∈ S)
    (hSg : ∀ Y, g Y ≠ 0 → (QuotientAddGroup.mk Y : V ⧸ U) ∈ S) :
    Q f g = Q ((U : Set V).indicator 1) ((U : Set V).indicator 1) * ∑ q ∈ S, f q.out * conj (g q.out) := by
  classical
  set e : V → ℂ := (U : Set V).indicator 1 with he_def
  have he : e ∈ SB V := sb_indicator U hUo hUc
  have hk : ∀ q, cosetInd U q ∈ SB V := fun q => sb_translate he _
  have hdiag : ∀ q, Q (cosetInd U q) (cosetInd U q) = Q e e := by
    intro q
    have := htr q.out (cosetInd U q) (hk q) (cosetInd U q) (hk q)
    have h2 : (fun Y => cosetInd U q (Y + q.out)) = e := by
      funext Y
      simp only [cosetInd, he_def, add_neg_cancel_right]
    rw [h2] at this
    exact this.symm
  have hoff : ∀ q q', q ≠ q' → Q (cosetInd U q) (cosetInd U q') = 0 := by
    intro q q' hqq
    have hnot : q.out - q'.out ∉ U := by
      intro hmem
      apply hqq
      have h1 : (QuotientAddGroup.mk q'.out : V ⧸ U) = QuotientAddGroup.mk q.out := by
        rw [QuotientAddGroup.eq, show -q'.out + q.out = q.out - q'.out by abel]
        exact hmem
      have e1 : (QuotientAddGroup.mk q.out : V ⧸ U) = q := Quotient.out_eq' q
      have e2 : (QuotientAddGroup.mk q'.out : V ⧸ U) = q' := Quotient.out_eq' q'
      rw [e1, e2] at h1
      exact h1.symm
    obtain ⟨Z, hZ1, hZU⟩ := hsep _ hnot
    have hmulq : ∀ r : V ⧸ U, (fun Y => χ Z Y * cosetInd U r Y) = χ Z r.out • cosetInd U r := by
      intro r
      funext Y
      simp only [Pi.smul_apply, smul_eq_mul, cosetInd]
      by_cases hY : Y + -r.out ∈ U
      · have : χ Z Y = χ Z r.out := by
          have := hχadd Z (Y + -r.out) r.out
          rw [neg_add_cancel_right, hZU _ hY, one_mul] at this
          exact this
        rw [this]
      · rw [Set.indicator_of_notMem (show Y + -r.out ∉ (U : Set V) from hY), mul_zero, mul_zero]
    have h := hχ Z _ (hk q) _ (hk q')
    rw [hmulq q, hmulq q', hsmul _ _ (hk q) _ ((SB V).smul_mem _ (hk q')),
      hsmul' _ _ (hk q) _ (hk q')] at h
    have hab : χ Z q.out * conj (χ Z q'.out) = χ Z (q.out - q'.out) := by
      have := hχadd Z (q.out - q'.out) q'.out
      rw [sub_add_cancel] at this
      rw [this, mul_assoc, hχn, mul_one]
    have h3 : (χ Z (q.out - q'.out) - 1) * Q (cosetInd U q) (cosetInd U q') = 0 := by
      rw [← hab]
      linear_combination h
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4) hZ1
    · exact h4
  have hfd := decomp U hfi S hSf
  have hgd := decomp U hgi S hSg
  have hgsum : (∑ q ∈ S, g q.out • cosetInd U q) ∈ SB V :=
    (SB V).sum_mem fun q _ => (SB V).smul_mem _ (hk q)
  calc Q f g = Q (∑ q ∈ S, f q.out • cosetInd U q) (∑ q ∈ S, g q.out • cosetInd U q) := by
        conv_lhs => rw [hfd, hgd]
    _ = ∑ q ∈ S, f q.out * ∑ q' ∈ S, conj (g q'.out) * Q (cosetInd U q) (cosetInd U q') := by
        rw [sum_left Q hadd hsmul S _ _ hk hgsum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [sum_right Q hadd' hsmul' S _ _ hk (hk q)]
    _ = ∑ q ∈ S, f q.out * (conj (g q.out) * Q e e) := by
        refine Finset.sum_congr rfl fun q hq => ?_
        rw [Finset.sum_eq_single q (fun q' _ hq' => by rw [hoff q q' (Ne.symm hq'), mul_zero])
          (fun h => absurd hq h), hdiag]
    _ = Q e e * ∑ q ∈ S, f q.out * conj (g q.out) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by ring

end Gen

section Loc

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Invertible (2 : K)] {κ : Type} [Fintype κ]

theorem schr_trans (ψ : AddChar K ℂ) (Z : κ → K) (φ : (κ → K) → ℂ) :
    schr ψ (Z, 0) φ = fun Y => φ (Y + Z) := by
  funext Y
  simp [schr]

theorem schr_char (ψ : AddChar K ℂ) (Z : κ → K) (φ : (κ → K) → ℂ) :
    schr ψ (0, Z) φ = fun Y => ψ (Y ⬝ᵥ Z) * φ Y := by
  funext Y
  simp [schr]

theorem form_eq_loc (ψ : AddChar K ℂ) (hψc : Continuous ψ) {x₀ : K} (hx₀ : ψ x₀ ≠ 1)
    (R : ((κ → K) → ℂ) →ₗ[ℂ] (κ → K) → ℂ) (A : (κ → K) × (κ → K) → (κ → K) × (κ → K))
    (hR : ∀ φ ∈ SB (κ → K), R φ ∈ SB (κ → K))
    (hRA : ∀ w, ∀ φ ∈ SB (κ → K), R (schr ψ w φ) = schr ψ (A w) (R φ))
    (μ : @Measure (κ → K) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    {t : K} (ht : t ≠ 0) {f g : (κ → K) → ℂ} (hf : f ∈ SB (κ → K)) (hg : g ∈ SB (κ → K))
    (hfi : ∀ Y, ∀ u ∈ vlat ψ t, f (Y + u) = f Y) (hgi : ∀ Y, ∀ u ∈ vlat ψ t, g (Y + u) = g Y)
    (S : Finset ((κ → K) ⧸ vlat (κ := κ) ψ t))
    (hSf : ∀ Y, f Y ≠ 0 → (QuotientAddGroup.mk Y : (κ → K) ⧸ vlat (κ := κ) ψ t) ∈ S)
    (hSg : ∀ Y, g Y ≠ 0 → (QuotientAddGroup.mk Y : (κ → K) ⧸ vlat (κ := κ) ψ t) ∈ S) :
    @integral _ ℂ _ _ (borel _) μ (fun x => R f x * conj (R g x)) =
      @integral _ ℂ _ _ (borel _) μ (fun x =>
        R (((vlat (κ := κ) ψ t : AddSubgroup (κ → K)) : Set (κ → K)).indicator 1) x *
          conj (R (((vlat (κ := κ) ψ t : AddSubgroup (κ → K)) : Set (κ → K)).indicator 1) x)) *
        ∑ q ∈ S, f q.out * conj (g q.out) := by
  letI : MeasurableSpace (κ → K) := borel _
  haveI : BorelSpace (κ → K) := ⟨rfl⟩
  haveI := hμ
  have hI : ∀ f ∈ SB (κ → K), ∀ g ∈ SB (κ → K), Integrable (fun x => R f x * conj (R g x)) μ :=
    fun f hf g hg => GlobalTheory.PolarSB.integrable_mul_conj μ (hR f hf) (hR g hg)
  have hinvar : ∀ w, ∀ f ∈ SB (κ → K), ∀ g ∈ SB (κ → K),
      ∫ x, R (schr ψ w f) x * conj (R (schr ψ w g) x) ∂μ = ∫ x, R f x * conj (R g x) ∂μ := by
    intro w f hf g hg
    rw [hRA w f hf, hRA w g hg]
    exact GlobalTheory.schr_unitary ψ hψc μ hμ (A w) (R f) (R g)
  refine form_eq (fun f g => ∫ x, R f x * conj (R g x) ∂μ) (vlat ψ t) (vlat_isOpen hψc t)
    (vlat_isCompact hψc hx₀ ht) ?_ ?_ ?_ ?_ ?_ (fun Z Y => ψ (Y ⬝ᵥ Z)) ?_ ?_ ?_ (fun Y hY => vlat_sep t Y hY)
    hf hg hfi hgi S hSf hSg
  · intro f hf f' hf' g hg
    rw [← integral_add (hI f hf g hg) (hI f' hf' g hg)]
    congr 1
    funext x
    rw [map_add, Pi.add_apply, add_mul]
  · intro c f hf g hg
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  · intro f hf g hg g' hg'
    rw [← integral_add (hI f hf g hg) (hI f hf g' hg')]
    congr 1
    funext x
    rw [map_add, Pi.add_apply, map_add, mul_add]
  · intro c f hf g hg
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  · intro Z f hf g hg
    have := hinvar (Z, 0) f hf g hg
    rwa [schr_trans, schr_trans] at this
  · intro Z f hf g hg
    have := hinvar (0, Z) f hf g hg
    rwa [schr_char, schr_char] at this
  · intro Z Y Y'
    simp only [add_dotProduct, AddChar.map_add_eq_mul]
  · intro Z Y
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, GlobalTheory.norm_addChar_nonarch ψ hψc]
    simp

end Loc

section Main

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Invertible (2 : K)] {κ : Type} [Fintype κ]

theorem sum_mul_conj_eq {V : Type} [AddCommGroup V] {U : AddSubgroup V} (S : Finset (V ⧸ U)) (h : V → ℂ) :
    ∑ q ∈ S, h q.out * conj (h q.out) = ((∑ q ∈ S, ‖h q.out‖ ^ 2 : ℝ) : ℂ) := by
  push_cast
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

theorem sum_pos_of_one {ψ : AddChar K ℂ} {t : K} (hle : vlat (κ := κ) ψ t ≤ vlat ψ 1)
    (S : Finset ((κ → K) ⧸ vlat (κ := κ) ψ t))
    (hS : ∀ Y, ((vlat (κ := κ) ψ 1 : AddSubgroup (κ → K)) : Set (κ → K)).indicator (1 : (κ → K) → ℂ) Y ≠ 0 →
      (QuotientAddGroup.mk Y : (κ → K) ⧸ vlat (κ := κ) ψ t) ∈ S) :
    0 < ∑ q ∈ S, ‖((vlat (κ := κ) ψ 1 : AddSubgroup (κ → K)) : Set (κ → K)).indicator (1 : (κ → K) → ℂ) q.out‖ ^ 2 := by
  set q₀ : (κ → K) ⧸ vlat (κ := κ) ψ t := QuotientAddGroup.mk 0 with hq₀_def
  have h0 : ((vlat (κ := κ) ψ 1 : AddSubgroup (κ → K)) : Set (κ → K)).indicator (1 : (κ → K) → ℂ) 0 ≠ 0 := by
    rw [Set.indicator_of_mem (show (0 : κ → K) ∈ ((vlat (κ := κ) ψ 1 : AddSubgroup (κ → K)) : Set (κ → K)) from
      (vlat (κ := κ) ψ 1).zero_mem)]
    simp
  have hq₀ : q₀ ∈ S := hS 0 h0
  have hout : q₀.out ∈ ((vlat (κ := κ) ψ 1 : AddSubgroup (κ → K)) : Set (κ → K)) := by
    have h1 : (QuotientAddGroup.mk q₀.out : (κ → K) ⧸ vlat (κ := κ) ψ t) = QuotientAddGroup.mk 0 :=
      Quotient.out_eq' q₀
    rw [QuotientAddGroup.eq] at h1
    apply hle
    have := (vlat (κ := κ) ψ t).neg_mem h1
    simpa using this
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun q : (κ → K) ⧸ vlat (κ := κ) ψ t =>
    ‖((vlat (κ := κ) ψ 1 : AddSubgroup (κ → K)) : Set (κ → K)).indicator (1 : (κ → K) → ℂ) q.out‖ ^ 2)
    (fun q _ => by positivity) hq₀)
  rw [Set.indicator_of_mem hout]
  simp

theorem main_local (ψ : AddChar K ℂ) (hψc : Continuous ψ) (hψ : ψ ≠ 1)
    (T : ((κ → K) → ℂ) →ₗ[ℂ] (κ → K) → ℂ) (A : (κ → K) × (κ → K) → (κ → K) × (κ → K))
    (hT : ∀ φ ∈ SB (κ → K), T φ ∈ SB (κ → K))
    (hTA : ∀ w, ∀ φ ∈ SB (κ → K), T (schr ψ w φ) = schr ψ (A w) (T φ)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → K) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ SB (κ → K), ∀ φ' ∈ SB (κ → K),
        @integral _ ℂ _ _ (borel _) μ (fun x => T φ x * starRingEnd ℂ (T φ' x)) =
          (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => φ x * starRingEnd ℂ (φ' x)) := by
  classical
  obtain ⟨x₀, hx₀⟩ : ∃ x, ψ x ≠ 1 := by
    by_contra h
    push_neg at h
    exact hψ (by ext x; rw [h x, AddChar.one_apply])
  obtain ⟨e₁, he₁_def⟩ : ∃ e : (κ → K) → ℂ,
      e = ((vlat (κ := κ) ψ 1 : AddSubgroup (κ → K)) : Set (κ → K)).indicator 1 := ⟨_, rfl⟩
  have he₁ : e₁ ∈ SB (κ → K) := by
    rw [he₁_def]
    exact sb_indicator _ (vlat_isOpen hψc 1) (vlat_isCompact hψc hx₀ one_ne_zero)
  have hTe₁ := hT e₁ he₁
  have hidA : ∀ w, ∀ φ ∈ SB (κ → K), (LinearMap.id : ((κ → K) → ℂ) →ₗ[ℂ] (κ → K) → ℂ) (schr ψ w φ) =
      schr ψ (id w) ((LinearMap.id : ((κ → K) → ℂ) →ₗ[ℂ] (κ → K) → ℂ) φ) := fun _ _ _ => rfl
  have hidSB : ∀ φ ∈ SB (κ → K), (LinearMap.id : ((κ → K) → ℂ) →ₗ[ℂ] (κ → K) → ℂ) φ ∈ SB (κ → K) :=
    fun φ hφ => hφ
  have he₁inv : ∀ t, vlat (κ := κ) ψ t ≤ vlat ψ 1 → ∀ Y, ∀ u ∈ vlat (κ := κ) ψ t, e₁ (Y + u) = e₁ Y := by
    intro t hle Y u hu
    simp only [he₁_def, Set.indicator_apply, SetLike.mem_coe, Pi.one_apply, (vlat (κ := κ) ψ 1).add_mem_cancel_right (hle hu)]
  have hW₀ : {w | ∀ Y, e₁ (Y + w) = e₁ Y} ∩ {w | ∀ Y, T e₁ (Y + w) = T e₁ Y} ∩
      ((vlat (κ := κ) ψ 1 : AddSubgroup (κ → K)) : Set (κ → K)) ∈ 𝓝 (0 : κ → K) :=
    Filter.inter_mem (Filter.inter_mem (sb_eventually_invariant he₁) (sb_eventually_invariant hTe₁))
      (vlat_mem_nhds hψc 1)
  obtain ⟨t₀, ht₀, hsub₀⟩ := vlat_small hx₀ hW₀
  have hle₀ : vlat (κ := κ) ψ t₀ ≤ vlat ψ 1 := fun u hu => (hsub₀ hu).2
  obtain ⟨S₁, hS₁⟩ := exists_cover (vlat (κ := κ) ψ t₀) (vlat_isOpen hψc t₀) he₁.2
  obtain ⟨S₂, hS₂⟩ := exists_cover (vlat (κ := κ) ψ t₀) (vlat_isOpen hψc t₀) hTe₁.2
  obtain ⟨D₁, hD₁⟩ : ∃ D : ℝ, D = ∑ q ∈ S₁ ∪ S₂, ‖e₁ q.out‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨D₂, hD₂⟩ : ∃ D : ℝ, D = ∑ q ∈ S₁ ∪ S₂, ‖T e₁ q.out‖ ^ 2 := ⟨_, rfl⟩
  have hD₁pos : 0 < D₁ := by
    rw [hD₁, he₁_def]
    exact sum_pos_of_one hle₀ _ (fun Y hY => Finset.mem_union_left _ (hS₁ Y (he₁_def ▸ hY)))
  refine ⟨D₂ / D₁, div_nonneg (by rw [hD₂]; exact Finset.sum_nonneg fun _ _ => by positivity) hD₁pos.le, ?_⟩
  intro μ hμ
  have key : @integral _ ℂ _ _ (borel _) μ (fun x => T e₁ x * conj (T e₁ x)) =
      ((D₂ / D₁ : ℝ) : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => e₁ x * conj (e₁ x)) := by
    have h1 := form_eq_loc ψ hψc hx₀ LinearMap.id id hidSB hidA μ hμ ht₀ hTe₁ hTe₁
      (fun Y u hu => (hsub₀ hu).1.2 Y) (fun Y u hu => (hsub₀ hu).1.2 Y) (S₁ ∪ S₂)
      (fun Y hY => Finset.mem_union_right _ (hS₂ Y hY)) (fun Y hY => Finset.mem_union_right _ (hS₂ Y hY))
    have h2 := form_eq_loc ψ hψc hx₀ LinearMap.id id hidSB hidA μ hμ ht₀ he₁ he₁
      (he₁inv t₀ hle₀) (he₁inv t₀ hle₀) (S₁ ∪ S₂)
      (fun Y hY => Finset.mem_union_left _ (hS₁ Y hY)) (fun Y hY => Finset.mem_union_left _ (hS₁ Y hY))
    simp only [LinearMap.id_apply] at h1 h2
    rw [sum_mul_conj_eq, ← hD₂] at h1
    rw [sum_mul_conj_eq, ← hD₁] at h2
    rw [h1, h2]
    have : (D₁ : ℂ) ≠ 0 := by exact_mod_cast hD₁pos.ne'
    rw [Complex.ofReal_div, div_mul_eq_mul_div, eq_div_iff this]
    ring
  intro φ hφ φ' hφ'
  have hW : {w | ∀ Y, φ (Y + w) = φ Y} ∩ {w | ∀ Y, φ' (Y + w) = φ' Y} ∩
      ((vlat (κ := κ) ψ 1 : AddSubgroup (κ → K)) : Set (κ → K)) ∈ 𝓝 (0 : κ → K) :=
    Filter.inter_mem (Filter.inter_mem (sb_eventually_invariant hφ) (sb_eventually_invariant hφ'))
      (vlat_mem_nhds hψc 1)
  obtain ⟨t, ht, hsub⟩ := vlat_small hx₀ hW
  have hle : vlat (κ := κ) ψ t ≤ vlat ψ 1 := fun u hu => (hsub hu).2
  obtain ⟨Sa, hSa⟩ := exists_cover (vlat (κ := κ) ψ t) (vlat_isOpen hψc t) hφ.2
  obtain ⟨Sb, hSb⟩ := exists_cover (vlat (κ := κ) ψ t) (vlat_isOpen hψc t) hφ'.2
  obtain ⟨Sc, hSc⟩ := exists_cover (vlat (κ := κ) ψ t) (vlat_isOpen hψc t) he₁.2
  have hfi : ∀ Y, ∀ u ∈ vlat (κ := κ) ψ t, φ (Y + u) = φ Y := fun Y u hu => (hsub hu).1.1 Y
  have hgi : ∀ Y, ∀ u ∈ vlat (κ := κ) ψ t, φ' (Y + u) = φ' Y := fun Y u hu => (hsub hu).1.2 Y
  have mA : ∀ Y, φ Y ≠ 0 → (QuotientAddGroup.mk Y : (κ → K) ⧸ vlat (κ := κ) ψ t) ∈ Sa ∪ Sb ∪ Sc :=
    fun Y hY => Finset.mem_union_left _ (Finset.mem_union_left _ (hSa Y hY))
  have mB : ∀ Y, φ' Y ≠ 0 → (QuotientAddGroup.mk Y : (κ → K) ⧸ vlat (κ := κ) ψ t) ∈ Sa ∪ Sb ∪ Sc :=
    fun Y hY => Finset.mem_union_left _ (Finset.mem_union_right _ (hSb Y hY))
  have mC : ∀ Y, e₁ Y ≠ 0 → (QuotientAddGroup.mk Y : (κ → K) ⧸ vlat (κ := κ) ψ t) ∈ Sa ∪ Sb ∪ Sc :=
    fun Y hY => Finset.mem_union_right _ (hSc Y hY)
  have hTf := form_eq_loc ψ hψc hx₀ T A hT hTA μ hμ ht hφ hφ' hfi hgi _ mA mB
  have hLf := form_eq_loc ψ hψc hx₀ LinearMap.id id hidSB hidA μ hμ ht hφ hφ' hfi hgi _ mA mB
  have hTe := form_eq_loc ψ hψc hx₀ T A hT hTA μ hμ ht he₁ he₁ (he₁inv t hle) (he₁inv t hle) _ mC mC
  have hLe := form_eq_loc ψ hψc hx₀ LinearMap.id id hidSB hidA μ hμ ht he₁ he₁ (he₁inv t hle)
    (he₁inv t hle) _ mC mC
  simp only [LinearMap.id_apply] at hLf hLe
  have hpos : 0 < ∑ q ∈ Sa ∪ Sb ∪ Sc, ‖e₁ q.out‖ ^ 2 := by
    rw [he₁_def]
    exact sum_pos_of_one hle _ (fun Y hY => mC Y (he₁_def ▸ hY))
  rw [sum_mul_conj_eq] at hTe hLe
  have hD : ((∑ q ∈ Sa ∪ Sb ∪ Sc, ‖e₁ q.out‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [hTe, hLe] at key
  have hcancel : ∀ a b d c : ℂ, d ≠ 0 → a * d = c * (b * d) → a = c * b := by
    intro a b d c hd h
    apply mul_right_cancel₀ hd
    rw [h]
    ring
  have := hcancel _ _ _ _ hD key
  rw [hTf, hLf, this]
  ring

end Main

end GlobalTheory.CompactOpenLattice

theorem GlobalTheory.CompactOpenLattice.inner_eq_const_mul : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) [Invertible (2 : Fv F v)] (κ : Type) [Fintype κ]
    (ψv : AddChar (Fv F v) ℂ), Continuous ψv → ψv ≠ 1 →
    ∀ (T : ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ) (A : (κ → Fv F v) × (κ → Fv F v) → (κ → Fv F v) × (κ → Fv F v)),
      (∀ φ ∈ SB (κ → Fv F v), T φ ∈ SB (κ → Fv F v)) →
      (∀ w, ∀ φ ∈ SB (κ → Fv F v), T (schr ψv w φ) = schr ψv (A w) (T φ)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ φ ∈ SB (κ → Fv F v), ∀ φ' ∈ SB (κ → Fv F v),
          @integral _ ℂ _ _ (borel _) μ (fun x => T φ x * starRingEnd ℂ (T φ' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => φ x * starRingEnd ℂ (φ' x)) := by
  intro F _ _ v _ κ _ ψv hc hne T A hT hTA
  exact GlobalTheory.CompactOpenLattice.main_local ψv hc hne T A hT hTA

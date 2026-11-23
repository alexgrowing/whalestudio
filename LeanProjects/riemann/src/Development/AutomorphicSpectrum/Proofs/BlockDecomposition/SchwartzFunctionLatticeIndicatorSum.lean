import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClopenCoset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZpowMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_latZ_subset_of_mem_nhds (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) {U : Set (Fin d → k)} (hU : U ∈ 𝓝 (0 : Fin d → k)) :
    ∃ r : ℕ, ((latZ z (r : ℤ)).sub : Set (Fin d → k)) ⊆ U := by
  have hall : ∀ᶠ t : k in 𝓝 0, ∀ w ∈ ((lat0 : COSub k d).sub : Set (Fin d → k)), t • w ∈ U := by
    refine (lat0 : COSub k d).isCompact.eventually_forall_of_forall_eventually fun w _ => ?_
    have hc : Continuous fun p : k × (Fin d → k) => p.1 • p.2 := continuous_fst.smul continuous_snd
    have h0 : U ∈ 𝓝 (((0 : k), w).1 • ((0 : k), w).2) := by simpa using hU
    exact hc.continuousAt.eventually h0
  have ht : Filter.Tendsto (fun n : ℕ => ϖ ^ n) Filter.atTop (𝓝 0) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
    intro γ hγ
    have : MulArchimedean (ValuativeRel.ValueGroupWithZero k) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ (Units.mk0 γ hγ)
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    rw [map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn
  obtain ⟨r, hr⟩ := (ht.eventually hall).exists
  refine ⟨r, fun y hy => ?_⟩
  have h1 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) ∈ U :=
    hr _ hy
  have h2 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) = y := by
    have := zpow_mulVec z ϖ hz hϖ0 (r : ℤ)
      ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, zpow_natCast] at this
    exact this.symm
  rwa [h2] at h1

theorem exists_latZ_invariant (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (f : SchF k d V) :
    ∃ r₀ : ℕ, ∀ y, ∀ l ∈ (latZ z (r₀ : ℤ)).sub, f.1 (y + l) = f.1 y := by
  have hlc : IsLocallyConstant f.1 := f.2.1
  have hK : IsCompact (tsupport f.1) := f.2.2
  have hW : ∀ᶠ l : Fin d → k in 𝓝 0, ∀ y ∈ tsupport f.1, f.1 (y + l) = f.1 y := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous fun p : (Fin d → k) × (Fin d → k) => p.2 + p.1 := continuous_snd.add continuous_fst
    have h1 := (IsLocallyConstant.iff_eventually_eq _).1 (hlc.comp_continuous hc) ((0 : Fin d → k), y)
    have h2 := (IsLocallyConstant.iff_eventually_eq _).1 (hlc.comp_continuous continuous_snd)
      ((0 : Fin d → k), y)
    filter_upwards [h1, h2] with p hp1 hp2
    have e1 : f.1 (p.2 + p.1) = f.1 (y + 0) := hp1
    have e2 : f.1 p.2 = f.1 y := hp2
    rw [e1, e2, add_zero]
  obtain ⟨r₀, hr₀⟩ := exists_latZ_subset_of_mem_nhds z ϖ hz hϖ hϖ0 hW
  refine ⟨r₀, fun y l hl => ?_⟩
  by_cases hy : y ∈ tsupport f.1
  · exact hr₀ hl y hy
  by_cases hyl : y + l ∈ tsupport f.1
  · have := hr₀ ((latZ z (r₀ : ℤ)).sub.neg_mem hl) (y + l) hyl
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyl]

theorem exists_eq_sum_ind_of_invariant (L : COSub k d) (f : SchF k d V)
    (hf : ∀ y, ∀ l ∈ L.sub, f.1 (y + l) = f.1 y) :
    ∃ I : Finset ((Fin d → k) × V), f = ∑ p ∈ I, ind L p.1 p.2 := by
  classical
  have hK : IsCompact (tsupport f.1) := f.2.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun c : Fin d → k => {y | y - c ∈ L.sub})
    (fun c => (isClopen_coset L c).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
  let mk : (Fin d → k) → (Fin d → k) ⧸ L.sub := QuotientAddGroup.mk
  have hmk : ∀ (q : (Fin d → k) ⧸ L.sub) (y : Fin d → k), y - Quotient.out q ∈ L.sub ↔ mk y = q := by
    intro q y
    have e : mk (Quotient.out q) = q := QuotientAddGroup.out_eq' q
    constructor
    · intro h
      rw [← e]
      exact (QuotientAddGroup.eq.2 (by simpa [sub_eq_add_neg, add_comm] using h)).symm
    · intro h
      have h' : mk (Quotient.out q) = mk y := e.trans h.symm
      simpa [sub_eq_add_neg, add_comm] using QuotientAddGroup.eq.1 h'
  let Q : Finset ((Fin d → k) ⧸ L.sub) := t.image mk
  let φ : ((Fin d → k) ⧸ L.sub) → (Fin d → k) × V := fun q => (Quotient.out q, f.1 (Quotient.out q))
  have hφ : Function.Injective φ := fun q q' h => by
    have h1 : Quotient.out q = Quotient.out q' := congrArg Prod.fst h
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', h1]
  refine ⟨Q.image φ, Subtype.ext (funext fun y => ?_)⟩
  rw [Finset.sum_image hφ.injOn, Submodule.coe_sum, Finset.sum_apply]
  have hterm : ∀ q ∈ Q, ((ind L (φ q).1 (φ q).2 : SchF k d V) : (Fin d → k) → V) y =
      if mk y = q then f.1 y else 0 := by
    intro q _
    show (ind L (φ q).1 (φ q).2).1 y = _
    rw [ind_apply]
    by_cases h : mk y = q
    · have hm : y - Quotient.out q ∈ L.sub := (hmk q y).2 h
      rw [if_pos hm, if_pos h]
      have := hf (Quotient.out q) _ hm
      rw [add_sub_cancel] at this
      exact this.symm
    · rw [if_neg (fun hm => h ((hmk q y).1 hm)), if_neg h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  split_ifs with hy
  · rfl
  · refine image_eq_zero_of_notMem_tsupport fun hyK => hy ?_
    obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hyK)
    have hc' : y - c ∈ L.sub := hc
    have : mk y = mk c := (QuotientAddGroup.eq.2 (by simpa [sub_eq_add_neg, add_comm] using hc')).symm
    rw [this]
    exact Finset.mem_image_of_mem mk hct

theorem schF_eq_sum_ind (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (f : SchF k d V) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → ∃ I : Finset ((Fin d → k) × V), f = ∑ p ∈ I, ind (latZ z (r : ℤ)) p.1 p.2 := by
  obtain ⟨r₀, hr₀⟩ := exists_latZ_invariant z ϖ hz hϖ hϖ0 f
  refine ⟨r₀, fun r hr => exists_eq_sum_ind_of_invariant _ f fun y l hl => hr₀ y l ?_⟩
  exact latZ_anti z ϖ hz hϖ hϖ0 _ _ (by exact_mod_cast hr) hl

end GlobalTheory.CompanionTheory.BZCore

end

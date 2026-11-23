import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PBundlePair
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

noncomputable section

namespace ModelTwistGenerated

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {K : Type} [Fintype K] {ι : K → Type}

theorem secOver_mul (y : (Σ k, ι k) → Ω) {β γ : K → ℤ} {a b : Ω} (ha : a ∈ secOver S y β)
    (hb : b ∈ secOver S y γ) : a * b ∈ secOver S y (β + γ) := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule] at ha hb ⊢
  intro c hc
  have : a * b * ∏ k, y ⟨k, c k⟩ ^ (-(β + γ) k) =
      (a * ∏ k, y ⟨k, c k⟩ ^ (-β k)) * (b * ∏ k, y ⟨k, c k⟩ ^ (-γ k)) := by
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.add_apply, neg_add, zpow_add₀ (hc k)]
  rw [this]
  exact Subalgebra.mul_mem _ (ha c hc) (hb c hc)

theorem one_mem_secOver (y : (Σ k, ι k) → Ω) : (1 : Ω) ∈ secOver S y 0 := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply]
  intro c _
  simp only [Pi.zero_apply, neg_zero, zpow_zero, Finset.prod_const_one, mul_one]
  exact Subalgebra.one_mem _

theorem pow_mem_secOver (y : (Σ k, ι k) → Ω) {δ : K → ℤ} {a : Ω} (ha : a ∈ secOver S y δ) (m : ℕ) :
    a ^ m ∈ secOver S y ((m : ℤ) • δ) := by
  induction m with
  | zero => simpa using one_mem_secOver (S := S) y
  | succ m ih =>
    have h := secOver_mul y ih ha
    rw [pow_succ]
    convert h using 2
    push_cast
    rw [add_smul, one_smul]

variable [DecidableEq K]

theorem coord_mem_secOver (y : (Σ k, ι k) → Ω) (k₀ : K) (i : ι k₀) :
    y ⟨k₀, i⟩ ∈ secOver S y (IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule, IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
  intro c _
  rw [Fintype.prod_eq_single k₀ fun k hk => by rw [Pi.single_eq_of_ne hk]; simp]
  rw [Pi.single_eq_same, zpow_neg_one, ← div_eq_mul_inv]
  exact Algebra.subset_adjoin ⟨⟨k₀, i⟩, rfl⟩

theorem prod_coord_mem_secOver (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (s : Finset (Fin (N + 1))) :
    ∏ j ∈ s, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) j ∈
      secOver S y ((s.card : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_secOver (S := S) y
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    have h := secOver_mul y (coord_mem_secOver (S := S) y k₀ (e.symm j)) ih
    convert h using 2 <;> first | rfl | (push_cast; rw [add_smul, one_smul, add_comm])

variable {N : ℕ} {y : (Σ k, ι k) → Ω} {k₀ : K} (e : ι k₀ ≃ Fin (N + 1))

local notation "X" => IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm

theorem twist_sub_eq_chartSecOver (β : K → ℤ)
    (Q : Kleiman.LineBundle S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))
    (hQ : ∀ c : ℤ, (Q.twist (Kleiman.twistSys S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
      secOver S y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀))
    (c : ℕ) (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) :
    ((Q.twist (Kleiman.twistSys S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (c : ℤ))).sub I : Set Ω) =
      chartSecOver S y k₀ e (β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) I := by
  have hsubQ : (Q.sub I : Set Ω) = chartSecOver S y k₀ e β I := by
    refine Set.ext fun t => ?_
    rw [SetLike.mem_coe, mem_sub_iff_gam]
    refine exists_congr fun n => ?_
    rw [Kleiman.SubSystem.gam, hQ]
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : X i ≠ 0 := (Kleiman.mem_support _).mp (I.2.2 hi)
  have hcard := Finset.card_erase_add_one hi
  have hxI : Kleiman.xProd I = X i * ∏ j ∈ I.1.erase i, X j := (Finset.mul_prod_erase I.1 _ hi).symm
  have hxic : X i ^ c ∈ secOver S y ((c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) :=
    pow_mem_secOver y (coord_mem_secOver y k₀ (e.symm i)) c
  have hP : (∏ j ∈ I.1.erase i, X j) ^ c ∈
      secOver S y ((c : ℤ) • (((I.1.erase i).card : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) :=
    pow_mem_secOver y (prod_coord_mem_secOver y k₀ e _) c
  ext t
  rw [SetLike.mem_coe, twist_sub_eq_mul]
  change t ∈ Kleiman.twistMod S X (c : ℤ) I * Q.sub I ↔ _
  rw [Kleiman.twistMod_eq_span (c : ℤ) I hi, Submodule.mem_span_singleton_mul, zpow_natCast]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hb' : b ∈ chartSecOver S y k₀ e β I := by rw [← hsubQ]; exact hb
    obtain ⟨n, hn⟩ := hb'
    refine ⟨n, ?_⟩
    have h := secOver_mul y hxic hn
    rw [show Kleiman.xProd I ^ n * (X i ^ c * b) = X i ^ c * (Kleiman.xProd I ^ n * b) by ring]
    convert h using 2
    abel
  · rintro ⟨n, hn⟩
    refine ⟨(X i ^ c)⁻¹ * t, ?_, by field_simp⟩
    rw [← SetLike.mem_coe, hsubQ]
    refine ⟨n + c, ?_⟩
    have h := secOver_mul y hP hn
    rw [show Kleiman.xProd I ^ (n + c) * ((X i ^ c)⁻¹ * t) =
        (∏ j ∈ I.1.erase i, X j) ^ c * (Kleiman.xProd I ^ n * t) by
      rw [hxI]; field_simp; ring]
    convert h using 2
    funext k
    rw [← hcard]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

end ModelTwistGenerated

open ModelTwistGenerated in

theorem ModelTwistGenerated.proof (hCG : ChartSecGen.Statement) : ModelTwistGenerated.Statement := by
  classical
  intro S _ K _ _ ι _ Ω _ _ y k₀ hS hM β
  obtain ⟨i₀, -⟩ := hM.1 k₀
  have hpos : 0 < Fintype.card (ι k₀) := Fintype.card_pos_iff.mpr ⟨i₀⟩
  set N := Fintype.card (ι k₀) - 1
  have hcard : Fintype.card (ι k₀) = N + 1 := by omega
  let e : ι k₀ ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hcard
  set x := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm with hx
  obtain ⟨Q, hQ⟩ := BundleOfDeg.full S K ι Ω y k₀ N e hM β
  obtain ⟨c₀, hc₀⟩ := GroundTheory.Heights₂.Heights.Kleiman.Generated.full S Ω N x Q
  refine ⟨max c₀ 0, fun c hc => ?_⟩
  lift c to ℕ using le_trans (le_max_right _ _) hc with m
  set L := Q.twist (Kleiman.twistSys S x (m : ℤ)) with hL
  have hgen : L.Generated := hc₀ m (le_trans (le_max_left _ _) hc)
  have hfin : ∀ I : Kleiman.Chart x, ∃ T : Finset Ω, (T : Set Ω) ⊆ L.secs ∧
      Submodule.span (Kleiman.chartRing S x I) (T : Set Ω) = L.sub I := by
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hfg : (L.sub I).FG := by
      rw [hL, twist_sub_eq_mul]
      change (Kleiman.twistMod S x (m : ℤ) I * Q.sub I).FG
      rw [Kleiman.twistMod_eq_span (m : ℤ) I hi]
      exact (Submodule.fg_span_singleton _).mul (Q.fg I)
    rw [← hgen I] at hfg ⊢
    obtain ⟨T, hT, hTs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
    exact ⟨T, hT, hTs.symm⟩
  choose T hTsub hTspan using hfin
  let _ : Fintype (Kleiman.Chart x) := Fintype.ofFinite _
  let U : Finset Ω := Finset.univ.biUnion T
  have hUsub : (U : Set Ω) ⊆ L.secs := by
    intro z hz
    obtain ⟨I, -, hzI⟩ := Finset.mem_biUnion.mp hz
    exact hTsub I hzI
  have hUspan : ∀ I, Submodule.span (Kleiman.chartRing S x I) (U : Set Ω) = L.sub I := by
    intro I
    apply le_antisymm
    · rw [← hgen I]
      exact Submodule.span_mono hUsub
    · rw [← hTspan I]
      exact Submodule.span_mono fun z hz => Finset.mem_biUnion.mpr ⟨I, Finset.mem_univ _, hz⟩
  have hsecs : L.secs = secOver S y (β + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := hQ m
  let η : Fin U.card → Ω := fun j => (U.equivFin.symm j : Ω)
  have hrange : Set.range η = (U : Set Ω) := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact (U.equivFin.symm j).2
    · intro hz
      exact ⟨U.equivFin ⟨z, hz⟩, by simp [η]⟩
  have hη : ∀ j, η j ∈ secOver S y (β + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
    intro j
    rw [← hsecs]
    exact hUsub (U.equivFin.symm j).2
  refine ⟨U.card, η, hη, (hCG S K ι Ω y k₀ N e hM _ U.card η hη).mpr fun I => ?_⟩
  rw [hrange, hUspan I]
  exact twist_sub_eq_chartSecOver e β Q hQ m I

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

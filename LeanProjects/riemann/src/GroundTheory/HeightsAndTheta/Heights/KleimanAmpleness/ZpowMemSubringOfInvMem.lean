import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisExtra
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqChartRing
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistBundleToSubSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

section Base

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem mem_of_forall_mem_locIn (B : Subalgebra F Ω) {u : Ω}
    (h : ∀ p : Ideal B, p.IsMaximal → u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn B p) : u ∈ B := by
  let I : Ideal B :=
    { carrier := {a | (a : Ω) * u ∈ B}
      add_mem' := fun {a b} ha hb => by
        show ((a : Ω) + b) * u ∈ B
        rw [add_mul]; exact B.add_mem ha hb
      zero_mem' := by show (0 : Ω) * u ∈ B; rw [zero_mul]; exact B.zero_mem
      smul_mem' := fun c a ha => by
        show ((c : Ω) * a) * u ∈ B
        rw [mul_assoc]; exact B.mul_mem c.2 ha }
  by_cases hI : I = ⊤
  · have h1 : (1 : B) ∈ I := hI ▸ Submodule.mem_top
    have h2 : ((1 : B) : Ω) * u ∈ B := h1
    simpa using h2
  · obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
    have := hp.isPrime
    obtain ⟨a, b, hb, hu⟩ := mem_locIn.mp (h p hp)
    have hb0 : (b : Ω) ≠ 0 := coe_ne_zero_of_not_mem hb
    refine absurd (hIp ?_) hb
    show (b : Ω) * u ∈ B
    rw [hu, mul_div_cancel₀ _ hb0]
    exact a.2

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

omit [Fintype K] [DecidableEq K] in

theorem adjoin_base_le (y : (Σ k, ι k) → Ω) (k₀ : K) (c : ∀ k, ι k) :
    Algebra.adjoin F (Set.range fun i => IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ i / IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ (c k₀)) ≤
      chartRingOver F y c := by
  rw [Algebra.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  exact Algebra.subset_adjoin ⟨⟨k₀, i⟩, rfl⟩

theorem prod_baseDeg (y : (Σ k, ι k) → Ω) (k₀ : K) (c : ∀ k, ι k) (m : ℤ) :
    (∏ k, y ⟨k, c k⟩ ^ (-(m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) = y ⟨k₀, c k₀⟩ ^ (-m) := by
  rw [Finset.prod_eq_single k₀]
  · simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
  · intro k _ hk
    simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg, hk]
  · intro h; exact absurd (Finset.mem_univ k₀) h

theorem zpow_mem_subring_of_inv_mem (z : Subring Ω) {r : Ω} (hr : r ∈ z) (hr' : r⁻¹ ∈ z) (m : ℤ) : r ^ m ∈ z := by
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]; exact z.pow_mem hr n
  · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact z.pow_mem hr' n

theorem secOver_baseDeg_eq (y : (Σ k, ι k) → Ω) (k₀ : K) (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) (m : ℤ) :
    secOver F y (m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
      secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => m) := by
  set x' := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ with hx'
  have hmem : ∀ t, t ∈ secOver F y (m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) ↔
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → t * y ⟨k₀, c k₀⟩ ^ (-m) ∈ chartRingOver F y c := by
    intro t
    simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
      Subalgebra.mem_toSubmodule, prod_baseDeg]
  ext t
  rw [hmem, mem_secOver_oneBlock]
  constructor
  · intro ht j hj
    apply mem_of_forall_mem_locIn
    intro p hp
    have hpp := hp.isPrime
    have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn _ p ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') := by
      refine ⟨fun _ => j, fun _ => hj, ?_⟩
      rw [chartRingOver_oneBlock_eq]
      exact ⟨p, hp.isPrime, rfl⟩
    rw [← hy.2] at hz
    obtain ⟨c, hc, q, hq, hzq⟩ := hz
    have hA : ∀ a ∈ chartRingOver F y c, a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p := fun a ha => by
      rw [hzq, mem_locIn]
      exact ⟨⟨a, ha⟩, 1, fun h => one_not_mem_of_prime hq h, by simp⟩
    have hB : ∀ a ∈ Algebra.adjoin F (Set.range fun i => x' i / x' j), a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p :=
      fun a ha => mem_locIn.mpr ⟨⟨a, ha⟩, 1, fun h => one_not_mem_of_prime hpp h, by simp⟩
    have hyc : y ⟨k₀, c k₀⟩ ≠ 0 := hc k₀
    have hr : y ⟨k₀, c k₀⟩ / x' j ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p := hB _ (Algebra.subset_adjoin ⟨c k₀, rfl⟩)
    have hr' : (y ⟨k₀, c k₀⟩ / x' j)⁻¹ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p := by
      rw [inv_div]
      exact hA _ (Algebra.subset_adjoin ⟨⟨k₀, j⟩, rfl⟩)
    have e : t * x' j ^ (-m) = t * y ⟨k₀, c k₀⟩ ^ (-m) * (y ⟨k₀, c k₀⟩ / x' j) ^ m := by
      rw [div_zpow, zpow_neg, zpow_neg]
      field_simp
    rw [e]
    exact Subring.mul_mem _ (hA _ (ht c hc)) (zpow_mem_subring_of_inv_mem _ hr hr' m)
  · intro ht c hc
    exact adjoin_base_le y k₀ c (ht (c k₀) (hc k₀))

end Base

theorem BaseRealises.proof : BaseRealises.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hy b c
  rw [Kleiman.twistBundle_toSubSystem, Kleiman.twistSys_twist_twistSys, twistSys_secs_eq_secOver, ← add_smul,
    secOver_baseDeg_eq y k₀ hy, hx, secOver_oneBlock_comp]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqChartRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

noncomputable section

section Local

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem spanSecs_mem_locIn_self {A : Subalgebra F Ω} {p : Ideal A} [hp : p.IsPrime] {a : Ω} (ha : a ∈ A) :
    a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  mem_locIn.mpr ⟨⟨a, ha⟩, 1, one_not_mem_of_prime hp, by simp⟩

theorem spanSecs_mul_step {B : Subalgebra F Ω} {q : Ideal B} [hq : q.IsPrime] {T : Set Ω} {u g : Ω}
    (hg : g ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn B q) (hu : ∃ b : B, b ∉ q ∧ (b : Ω) * u ∈ Submodule.span B T) :
    ∃ b : B, b ∉ q ∧ (b : Ω) * (g * u) ∈ Submodule.span B T := by
  obtain ⟨b, hb, hbu⟩ := hu
  obtain ⟨a, b', hb', rfl⟩ := mem_locIn.mp hg
  refine ⟨b' * b, fun h => (hq.mem_or_mem h).elim hb' hb, ?_⟩
  have h0 := coe_ne_zero_of_not_mem hb'
  have e : ((b' * b : B) : Ω) * ((a : Ω) / b' * u) = a • ((b : Ω) * u) := by
    rw [Subalgebra.smul_def, smul_eq_mul, Subalgebra.coe_mul]
    field_simp
  rw [e]
  exact Submodule.smul_mem _ _ hbu

theorem spanSecs_exists_mul_mem (B C : Subalgebra F Ω) (q : Ideal B) [hq : q.IsPrime]
    (hC : ∀ a ∈ C, a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn B q) (T : Set Ω) {u : Ω} (hu : u ∈ Submodule.span C T) :
    ∃ b : B, b ∉ q ∧ (b : Ω) * u ∈ Submodule.span B T := by
  induction hu using Submodule.span_induction with
  | mem z hz => exact ⟨1, one_not_mem_of_prime hq, by simpa using Submodule.subset_span hz⟩
  | zero => exact ⟨1, one_not_mem_of_prime hq, by simp⟩
  | add z w _ _ hz hw =>
    obtain ⟨b₁, hb₁, h₁⟩ := hz
    obtain ⟨b₂, hb₂, h₂⟩ := hw
    refine ⟨b₁ * b₂, fun h => (hq.mem_or_mem h).elim hb₁ hb₂, ?_⟩
    have e : ((b₁ * b₂ : B) : Ω) * (z + w) = b₂ • ((b₁ : Ω) * z) + b₁ • ((b₂ : Ω) * w) := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, Subalgebra.coe_mul]
      ring
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
  | smul a z _ hz =>
    rw [Subalgebra.smul_def, smul_eq_mul]
    exact spanSecs_mul_step (hC _ a.2) hz

theorem spanSecs_mem_of_local (B : Subalgebra F Ω) (T : Set Ω) (u : Ω)
    (h : ∀ q : Ideal B, q.IsMaximal → ∃ b : B, b ∉ q ∧ (b : Ω) * u ∈ Submodule.span B T) :
    u ∈ Submodule.span B T := by
  let J : Ideal B := (Submodule.span B T).comap (LinearMap.toSpanSingleton B Ω u)
  have hJ : ∀ b : B, b ∈ J ↔ (b : Ω) * u ∈ Submodule.span B T := fun b => Iff.rfl
  by_cases hJt : J = ⊤
  · have h1 : (1 : B) ∈ J := hJt ▸ Submodule.mem_top
    simpa using (hJ 1).mp h1
  · obtain ⟨q, hq, hJq⟩ := Ideal.exists_le_maximal J hJt
    obtain ⟨b, hb, hbu⟩ := h q hq
    exact absurd (hJq ((hJ b).mpr hbu)) hb

end Local

theorem SpanSecs.proof : SpanSecs.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod T d s
  have hxv : ∀ i, x i = y ⟨k₀, e.symm i⟩ := fun i => by rw [hx]; rfl

  let B : ι k₀ → Subalgebra F Ω := fun i' =>
    chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => i')
  have hB : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), Kleiman.chartRing F x (Kleiman.singleChart hi) = B (e.symm i) := by
    intro i hi
    rw [← chartRingOver_oneBlock_eq_chartRing (S := F) x (fun _ => i) hi]
    unfold B chartRingOver
    congr 1
    ext z
    constructor
    · rintro ⟨⟨_, l⟩, rfl⟩
      exact ⟨⟨(), e.symm l⟩, by simp [IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec, hxv]⟩
    · rintro ⟨⟨_, l⟩, rfl⟩
      exact ⟨⟨(), e l⟩, by simp [IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec, hxv]⟩

  have hBc : ∀ c : ∀ k, ι k, B (c k₀) ≤ chartRingOver F y c := by
    intro c
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨_, l⟩, rfl⟩
    exact Algebra.subset_adjoin ⟨⟨k₀, l⟩, rfl⟩
  constructor
  · intro hs c hc
    have hi : x (e (c k₀)) ≠ 0 := by rw [hxv, Equiv.symm_apply_apply]; exact hc k₀
    set A := Kleiman.chartRing F x (Kleiman.singleChart hi) with hA
    have hAc : A ≤ chartRingOver F y c := by
      rw [hA, hB, Equiv.symm_apply_apply]; exact hBc c
    have hs' := Submodule.mem_iInf _ |>.mp hs (Kleiman.singleChart hi)
    rw [Submodule.restrictScalars_mem,
      Kleiman.twistMod_eq_span d _ (Finset.mem_singleton_self (e (c k₀)))] at hs'
    have hv : y ⟨k₀, c k₀⟩ = x (e (c k₀)) := by rw [hxv, Equiv.symm_apply_apply]
    rw [hv]
    refine Submodule.mul_induction_on hs' ?_ ?_
    · intro m hm n hn
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hn
      have e1 : m * (a • x (e (c k₀)) ^ d) * x (e (c k₀)) ^ (-d) = (⟨a, hAc a.2⟩ : chartRingOver F y c) • m := by
        rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, zpow_neg]
        field_simp
      rw [e1]
      exact Submodule.smul_mem _ _ (span_subset_span hAc T hm)
    · intro a b ha hb
      rw [add_mul]
      exact Submodule.add_mem _ ha hb
  · intro h
    refine Submodule.mem_iInf _ |>.mpr fun I => ?_
    rw [Submodule.restrictScalars_mem]
    obtain ⟨i, hiI⟩ := I.2.1
    have hi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hiI)
    rw [Kleiman.twistMod_eq_span d I hiI]
    have hle : Kleiman.chartRing F x (Kleiman.singleChart hi) ≤ Kleiman.chartRing F x I :=
      Kleiman.chartRing_mono (Finset.singleton_subset_iff.mpr hiI)

    suffices key : s * x i ^ (-d) ∈ Submodule.span (Kleiman.chartRing F x (Kleiman.singleChart hi)) T by
      have e1 : s = s * x i ^ (-d) * x i ^ d := by
        rw [zpow_neg, mul_assoc, inv_mul_cancel₀ (zpow_ne_zero d hi), mul_one]
      rw [e1]
      exact Submodule.mul_mem_mul (span_subset_span hle T key) (Submodule.subset_span rfl)
    rw [hB i hi]
    have hxi' : y ⟨k₀, e.symm i⟩ ≠ 0 := by rw [← hxv]; exact hi
    refine spanSecs_mem_of_local _ T _ fun q hq => ?_
    have := hq.isPrime

    have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q ∈
        IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) :=
      ⟨fun _ => e.symm i, fun _ => hxi', q, hq.isPrime, rfl⟩
    rw [← hmod.2] at hz
    obtain ⟨c, hc, p, hp, hzp⟩ := hz
    have := hp
    have hCz : ∀ a ∈ chartRingOver F y c, a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q := by
      intro a ha
      rw [hzp]
      exact spanSecs_mem_locIn_self ha

    set w := y ⟨k₀, c k₀⟩ with hw
    set v := y ⟨k₀, e.symm i⟩ with hvdef
    have hw0 : w ≠ 0 := hc k₀
    have h1 : w / v ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q :=
      spanSecs_mem_locIn_self (Algebra.subset_adjoin ⟨⟨(), c k₀⟩, rfl⟩)
    have h2 : v / w ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q :=
      hCz _ (Algebra.subset_adjoin ⟨⟨k₀, e.symm i⟩, rfl⟩)
    have hg : (w / v) ^ d ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q := by
      obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg d
      · rw [zpow_natCast]; exact pow_mem h1 n
      · rw [zpow_neg, zpow_natCast, ← inv_pow, inv_div]; exact pow_mem h2 n
    have e2 : s * x i ^ (-d) = (w / v) ^ d * (s * w ^ (-d)) := by
      rw [hxv, ← hvdef, div_zpow, zpow_neg, zpow_neg]
      field_simp
    rw [e2]
    exact spanSecs_mul_step hg (spanSecs_exists_mul_mem _ _ q hCz T (h c hc))

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

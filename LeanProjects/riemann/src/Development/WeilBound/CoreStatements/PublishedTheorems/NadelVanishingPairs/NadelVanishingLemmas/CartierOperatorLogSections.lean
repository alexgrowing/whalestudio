import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogCartierRoundingFamily
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierMapEqExtDImpEqZero
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogFormsEqChartForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RoundedTwistLocalEquationChartStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

namespace GlobalTheory

theorem mem_logSec_iff {X : Scheme.{0}} [IsIntegral X] {Z : Set X} {G : CartierDiv X} {a : ℕ}
    {U : X.Opens} {η : abelian₂ X.functionField} : η ∈ logSec Z G a U ↔ ∀ y ∈ U, η ∈ logAt Z G a y := by
  simp only [logSec, latSec, AddSubgroup.mem_iInf]

theorem mem_inter_of_forall {X : Scheme.{0}} [IsIntegral X] {ι : Type} (U : ι → X.Opens) (s : Finset ι)
    (y : X) (h : ∀ i ∈ s, y ∈ U i) : y ∈ inter U s := by
  classical
  unfold inter
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.inf_insert]
    exact ⟨h i (Finset.mem_insert_self i s), ih fun k hk => h k (Finset.mem_insert_of_mem hk)⟩

private theorem spanForms_le_of_mem_closure_smul {K : Type} [Field K] (M : Set K) (A : Subring K)
    (hM : ∀ c ∈ M, ∀ b ∈ A, c * b ∈ M) (H H' : Set Ω[K⁄ℤ])
    (hH : ∀ h ∈ H, h ∈ AddSubgroup.closure {w | ∃ b ∈ A, ∃ h' ∈ H', w = b • h'}) :
    ∀ a, spanForms M H a ≤ spanForms M H' a := by
  have key : ∀ a (c : K), c ∈ M → ∀ v : Fin a → Ω[K⁄ℤ],
      (∀ i, v i ∈ AddSubgroup.closure {w | ∃ b ∈ A, ∃ h' ∈ H', w = b • h'}) →
      c • ExteriorAlgebra.ιMulti K a v ∈ spanForms M H' a := by
    intro a
    induction a with
    | zero =>
      intro c hc v _
      exact AddSubgroup.subset_closure ⟨c, hc, v, fun i => i.elim0, rfl⟩
    | succ a ih =>
      intro c hc v hv
      have hpre : ∀ h' ∈ H', ∀ z ∈ spanForms M H' a,
          ExteriorAlgebra.ι K h' * z ∈ spanForms M H' (a + 1) := by
        intro h' hh' z hz
        induction hz using AddSubgroup.closure_induction with
        | mem z hz =>
          obtain ⟨c', hc', v', hv', rfl⟩ := hz
          apply AddSubgroup.subset_closure
          refine ⟨c', hc', Fin.cons h' v', ?_, ?_⟩
          · intro i
            refine Fin.cases hh' (fun k => ?_) i
            simpa using hv' k
          · rw [ExteriorAlgebra.ιMulti_succ_apply, mul_smul_comm]
            rfl
        | zero => simp
        | add z1 z2 _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
        | neg z _ h1 => rw [mul_neg]; exact neg_mem h1
      have claim : ∀ w ∈ AddSubgroup.closure {w | ∃ b ∈ A, ∃ h' ∈ H', w = b • h'}, ∀ c ∈ M,
          c • (ExteriorAlgebra.ι K w * ExteriorAlgebra.ιMulti K a (Matrix.vecTail v)) ∈
            spanForms M H' (a + 1) := by
        intro w hw
        induction hw using AddSubgroup.closure_induction with
        | mem w hw =>
          obtain ⟨b, hb, h', hh', rfl⟩ := hw
          intro c hc
          rw [map_smul, smul_mul_assoc, smul_smul, ← mul_smul_comm]
          exact hpre h' hh' _ (ih (c * b) (hM c hc b hb) _ (fun i => hv i.succ))
        | zero => intro c _; simp
        | add w1 w2 _ _ h1 h2 =>
          intro c hc
          rw [map_add, add_mul, smul_add]
          exact add_mem (h1 c hc) (h2 c hc)
        | neg w _ h1 =>
          intro c hc
          rw [map_neg, neg_mul, smul_neg]
          exact neg_mem (h1 c hc)
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      exact claim _ (hv 0) c hc
  intro a
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨c, hc, v, hv, rfl⟩
  exact key a c hc v (fun i => hH _ (hv i))

private theorem dlog_mul' {K : Type} [Field K] (u v : Kˣ) : dlog (u * v) = dlog u + dlog v := by
  simp only [dlog, dK, Units.val_mul, Derivation.leibniz, smul_add, smul_smul]
  rw [add_comm]
  congr 1 <;> congr 1 <;> simp only [Units.val_inv_eq_inv_val, Units.val_mul, mul_inv_rev] <;> field_simp

private theorem dlog_one' {K : Type} [Field K] : dlog (1 : Kˣ) = 0 := by
  simp [dlog, dK]

private theorem dlog_pow' {K : Type} [Field K] (u : Kˣ) (k : ℕ) : dlog (u ^ k) = k • dlog u := by
  induction k with
  | zero => simp [dlog_one']
  | succ k ih => rw [pow_succ, dlog_mul', ih, succ_nsmul]

private theorem dlog_inv' {K : Type} [Field K] (u : Kˣ) : dlog u⁻¹ = - dlog u := by
  have h := dlog_mul' u u⁻¹
  rw [mul_inv_cancel, dlog_one'] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

private theorem dlog_zpow' {K : Type} [Field K] (u : Kˣ) (m : ℤ) : dlog (u ^ m) = m • dlog u := by
  cases m with
  | ofNat k => rw [Int.ofNat_eq_coe, zpow_natCast, dlog_pow', natCast_zsmul]
  | negSucc k => rw [zpow_negSucc, dlog_inv', dlog_pow', negSucc_zsmul]

private theorem dlog_prod_zpow {K : Type} [Field K] {n : ℕ} (s : Finset (Fin n)) (x : Fin n → Kˣ) (m : Fin n → ℤ) :
    dlog (∏ j ∈ s, x j ^ m j) = ∑ j ∈ s, m j • dlog (x j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dlog_one']
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, dlog_mul', dlog_zpow', ih]

private theorem dK_units_eq_smul_dlog {K : Type} [Field K] (u : Kˣ) : dK (u : K) = (u : K) • dlog u := by
  simp [dlog, smul_smul]

private theorem logUnit_of_unitAt {X : Scheme.{0}} [IsIntegral X] (Z : Set X) {y : X}
    {g : X.functionFieldˣ} (h : UnitAt y (g : X.functionField)) : LogUnit Z y g := by
  obtain ⟨V, hyV, hV⟩ := h.exists_nhds
  intro z hz _
  exact hV z (hz.mem_open V.isOpen hyV)

private theorem exists_unitAt_dK_eq_smul_dlog_of_regAt {X : Scheme.{0}} [IsIntegral X] {y : X} {a : X.functionField} (ha : RegAt y a) :
    ∃ u : X.functionFieldˣ, UnitAt y (u : X.functionField) ∧ ∃ b, RegAt y b ∧ dK a = b • dlog u := by
  obtain ⟨s, rfl⟩ := ha
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self s with hs | hs
  · refine ⟨(hs.map (algebraMap _ X.functionField)).unit, ⟨s, hs, rfl⟩, _, ⟨s, rfl⟩, ?_⟩
    have h := dK_units_eq_smul_dlog (hs.map (algebraMap _ X.functionField)).unit
    rw [IsUnit.unit_spec] at h
    exact h
  · refine ⟨(hs.map (algebraMap _ X.functionField)).unit, ⟨1 - s, hs, rfl⟩, _, ⟨-(1 - s), rfl⟩, ?_⟩
    have h := dK_units_eq_smul_dlog (hs.map (algebraMap _ X.functionField)).unit
    rw [IsUnit.unit_spec] at h
    rw [map_neg, neg_smul, ← h]
    simp [dK, map_sub]

private theorem logAt_le_chartForms_of_isLogChart {X : Scheme.{0}} [IsIntegral X] {Z : Set X} {U : X.Opens} {n : ℕ}
    {x : Fin n → X.functionFieldˣ} {J : Finset (Fin n)} (hc : IsLogChart Z U x J) {y : X} (hy : y ∈ U)
    {D : CartierDiv X} {t : X.functionFieldˣ} (ht : D.IsEqn y t) (a : ℕ) :
    logAt Z D a y ≤ chartForms (locRing y) x J t a := by
  have hM : {c : X.functionField | D.RegularAt y c} = {c | c * (t : X.functionField) ∈ locRing y} :=
    Set.ext fun c => (ht.regularAt_iff).trans mem_locRing.symm
  show spanForms {c | D.RegularAt y c} _ a ≤ spanForms {c | c * (t : X.functionField) ∈ locRing y} _ a
  rw [hM]
  refine spanForms_le_of_mem_closure_smul _ (locRing y) (fun c hc b hb => ?_) _ _ ?_ a
  · show c * b * (t : X.functionField) ∈ locRing y
    rw [mul_right_comm]
    exact (locRing y).mul_mem hc hb
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨u, m, hu, rfl⟩ := (hc.logUnit y hy g).1 hg
  have hch := hc.chart y hy
  have hfr : ∀ k, ∀ b ∈ locRing y, b • frame x J k ∈ AddSubgroup.closure
      {w : Ω[X.functionField⁄ℤ] | ∃ b ∈ locRing y, ∃ h' ∈ Set.range (frame x J), w = b • h'} :=
    fun k b hb => AddSubgroup.subset_closure ⟨b, hb, _, ⟨k, rfl⟩, rfl⟩
  have hdK : ∀ k, ∀ b ∈ locRing y, b • dK (x k : X.functionField) ∈ AddSubgroup.closure
      {w : Ω[X.functionField⁄ℤ] | ∃ b ∈ locRing y, ∃ h' ∈ Set.range (frame x J), w = b • h'} := by
    intro k b hb
    by_cases hk : k ∈ J
    · have h1 : dK (x k : X.functionField) = (x k : X.functionField) • frame x J k := by
        rw [frame, if_pos hk, dK_units_eq_smul_dlog]
      rw [h1, smul_smul]
      exact hfr k _ ((locRing y).mul_mem hb (hch.mem k))
    · have h1 : dK (x k : X.functionField) = frame x J k := by rw [frame, if_neg hk]
      rw [h1]
      exact hfr k b hb
  rw [dlog_mul', dlog_prod_zpow]
  refine add_mem ?_ (sum_mem fun k hk => zsmul_mem ?_ _)
  · obtain ⟨a1, _, ha1⟩ := hu.inv
    obtain ⟨a0, _, ha0⟩ := hu
    have huA : (u : X.functionField) ∈ locRing y := mem_locRing.2 ⟨a0, ha0⟩
    have huiA : ((u⁻¹ : X.functionFieldˣ) : X.functionField) ∈ locRing y := by
      rw [Units.val_inv_eq_inv_val]
      exact mem_locRing.2 ⟨a1, ha1⟩
    obtain ⟨cf, hcf, hdu⟩ := hch.deriv _ huA
    rw [dlog, hdu, Finset.smul_sum]
    exact sum_mem fun k _ => by
      rw [smul_smul]
      exact hdK k _ ((locRing y).mul_mem huiA (hcf k))
  · have h1 : dlog (x k) = (1 : X.functionField) • frame x J k := by rw [frame, if_pos hk, one_smul]
    rw [h1]
    exact hfr k 1 (locRing y).one_mem

private theorem chartForms_le_logAt_of_isLogChart {X : Scheme.{0}} [IsIntegral X] {Z : Set X} {U : X.Opens} {n : ℕ}
    {x : Fin n → X.functionFieldˣ} {J : Finset (Fin n)} (hc : IsLogChart Z U x J) {y : X} (hy : y ∈ U)
    {D : CartierDiv X} {t : X.functionFieldˣ} (ht : D.IsEqn y t) (a : ℕ) :
    chartForms (locRing y) x J t a ≤ logAt Z D a y := by
  classical
  have hM : {c : X.functionField | D.RegularAt y c} = {c | c * (t : X.functionField) ∈ locRing y} :=
    Set.ext fun c => (ht.regularAt_iff).trans mem_locRing.symm
  show spanForms {c | c * (t : X.functionField) ∈ locRing y} _ a ≤ spanForms {c | D.RegularAt y c} _ a
  rw [hM]
  refine spanForms_le_of_mem_closure_smul _ (locRing y) (fun c hc b hb => ?_) _ _ ?_ a
  · show c * b * (t : X.functionField) ∈ locRing y
    rw [mul_right_comm]
    exact (locRing y).mul_mem hc hb
  rintro _ ⟨k, rfl⟩
  by_cases hk : k ∈ J
  · have hlu : LogUnit Z y (x k) := by
      refine (hc.logUnit y hy (x k)).2 ⟨1, fun i => if i = k then 1 else 0, ⟨1, isUnit_one, by simp⟩, ?_⟩
      rw [one_mul, Finset.prod_eq_single k (fun b _ hb => by simp [hb]) (fun h => absurd hk h)]
      simp
    rw [frame, if_pos hk, ← one_smul X.functionField (dlog (x k))]
    exact AddSubgroup.subset_closure ⟨1, (locRing y).one_mem, _, ⟨x k, hlu, rfl⟩, rfl⟩
  · rw [frame, if_neg hk]
    obtain ⟨u, hu, b, hb, hd⟩ := exists_unitAt_dK_eq_smul_dlog_of_regAt (mem_locRing.1 ((hc.chart y hy).mem k))
    rw [hd]
    exact AddSubgroup.subset_closure ⟨b, mem_locRing.2 hb, _, ⟨u, logUnit_of_unitAt Z hu, rfl⟩, rfl⟩

private theorem isEqn_smul_add_sum_smul {X : Scheme.{0}} [IsIntegral X] {C : Type} [Fintype C] (E : C → CartierDiv X)
    (G : CartierDiv X) (r : C → ℕ) (p : ℕ) {n : ℕ} (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n))
    (e : C → Option (Fin n)) (hJ : ∀ j, j ∈ J ↔ ∃ c, e c = some j) (y : X) (t : X.functionFieldˣ)
    (ht : G.IsEqn y t) (hE : ∀ c, (E c).IsEqn y ((e c).elim 1 x)) :
    (p • G + ∑ c, r c • E c).IsEqn y
      (t ^ p * ∏ j ∈ J, x j ^ (∑ c ∈ Finset.univ.filter (fun c => e c = some j), r c)) := by
  classical
  have hs : ∀ s : Finset C, (∑ c ∈ s, r c • E c).IsEqn y (∏ c ∈ s, ((e c).elim 1 x) ^ r c) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using CartierDiv.isEqn_zero y
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact ((hE a).nsmul (r a)).add ih
  have hprod : ∏ j ∈ J, x j ^ (∑ c ∈ Finset.univ.filter (fun c => e c = some j), r c) =
      ∏ c, ((e c).elim 1 x) ^ r c := by
    have h1 : ∀ j, x j ^ (∑ c ∈ Finset.univ.filter (fun c => e c = some j), r c) =
        ∏ c, (if e c = some j then x j ^ r c else 1) := by
      intro j
      rw [← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]
    simp_rw [h1]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun c _ => ?_
    rcases hc : e c with _ | j0
    · simp
    · have hj0 : j0 ∈ J := (hJ j0).2 ⟨c, hc⟩
      simp only [Option.some.injEq, Option.elim_some]
      rw [Finset.prod_ite_eq J j0 (fun j => x j ^ r c), if_pos hj0]
  rw [hprod]
  exact (ht.nsmul p).add (hs _)

theorem cartierAt_atlas_inter : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X]
    [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type}
    [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) →
    ∀ (s : Finset ι), ∀ j ∈ s, ∀ γ, IsCartierMap p (𝒜.x j) γ →
    CartierAt (extD _) γ (fun a => logSec (suppAll E) G a (inter 𝒜.U s))
      (fun a => logSec (suppAll E) (p • G + ∑ c, r c • E c) a (inter 𝒜.U s)) := by
  intro p _ X _ _ C _ E n ι _ 𝒜 G r hr s j hj γ hγ
  classical
  obtain ⟨e, he_inj, hJ, heqn⟩ := 𝒜.snc j
  have hW : ∀ w ∈ inter 𝒜.U s, w ∈ 𝒜.U j := fun w hw => (Finset.inf_le hj : inter 𝒜.U s ≤ 𝒜.U j) hw
  have hcoord : IsCoord (𝒜.x j) := ((𝒜.chart j).chart _ (𝒜.gen j)).coord
  have hR : ∀ j', (∑ c ∈ Finset.univ.filter (fun c => e c = some j'), r c) < p := by
    intro j'
    by_cases hne : ∃ c, e c = some j'
    · obtain ⟨c0, hc0⟩ := hne
      have h1 : Finset.univ.filter (fun c => e c = some j') = {c0} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => he_inj c c0 j' h hc0, fun h => h ▸ hc0⟩
      rw [h1, Finset.sum_singleton]
      exact hr c0
    · have h1 : Finset.univ.filter (fun c => e c = some j') = ∅ := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        exact fun h => hne ⟨c, h⟩
      rw [h1, Finset.sum_empty]
      exact (Fact.out : p.Prime).pos
  choose tG htG using fun w : X => G.exists_isEqn w
  have hLe : ∀ (D : CartierDiv X) (w : X), w ∈ 𝒜.U j → ∀ (t : X.functionFieldˣ), D.IsEqn w t → ∀ a,
      logAt (suppAll E) D a w = chartForms (locRing w) (𝒜.x j) (𝒜.J j) t a :=
    fun D w hw t ht a => le_antisymm (logAt_le_chartForms_of_isLogChart (𝒜.chart j) hw ht a) (chartForms_le_logAt_of_isLogChart (𝒜.chart j) hw ht a)
  have hG' : ∀ w ∈ 𝒜.U j, (p • G + ∑ c, r c • E c).IsEqn w
      (tG w ^ p * ∏ j' ∈ 𝒜.J j, 𝒜.x j j' ^ (∑ c ∈ Finset.univ.filter (fun c => e c = some j'), r c)) :=
    fun w hw => isEqn_smul_add_sum_smul E G r p (𝒜.x j) (𝒜.J j) e hJ w (tG w) (htG w) (fun c => heqn c w hw)
  haveI hY : Nonempty {w : X // w ∈ inter 𝒜.U s} :=
    ⟨⟨genericPoint X, mem_inter_of_forall _ _ _ (fun i _ => 𝒜.gen i)⟩⟩
  have hfam := fun a η => logCartier_rounding_family X.functionField p n (𝒜.x j) (𝒜.J j) γ
    {w : X // w ∈ inter 𝒜.U s} (fun w => locRing w.1) (fun w => tG w.1)
    (fun _ j' => ∑ c ∈ Finset.univ.filter (fun c => e c = some j'), r c)
    (fun w => (𝒜.chart j).chart w.1 (hW _ w.2)) (fun _ => hR) hγ a η
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _ h0
    exact cartierMap_eq_extD_imp_eq_zero _ p n (𝒜.x j) γ hcoord hγ x 0 (by rw [h0, map_zero])
  · intro a x _ z _ h
    exact cartierMap_eq_extD_imp_eq_zero _ p n (𝒜.x j) γ hcoord hγ x z h
  · intro y hy hd
    obtain ⟨ζ, ξ, hζ, _, h0, hyeq⟩ := hfam 0 y (fun w => by
      rw [← hLe _ _ (hW _ w.2) _ (hG' _ (hW _ w.2))]
      exact (mem_logSec_iff.1 hy) w.1 w.2) hd
    refine ⟨ζ, mem_logSec_iff.2 fun w hw => ?_, ?_⟩
    · rw [hLe _ _ (hW _ hw) _ (htG w)]
      exact hζ ⟨w, hw⟩
    · rw [hyeq, h0 rfl, map_zero, add_zero]
  · intro a y hy hd
    obtain ⟨ζ, ξ, hζ, hξ, _, hyeq⟩ := hfam (a + 1) y (fun w => by
      rw [← hLe _ _ (hW _ w.2) _ (hG' _ (hW _ w.2))]
      exact (mem_logSec_iff.1 hy) w.1 w.2) hd
    refine ⟨ζ, mem_logSec_iff.2 fun w hw => ?_, ξ, mem_logSec_iff.2 fun w hw => ?_, hyeq⟩
    · rw [hLe _ _ (hW _ hw) _ (htG w)]
      exact hζ ⟨w, hw⟩
    · rw [hLe _ _ (hW _ hw) _ (hG' _ (hW _ hw))]
      exact hξ ⟨w, hw⟩ a rfl

end GlobalTheory

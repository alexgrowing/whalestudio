import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WS.Orbit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem zero_mem_Ln {n : ℤ} : (0 : F × F) ∈ Ln F n := ⟨zero_mem _, zero_mem _⟩

theorem Ln_add {n : ℤ} {v w : F × F} (hv : v ∈ Ln F n) (hw : w ∈ Ln F n) : v + w ∈ Ln F n :=
  ⟨add_mem hv.1 hw.1, add_mem hv.2 hw.2⟩

theorem Ln_sub {n : ℤ} {v w : F × F} (hv : v ∈ Ln F n) (hw : w ∈ Ln F n) : v - w ∈ Ln F n :=
  ⟨sub_mem hv.1 hw.1, sub_mem hv.2 hw.2⟩

theorem Ln_neg {n : ℤ} {v : F × F} (hv : v ∈ Ln F n) : -v ∈ Ln F n :=
  ⟨neg_mem hv.1, neg_mem hv.2⟩

theorem Ln_smul {n : ℤ} {a : F} {v : F × F} (ha : a ∈ valBall F 0) (hv : v ∈ Ln F n) :
    a • v ∈ Ln F n := by
  have h1 := mul_mem_valBall ha hv.1
  have h2 := mul_mem_valBall ha hv.2
  rw [zero_add] at h1 h2
  exact ⟨h1, h2⟩

theorem isOpen_Ln (n : ℤ) : IsOpen (Ln F n) :=
  ((isOpen_valBall n).preimage continuous_fst).inter ((isOpen_valBall n).preimage continuous_snd)

theorem unif_mem : (unifUnit F : F) ∈ valBall F 1 :=
  (mem_valBall_iff_le_ord (unifUnit F).ne_zero).2 (by rw [ord_unifUnit])

theorem mem_zero_of_unit {t : Fˣ} (ht : t ∈ unitFiltrationUnits F 0) : (t : F) ∈ valBall F 0 :=
  (mem_valBall_iff_le_ord t.ne_zero).2 (mem_unitFiltrationUnits_zero_iff_ord.1 ht).ge

theorem unit_or_mul {a : F} (ha : a ∈ 𝒪[F]) :
    (∃ t : Fˣ, t ∈ unitFiltrationUnits F 0 ∧ (t : F) = a) ∨
      ∃ b ∈ 𝒪[F], a = b * (unifUnit F : F) := by
  have hϖ : (unifUnit F : F) ≠ 0 := (unifUnit F).ne_zero
  by_cases h0 : a = 0
  · exact Or.inr ⟨0, zero_mem _, by simp [h0]⟩
  have hord : 0 ≤ ord a := (mem_valBall_iff_le_ord h0).1 (mem_valBall_zero_iff.2 ha)
  rcases hord.eq_or_lt with h | h
  · exact Or.inl ⟨Units.mk0 a h0, mem_unitFiltrationUnits_zero_iff_ord.2 (by simpa using h.symm), rfl⟩
  · refine Or.inr ⟨a * (unifUnit F : F)⁻¹, ?_, by field_simp⟩
    have hb : a * (unifUnit F : F)⁻¹ ≠ 0 := mul_ne_zero h0 (inv_ne_zero hϖ)
    rw [← mem_valBall_zero_iff, mem_valBall_iff_le_ord hb, ord_mul h0 (inv_ne_zero hϖ),
      ord_inv hϖ, ord_unifUnit]
    omega

theorem unit_sub {t : Fˣ} (ht : t ∈ unitFiltrationUnits F 0) {b : F} (hb : b ∈ 𝒪[F]) :
    ∃ c : Fˣ, c ∈ unitFiltrationUnits F 0 ∧ (c : F) = t - b * (unifUnit F : F) := by
  have hv : ValuativeRel.valuation F (t : F) = 1 := mem_unitFiltrationUnits_zero_iff.1 ht
  have hm : b * (unifUnit F : F) ∈ valBall F 1 := by
    have := mul_mem_valBall (mem_valBall_zero_iff.2 hb) (unif_mem (F := F))
    simpa using this
  have hlt := mem_valBall_one_iff.1 hm
  have hc : ValuativeRel.valuation F ((t : F) - b * (unifUnit F : F)) = 1 := by
    rw [Valuation.map_sub_eq_of_lt_left _ (by rw [hv]; exact hlt), hv]
  have h0 : (t : F) - b * (unifUnit F : F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact zero_ne_one hc
  exact ⟨Units.mk0 _ h0, mem_unitFiltrationUnits_zero_iff.2 (by simpa using hc), rfl⟩

theorem exists_equivalence_class_representatives {α : Type} (R : α → α → Prop) (hr : ∀ a, R a a)
    (hs : ∀ a b, R a b → R b a) (ht : ∀ a b c, R a b → R b c → R a c) (T : Finset α) :
    ∃ s : Finset α, (∀ t ∈ s, t ∈ T) ∧ (∀ t ∈ T, ∃ t' ∈ s, R t t') ∧
      ∀ t ∈ s, ∀ t' ∈ s, R t t' → t = t' := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | insert a T _ ih =>
    obtain ⟨s, h1, h2, h3⟩ := ih
    by_cases h : ∃ t' ∈ s, R a t'
    · refine ⟨s, fun t a' => Finset.mem_insert_of_mem (h1 t a'), fun t ht' => ?_, h3⟩
      rcases Finset.mem_insert.1 ht' with rfl | ht'
      · exact h
      · exact h2 t ht'
    · push Not at h
      refine ⟨insert a s, fun t ht' => ?_, fun t ht' => ?_, fun t ht1 t' ht2 hR => ?_⟩
      · rcases Finset.mem_insert.1 ht' with rfl | ht'
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (h1 t ht')
      · rcases Finset.mem_insert.1 ht' with rfl | ht'
        · exact ⟨t, Finset.mem_insert_self _ _, hr t⟩
        · obtain ⟨u, hu, hR⟩ := h2 t ht'
          exact ⟨u, Finset.mem_insert_of_mem hu, hR⟩
      · rcases Finset.mem_insert.1 ht1 with e1 | e1 <;>
          rcases Finset.mem_insert.1 ht2 with e2 | e2
        · rw [e1, e2]
        · exact absurd (e1 ▸ hR) (h t' e2)
        · exact absurd (e2 ▸ hs _ _ hR) (h t e1)
        · exact h3 t e1 t' e2 hR

theorem exists_reps (n : ℤ) (x : F × F) :
    ∃ s : Finset Fˣ, (∀ t ∈ s, t ∈ unitFiltrationUnits F 0) ∧
      (∀ t ∈ unitFiltrationUnits F 0, ∃ t' ∈ s, ((t : F) - t') • x ∈ Ln F n) ∧
      ∀ t ∈ s, ∀ t' ∈ s, ((t : F) - t') • x ∈ Ln F n → t = t' := by
  have hopen : ∀ c : Fˣ, IsOpen {t : Fˣ | ((t : F) - c) • x ∈ Ln F n} := fun c =>
    (isOpen_Ln n).preimage
      (((Units.continuous_val.sub continuous_const).smul continuous_const))
  obtain ⟨T, hT, hcov⟩ := (isCompact_unitFiltrationUnits (K := F) 0).elim_nhds_subcover
    (fun c => {t : Fˣ | ((t : F) - c) • x ∈ Ln F n})
    (fun c _ => (hopen c).mem_nhds (by
      rw [Set.mem_setOf_eq, sub_self, zero_smul]
      exact zero_mem_Ln))
  obtain ⟨s, h1, h2, h3⟩ := exists_equivalence_class_representatives (fun a b : Fˣ => ((a : F) - b) • x ∈ Ln F n)
    (fun a => by
      rw [sub_self, zero_smul]
      exact zero_mem_Ln)
    (fun a b h => by
      have := Ln_neg h
      rwa [← neg_smul, neg_sub] at this)
    (fun a b c h h' => by
      have := Ln_add h h'
      rwa [← add_smul, sub_add_sub_cancel] at this) T
  refine ⟨s, fun t ht => hT t (h1 t ht), fun t ht => ?_, h3⟩
  obtain ⟨c, hc, hct⟩ := Set.mem_iUnion₂.1 (hcov ht)
  obtain ⟨t', ht', hR⟩ := h2 c hc
  refine ⟨t', ht', ?_⟩
  have := Ln_add hct hR
  rwa [← add_smul, sub_add_sub_cancel] at this

theorem main : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F), x ∉ GlobalTheory.CompanionTheory.WS.Ln F n → ∃ s : Finset Fˣ, s.Nonempty ∧ (∀ t ∈ s, t ∈ unitFiltrationUnits F 0) ∧ (GlobalTheory.CompanionTheory.WS.spanSet n x).indicator (1 : F × F → ℂ) - (GlobalTheory.CompanionTheory.WS.spanSet n (((unifUnit F : Fˣ) : F) • x)).indicator (1 : F × F → ℂ) = ∑ t ∈ s, GlobalTheory.CompanionTheory.WS.cosetInd n ((t : F) • x) := by
  intro F _ _ _ _ _ _ n x hx
  obtain ⟨s, hU, hcov, hinj⟩ := exists_reps n x
  have hne : s.Nonempty := by
    obtain ⟨t, ht, -⟩ := hcov 1 (one_mem _)
    exact ⟨t, ht⟩
  refine ⟨s, hne, hU, ?_⟩

  have hBA : ∀ v, v ∈ spanSet n ((unifUnit F : F) • x) → v ∈ spanSet n x := by
    rintro v ⟨a, ha, hv⟩
    refine ⟨a * (unifUnit F : F), ?_, ?_⟩
    · exact mul_mem ha (mem_valBall_zero_iff.1 (valBall_antitone (by omega) (unif_mem (F := F))))
    · rwa [mul_smul]

  have hfw : ∀ v, v ∈ spanSet n x → v ∉ spanSet n ((unifUnit F : F) • x) →
      ∃ t ∈ s, v - (t : F) • x ∈ Ln F n := by
    rintro v ⟨a, ha, hv⟩ hvB
    rcases unit_or_mul ha with ⟨t, ht, rfl⟩ | ⟨b, hb, rfl⟩
    · obtain ⟨t', ht', hR⟩ := hcov t ht
      refine ⟨t', ht', ?_⟩
      have := Ln_add hv hR
      rwa [show v - (t : F) • x + ((t : F) - t') • x = v - (t' : F) • x by
        rw [sub_smul]; abel] at this
    · exact absurd ⟨b, hb, by rwa [← mul_smul]⟩ hvB

  have hbw : ∀ v, ∀ t ∈ s, v - (t : F) • x ∈ Ln F n → v ∉ spanSet n ((unifUnit F : F) • x) := by
    rintro v t ht hv ⟨b, hb, hvb⟩
    obtain ⟨c, hc, hct⟩ := unit_sub (hU t ht) hb
    have h1 : (c : F) • x ∈ Ln F n := by
      have := Ln_sub hvb hv
      rwa [show v - b • (unifUnit F : F) • x - (v - (t : F) • x) = (c : F) • x by
        rw [hct, sub_smul, mul_smul]; abel] at this
    have h2 := Ln_smul (mem_zero_of_unit (inv_mem hc)) h1
    rw [smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ c.ne_zero, one_smul] at h2
    exact hx h2
  funext v
  rw [Finset.sum_apply, Pi.sub_apply]
  by_cases h : ∃ t ∈ s, v - (t : F) • x ∈ Ln F n
  · obtain ⟨t, ht, hv⟩ := h
    have hA : v ∈ spanSet n x :=
      ⟨t, mem_valBall_zero_iff.1 (mem_zero_of_unit (hU t ht)), hv⟩
    rw [Set.indicator_of_mem hA, Set.indicator_of_notMem (hbw v t ht hv),
      Finset.sum_eq_single t]
    · simp [cosetInd, Set.indicator, hv]
    · intro t' ht' hne'
      have : v - (t' : F) • x ∉ Ln F n := fun hv' => by
        refine hne' (hinj t' ht' t ht ?_)
        have := Ln_sub hv hv'
        rwa [show v - (t : F) • x - (v - (t' : F) • x) = ((t' : F) - t) • x by
          rw [sub_smul]; abel] at this
      simp [cosetInd, Set.indicator, this]
    · exact fun h' => absurd ht h'
  · push Not at h
    have hz : ∑ t ∈ s, cosetInd n ((t : F) • x) v = 0 :=
      Finset.sum_eq_zero fun t ht => by simp [cosetInd, Set.indicator, h t ht]
    rw [hz]
    by_cases hB : v ∈ spanSet n ((unifUnit F : F) • x)
    · rw [Set.indicator_of_mem hB, Set.indicator_of_mem (hBA v hB), sub_self]
    · have hA : v ∉ spanSet n x := fun hA => by
        obtain ⟨t, ht, hv⟩ := hfw v hA hB
        exact h t ht hv
      rw [Set.indicator_of_notMem hB, Set.indicator_of_notMem hA, sub_self]

end GlobalTheory.CompanionTheory.WS.Orbit

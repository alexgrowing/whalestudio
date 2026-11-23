import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteria
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VLtOneOfOrdLEqOne

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT Formalism.UG
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.DcosProduct

section Abstract

variable {G : Type} [Group G]

def dc (I : Subgroup G) (t : G) : Set G := {y | ∃ x ∈ I, ∃ z ∈ I, y = x * t * z}

theorem mem_dc_mul {I : Subgroup G} {t t' : G}
    (hf : ∀ g ∈ I, ∃ a ∈ I, ∃ b ∈ I, g = a * b ∧ t * a * t⁻¹ ∈ I ∧ t'⁻¹ * b * t' ∈ I)
    {z m : G} (h1 : z ∈ dc I t) (h2 : z⁻¹ * m ∈ dc I t') : m ∈ dc I (t * t') := by
  obtain ⟨x, hx, y, hy, rfl⟩ := h1
  obtain ⟨p, hp, r, hr, e⟩ := h2
  obtain ⟨a, -, b, -, hab, ha, hb⟩ := hf (y * p) (mul_mem hy hp)
  refine ⟨x * (t * a * t⁻¹), mul_mem hx ha, (t'⁻¹ * b * t') * r, mul_mem hb hr, ?_⟩
  have : m = x * t * (y * p) * t' * r := by
    have e' : m = (x * t * y) * (p * t' * r) := by rw [← e]; group
    rw [e']; group
  rw [this, hab]; group

theorem inv_mul_mem_of_dc {I : Subgroup G} {t t' : G}
    (hf : ∀ g ∈ I, ∃ a ∈ I, ∃ b ∈ I, g = a * b ∧ t * a * t⁻¹ ∈ I ∧ t'⁻¹ * b * t' ∈ I)
    (hc : ∀ g ∈ I, (t * t')⁻¹ * g * (t * t') ∈ I → t⁻¹ * g * t ∈ I)
    {z : G} (h1 : z ∈ dc I t) (h2 : z⁻¹ * (t * t') ∈ dc I t') : t⁻¹ * z ∈ I := by
  obtain ⟨x, hx, y, hy, rfl⟩ := h1
  obtain ⟨p, hp, r, hr, e⟩ := h2
  obtain ⟨a, haI, b, -, hab, ha, hb⟩ := hf (y * p) (mul_mem hy hp)
  have e1 : t * t' = x * t * (y * p) * t' * r := by
    have e' : t * t' = (x * t * y) * (p * t' * r) := by rw [← e]; group
    rw [e']; group
  rw [hab] at e1
  set j := t * a * t⁻¹ with hj
  set c := (t'⁻¹ * b * t') * r with hcd
  have hcI : c ∈ I := mul_mem hb hr
  have e2 : t * t' = (x * j) * (t * t') * c := by
    rw [hcd, hj]
    refine e1.trans ?_
    group
  have e3 : (t * t')⁻¹ * (x * j) * (t * t') = c⁻¹ := by
    have : (x * j) * (t * t') = (t * t') * c⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]; exact e2.symm
    rw [mul_assoc, this]; group
  have h3 := hc (x * j) (mul_mem hx ha) (e3 ▸ inv_mem hcI)
  have h4 : t⁻¹ * x * t = (t⁻¹ * (x * j) * t) * a⁻¹ := by rw [hj]; group
  have h5 : t⁻¹ * x * t ∈ I := h4 ▸ mul_mem h3 (inv_mem haI)
  have h6 : t⁻¹ * (x * t * y) = (t⁻¹ * x * t) * y := by group
  rw [h6]
  exact mul_mem h5 hy

theorem hint_coset {K I : Subgroup G} (hIK : I ≤ K) {u : G → ℂ} (z₀ : G)
    (hu : ∀ z, u z = if z₀⁻¹ * z ∈ I then 1 else 0) : hint K u = ((I.relIndex K : ℕ) : ℂ)⁻¹ := by
  have hR : rStab u ⊓ K = I := by
    ext g
    constructor
    · rintro ⟨h, -⟩
      have h' : u (z₀ * g) = u z₀ := h z₀
      rw [hu, hu, inv_mul_cancel, if_pos (one_mem _), inv_mul_cancel_left] at h'
      by_contra hg
      rw [if_neg hg] at h'
      exact zero_ne_one h'
    · intro hg
      refine ⟨fun x => ?_, hIK hg⟩
      rw [hu, hu]
      have : z₀⁻¹ * (x * g) ∈ I ↔ z₀⁻¹ * x ∈ I := by
        rw [← mul_assoc]; exact Subgroup.mul_mem_cancel_right _ hg
      simp only [this]
  unfold hint
  rw [hR, finsum_eq_single _ (z₀ : G ⧸ I)]
  · rw [hu, if_pos (QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm), mul_one]
  · intro q hq
    rw [hu, if_neg]
    intro h
    apply hq
    rw [← QuotientGroup.out_eq' q]
    exact (QuotientGroup.eq.2 h).symm

theorem hint_zero (K : Subgroup G) {u : G → ℂ} (hu : ∀ z, u z = 0) : hint K u = 0 := by
  unfold hint
  simp [hu]

theorem hint_conv {K I : Subgroup G} (hIK : I ≤ K) {t t' : G}
    (hf : ∀ g ∈ I, ∃ a ∈ I, ∃ b ∈ I, g = a * b ∧ t * a * t⁻¹ ∈ I ∧ t'⁻¹ * b * t' ∈ I)
    (hc : ∀ g ∈ I, (t * t')⁻¹ * g * (t * t') ∈ I → t⁻¹ * g * t ∈ I) (m : G) :
    hint K (fun z => (if z ∈ dc I t then (1 : ℂ) else 0) * (if z⁻¹ * m ∈ dc I t' then 1 else 0)) =
      ((I.relIndex K : ℕ) : ℂ)⁻¹ * (if m ∈ dc I (t * t') then 1 else 0) := by
  by_cases hm : m ∈ dc I (t * t')
  · rw [if_pos hm, mul_one]
    obtain ⟨i, hi, i', hi', rfl⟩ := hm
    refine hint_coset hIK (i * t) fun z => ?_
    by_cases hz : (i * t)⁻¹ * z ∈ I
    · have h1 : z ∈ dc I t := ⟨i, hi, _, hz, by group⟩
      have h2 : z⁻¹ * (i * (t * t') * i') ∈ dc I t' :=
        ⟨((i * t)⁻¹ * z)⁻¹, inv_mem hz, i', hi', by group⟩
      rw [if_pos h1, if_pos h2, if_pos hz, one_mul]
    · rw [if_neg hz]
      by_cases h1 : z ∈ dc I t
      · by_cases h2 : z⁻¹ * (i * (t * t') * i') ∈ dc I t'
        · exfalso
          apply hz
          have h1' : i⁻¹ * z ∈ dc I t := by
            obtain ⟨x, hx, y, hy, rfl⟩ := h1
            exact ⟨i⁻¹ * x, mul_mem (inv_mem hi) hx, y, hy, by group⟩
          have h2' : (i⁻¹ * z)⁻¹ * (t * t') ∈ dc I t' := by
            obtain ⟨x, hx, y, hy, e⟩ := h2
            refine ⟨x, hx, y * i'⁻¹, mul_mem hy (inv_mem hi'), ?_⟩
            have : (i⁻¹ * z)⁻¹ * (t * t') = z⁻¹ * (i * (t * t') * i') * i'⁻¹ := by group
            rw [this, e]; group
          have := inv_mul_mem_of_dc hf hc h1' h2'
          have e : (i * t)⁻¹ * z = t⁻¹ * (i⁻¹ * z) := by group
          rwa [e]
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
  · rw [if_neg hm, mul_zero]
    refine hint_zero K fun z => ?_
    by_cases h1 : z ∈ dc I t
    · by_cases h2 : z⁻¹ * m ∈ dc I t'
      · exact absurd (mem_dc_mul hf h1 h2) hm
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

end Abstract

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem val_unif {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) :
    ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) =
      ValuativeRel.uniformizer (w.adicCompletion E) := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have h1 : Valued.v (ϖ : w.adicCompletion E) < 1 :=
    GlobalTheory.CompanionTheory.IwahoriContraction.v_lt_one_of_ordL_eq_one w ϖ.ne_zero hϖ.1
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (ValuativeRel.uniformizer (w.adicCompletion E))
  apply le_antisymm
  · rw [ValuativeRel.le_uniformizer_iff]
    exact e.lt_one_iff_lt_one.2 h1
  · rw [← hy]
    have h2 : Valued.v y < 1 := e.lt_one_iff_lt_one.1 (hy ▸ ValuativeRel.uniformizer_lt_one)
    exact (e _ _).2 (GlobalTheory.CompanionTheory.IwahoriContraction.v_le_of_ordL_eq_one w ϖ.ne_zero hϖ.1 h2)

theorem tdiag_add {w : Pl E} {n : ℕ} (ϖ : (w.adicCompletion E)ˣ) (x x' : Fin n → ℤ) :
    tdiag ϖ (x + x') = tdiag ϖ x * tdiag ϖ x' := by
  unfold tdiag
  rw [← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]

theorem iw_fact {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {n : ℕ} {x x' : Fin n → ℤ}
    (hx : Antitone x) (hx' : Antitone x') :
    ∀ g ∈ iwGL n w, ∃ a ∈ iwGL n w, ∃ b ∈ iwGL n w, g = a * b ∧
      tdiag ϖ x * a * (tdiag ϖ x)⁻¹ ∈ iwGL n w ∧ (tdiag ϖ x')⁻¹ * b * tdiag ϖ x' ∈ iwGL n w := by
  intro g hg
  have c1 := GlobalTheory.IwahoriTraceProof.dominantContracts (k := w.adicCompletion E) (n := Fin n) ϖ (val_unif hϖ) x hx
  have c2 := GlobalTheory.IwahoriTraceProof.dominantContracts (k := w.adicCompletion E) (n := Fin n) ϖ (val_unif hϖ) x' hx'
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := GlobalTheory.IwahoriTraceProof.iwahori_factorisation hg
  have hdI := GlobalTheory.SmGL.diagT_mem_iwahori hd
  have huI := (GlobalTheory.IwahoriTraceProof.mem_unipO_iff hu.1).2 hu
  have hcI := GlobalTheory.SmGL.KOne_le_iwahori _ _ hc.2
  refine ⟨_, mul_mem huI hdI, c, hcI, rfl, ?_, GlobalTheory.SmGL.KOne_le_iwahori _ _ (c2.2 c hc).2⟩
  have hcomm : tdiag ϖ x * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) d * (tdiag ϖ x)⁻¹ =
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) d := by
    unfold tdiag
    rw [← map_mul, mul_comm, map_mul]
    group
  have h1 := c1.1 u hu
  have h1I := (GlobalTheory.IwahoriTraceProof.mem_unipO_iff h1.1).2 h1
  have e : tdiag ϖ x * (u * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) d) * (tdiag ϖ x)⁻¹ =
      (tdiag ϖ x * u * (tdiag ϖ x)⁻¹) *
        (tdiag ϖ x * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) d * (tdiag ϖ x)⁻¹) := by group
  rw [e, hcomm]
  exact mul_mem h1I hdI

theorem conj_entry {w : Pl E} {n : ℕ} (ϖ : (w.adicCompletion E)ˣ) (x : Fin n → ℤ) (g : GLw n w) (i j : Fin n) :
    ((tdiag ϖ x)⁻¹ * g * tdiag ϖ x).val i j = ((ϖ ^ (x j - x i) : (w.adicCompletion E)ˣ) : w.adicCompletion E) * g.val i j := by
  have h := GlobalTheory.IwahoriTraceProof.diag_mul_mul_diag (k := w.adicCompletion E) (fun i => ϖ ^ x i)⁻¹ (fun i => ϖ ^ x i) g i j
  rw [map_inv] at h
  unfold tdiag
  rw [h]
  congr 2
  rw [_root_.zpow_sub]
  exact mul_comm _ _

theorem v_zpow_le_one {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {k : ℤ} (hk : 0 ≤ k) :
    Valued.v ((ϖ ^ k : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1 := by
  have h1 : Valued.v (ϖ : w.adicCompletion E) < 1 :=
    GlobalTheory.CompanionTheory.IwahoriContraction.v_lt_one_of_ordL_eq_one w ϖ.ne_zero hϖ.1
  have h0 : 0 < Valued.v (ϖ : w.adicCompletion E) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ϖ.ne_zero)
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact zpow_le_one₀ h0 h1.le hk

theorem int_entries {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {n : ℕ} {x x' : Fin n → ℤ}
    (hx : Antitone x) (hx' : Antitone x') {g : GLw n w} (h1 : ∀ i j, Valued.v (g.val i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (((tdiag ϖ (x + x'))⁻¹ * g * tdiag ϖ (x + x')).val i j) ≤ 1) (i j : Fin n) :
    Valued.v (((tdiag ϖ x)⁻¹ * g * tdiag ϖ x).val i j) ≤ 1 := by
  rw [conj_entry]
  rcases le_total i j with h | h
  · have a1 := hx' h
    have e : ((ϖ ^ (x j - x i) : (w.adicCompletion E)ˣ) : w.adicCompletion E) * g.val i j =
        ((ϖ ^ (x' i - x' j) : (w.adicCompletion E)ˣ) : w.adicCompletion E) *
          (((tdiag ϖ (x + x'))⁻¹ * g * tdiag ϖ (x + x')).val i j) := by
      rw [conj_entry, ← mul_assoc, ← Units.val_mul, ← _root_.zpow_add]
      congr 3
      simp only [Pi.add_apply]
      ring
    rw [e, map_mul]
    exact mul_le_one' (v_zpow_le_one hϖ (by omega)) (h2 i j)
  · have a1 := hx h
    rw [map_mul]
    exact mul_le_one' (v_zpow_le_one hϖ (by omega)) (h1 i j)

theorem iw_chain {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {n : ℕ} {x x' : Fin n → ℤ}
    (hx : Antitone x) (hx' : Antitone x') :
    ∀ g ∈ iwGL n w, (tdiag ϖ x * tdiag ϖ x')⁻¹ * g * (tdiag ϖ x * tdiag ϖ x') ∈ iwGL n w →
      (tdiag ϖ x)⁻¹ * g * tdiag ϖ x ∈ iwGL n w := by
  intro g hg hg'
  rw [← tdiag_add] at hg'
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1.1 hg
  obtain ⟨p1, p2, -⟩ := (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1.1 hg'
  have e : ∀ t : GLw n w, (t⁻¹ * g * t)⁻¹ = t⁻¹ * g⁻¹ * t := fun t => by group
  refine (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1.2
    ⟨int_entries hϖ hx hx' h1 p1, ?_, fun i j hij => ?_⟩
  · rw [e]
    exact int_entries hϖ hx hx' h2 (by rw [← e]; exact p2)
  · rw [conj_entry, map_mul]
    have a1 := hx hij.le
    exact (mul_le_of_le_one_left' (v_zpow_le_one hϖ (by omega))).trans_lt (h3 i j hij)

theorem iwGL_le (w : Pl E) (n : ℕ) : iwGL n w ≤ GlobalTheory.LFun.KGL w n := fun g hg => by
  obtain ⟨h1, h2, -⟩ := (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1.1 hg
  exact (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).2.2 ⟨h1, h2⟩

theorem dcos_mul_eq {a b : ℕ} (w : Pl E) (t : GLw a w) (s : GLw b w) (y : GLw a w × GLw b w) :
    dcos a w t y.1 * dcos b w s y.2 = if y ∈ dc ((iwGL a w).prod (iwGL b w)) (t, s) then 1 else 0 := by
  have key : y ∈ dc ((iwGL a w).prod (iwGL b w)) (t, s) ↔
      (∃ x ∈ iwGL a w, ∃ z ∈ iwGL a w, y.1 = x * t * z) ∧ ∃ x ∈ iwGL b w, ∃ z ∈ iwGL b w, y.2 = x * s * z := by
    constructor
    · rintro ⟨p, hp, q, hq, rfl⟩
      exact ⟨⟨p.1, (Subgroup.mem_prod.1 hp).1, q.1, (Subgroup.mem_prod.1 hq).1, rfl⟩,
        ⟨p.2, (Subgroup.mem_prod.1 hp).2, q.2, (Subgroup.mem_prod.1 hq).2, rfl⟩⟩
    · rintro ⟨⟨p, hp, q, hq, e⟩, p', hp', q', hq', e'⟩
      exact ⟨(p, p'), Subgroup.mem_prod.2 ⟨hp, hp'⟩, (q, q'), Subgroup.mem_prod.2 ⟨hq, hq'⟩, Prod.ext e e'⟩
  unfold dcos
  by_cases h1 : ∃ x ∈ iwGL a w, ∃ z ∈ iwGL a w, y.1 = x * t * z
  · by_cases h2 : ∃ x ∈ iwGL b w, ∃ z ∈ iwGL b w, y.2 = x * s * z
    · rw [if_pos h1, if_pos h2, if_pos (key.2 ⟨h1, h2⟩), one_mul]
    · rw [if_neg h2, if_neg fun h => h2 (key.1 h).2, mul_zero]
  · rw [if_neg h1, if_neg fun h => h1 (key.1 h).1, zero_mul]

theorem dcosMul : DcosMul := by
  intro E _ _ _ w ϖ hϖ a b x x' y y' hx hx' hy hy'
  funext m
  have hK : (iwGL a w).prod (iwGL b w) ≤ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) :=
    Subgroup.prod_mono (iwGL_le w a) (iwGL_le w b)
  have hf : ∀ g ∈ (iwGL a w).prod (iwGL b w), ∃ p ∈ (iwGL a w).prod (iwGL b w),
      ∃ q ∈ (iwGL a w).prod (iwGL b w), g = p * q ∧
        (tdiag ϖ x, tdiag ϖ y) * p * (tdiag ϖ x, tdiag ϖ y)⁻¹ ∈ (iwGL a w).prod (iwGL b w) ∧
        (tdiag ϖ x', tdiag ϖ y')⁻¹ * q * (tdiag ϖ x', tdiag ϖ y') ∈ (iwGL a w).prod (iwGL b w) := by
    intro g hg
    obtain ⟨g1, g2⟩ := Subgroup.mem_prod.1 hg
    obtain ⟨p1, hp1, q1, hq1, e1, c1, d1⟩ := iw_fact hϖ hx hx' _ g1
    obtain ⟨p2, hp2, q2, hq2, e2, c2, d2⟩ := iw_fact hϖ hy hy' _ g2
    exact ⟨(p1, p2), Subgroup.mem_prod.2 ⟨hp1, hp2⟩, (q1, q2), Subgroup.mem_prod.2 ⟨hq1, hq2⟩, Prod.ext e1 e2,
      Subgroup.mem_prod.2 ⟨c1, c2⟩, Subgroup.mem_prod.2 ⟨d1, d2⟩⟩
  have hc : ∀ g ∈ (iwGL a w).prod (iwGL b w),
      ((tdiag ϖ x, tdiag ϖ y) * (tdiag ϖ x', tdiag ϖ y'))⁻¹ * g * ((tdiag ϖ x, tdiag ϖ y) * (tdiag ϖ x', tdiag ϖ y')) ∈
        (iwGL a w).prod (iwGL b w) →
      (tdiag ϖ x, tdiag ϖ y)⁻¹ * g * (tdiag ϖ x, tdiag ϖ y) ∈ (iwGL a w).prod (iwGL b w) := by
    intro g hg h
    obtain ⟨g1, g2⟩ := Subgroup.mem_prod.1 hg
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 h
    exact Subgroup.mem_prod.2 ⟨iw_chain hϖ hx hx' _ g1 h1, iw_chain hϖ hy hy' _ g2 h2⟩
  have main := hint_conv hK hf hc m
  have e : ((tdiag ϖ x, tdiag ϖ y) * (tdiag ϖ x', tdiag ϖ y') : GLw a w × GLw b w) =
      (tdiag ϖ (x + x'), tdiag ϖ (y + y')) := by
    rw [tdiag_add, tdiag_add]; rfl
  rw [e] at main
  show hint _ (fun m' : GLw a w × GLw b w => (dcos a w (tdiag ϖ x) m'.1 * dcos b w (tdiag ϖ y) m'.2) *
    (dcos a w (tdiag ϖ x') (m'⁻¹ * m).1 * dcos b w (tdiag ϖ y') (m'⁻¹ * m).2)) = _
  simp only [dcos_mul_eq]
  exact main

end Local

end GlobalTheory.CompanionTheory.DcosProduct

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplication
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupportDcos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeAlgebraStructure

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open GlobalTheory.CompanionTheory.DcosProduct (dc mem_dc_mul inv_mul_mem_of_dc tdiag_add conj_entry)
open PositivityTheory.Rg.BcN.F2 (hconv hk IsHk)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.IwHeckeMul

section Abstract

variable {G : Type} [Group G]

theorem fibre_coset {I : Subgroup G} {t t' : G}
    (hf : ∀ g ∈ I, ∃ a ∈ I, ∃ b ∈ I, g = a * b ∧ t * a * t⁻¹ ∈ I ∧ t'⁻¹ * b * t' ∈ I)
    (hc : ∀ g ∈ I, (t * t')⁻¹ * g * (t * t') ∈ I → t⁻¹ * g * t ∈ I)
    {i i' z : G} (hi : i ∈ I) (hi' : i' ∈ I) (h1 : z ∈ dc I t)
    (h2 : z⁻¹ * (i * (t * t') * i') ∈ dc I t') : (i * t)⁻¹ * z ∈ I := by
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

theorem conv_dc {I : Subgroup G} {t t' : G}
    (hf : ∀ g ∈ I, ∃ a ∈ I, ∃ b ∈ I, g = a * b ∧ t * a * t⁻¹ ∈ I ∧ t'⁻¹ * b * t' ∈ I)
    (hc : ∀ g ∈ I, (t * t')⁻¹ * g * (t * t') ∈ I → t⁻¹ * g * t ∈ I)
    {e e' e'' : G → ℂ} (he : ∀ y, (y ∈ dc I t → e y = 1) ∧ (y ∉ dc I t → e y = 0))
    (he' : ∀ y, (y ∈ dc I t' → e' y = 1) ∧ (y ∉ dc I t' → e' y = 0))
    (he'' : ∀ y, (y ∈ dc I (t * t') → e'' y = 1) ∧ (y ∉ dc I (t * t') → e'' y = 0)) (m : G) :
    ∑ᶠ q : G ⧸ I, e q.out * e' (q.out⁻¹ * m) = e'' m := by
  by_cases hm : m ∈ dc I (t * t')
  · rw [(he'' m).1 hm]
    obtain ⟨i, hi, i', hi', rfl⟩ := hm
    rw [finsum_eq_single _ (((i * t : G)) : G ⧸ I)]
    · have hz : (i * t)⁻¹ * (((i * t : G)) : G ⧸ I).out ∈ I :=
        QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm
      obtain ⟨z, hzd⟩ : ∃ z, z = (((i * t : G)) : G ⧸ I).out := ⟨_, rfl⟩
      rw [← hzd] at hz ⊢
      have h1 : z ∈ dc I t := ⟨i, hi, _, hz, by group⟩
      have h2 : z⁻¹ * (i * (t * t') * i') ∈ dc I t' :=
        ⟨((i * t)⁻¹ * z)⁻¹, inv_mem hz, i', hi', by group⟩
      rw [(he _).1 h1, (he' _).1 h2, one_mul]
    · intro q hq
      by_cases h1 : q.out ∈ dc I t
      · by_cases h2 : q.out⁻¹ * (i * (t * t') * i') ∈ dc I t'
        · exfalso
          apply hq
          rw [← QuotientGroup.out_eq' q]
          exact (QuotientGroup.eq.2 (fibre_coset hf hc hi hi' h1 h2)).symm
        · rw [(he' _).2 h2, mul_zero]
      · rw [(he _).2 h1, zero_mul]
  · rw [(he'' m).2 hm]
    refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
    by_cases h1 : q.out ∈ dc I t
    · by_cases h2 : q.out⁻¹ * m ∈ dc I t'
      · exact absurd (mem_dc_mul hf h1 h2) hm
      · rw [(he' _).2 h2, mul_zero]
    · rw [(he _).2 h1, zero_mul]

end Abstract

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem val_unif {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : ordL (ϖ : w.adicCompletion E) = 1) :
    ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) =
      ValuativeRel.uniformizer (w.adicCompletion E) := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have h1 : Valued.v (ϖ : w.adicCompletion E) < 1 :=
    GlobalTheory.CompanionTheory.IwahoriContraction.v_lt_one_of_ordL_eq_one w ϖ.ne_zero hϖ
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (ValuativeRel.uniformizer (w.adicCompletion E))
  apply le_antisymm
  · rw [ValuativeRel.le_uniformizer_iff]
    exact e.lt_one_iff_lt_one.2 h1
  · rw [← hy]
    have h2 : Valued.v y < 1 := e.lt_one_iff_lt_one.1 (hy ▸ ValuativeRel.uniformizer_lt_one)
    exact (e _ _).2 (GlobalTheory.CompanionTheory.IwahoriContraction.v_le_of_ordL_eq_one w ϖ.ne_zero hϖ h2)

theorem iw_fact {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : ordL (ϖ : w.adicCompletion E) = 1) {n : ℕ}
    {x x' : Fin n → ℤ} (hx : Antitone x) (hx' : Antitone x') :
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

theorem v_zpow_le_one {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : ordL (ϖ : w.adicCompletion E) = 1) {k : ℤ}
    (hk : 0 ≤ k) : Valued.v ((ϖ ^ k : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1 := by
  have h1 : Valued.v (ϖ : w.adicCompletion E) < 1 :=
    GlobalTheory.CompanionTheory.IwahoriContraction.v_lt_one_of_ordL_eq_one w ϖ.ne_zero hϖ
  have h0 : 0 < Valued.v (ϖ : w.adicCompletion E) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ϖ.ne_zero)
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact zpow_le_one₀ h0 h1.le hk

theorem int_entries {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : ordL (ϖ : w.adicCompletion E) = 1) {n : ℕ}
    {x x' : Fin n → ℤ} (hx : Antitone x) (hx' : Antitone x') {g : GLw n w}
    (h1 : ∀ i j, Valued.v (g.val i j) ≤ 1)
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

theorem iw_chain {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : ordL (ϖ : w.adicCompletion E) = 1) {n : ℕ}
    {x x' : Fin n → ℤ} (hx : Antitone x) (hx' : Antitone x') :
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

theorem dcos_mem (n : ℕ) (w : Pl E) (t y : GLw n w) :
    (y ∈ dc (iwGL n w) t → dcos n w t y = 1) ∧ (y ∉ dc (iwGL n w) t → dcos n w t y = 0) :=
  ⟨fun h => if_pos h, fun h => if_neg h⟩

theorem isHk_dcos (n : ℕ) (w : Pl E) (t : GLw n w) : IsHk (iwGL n w) (dcos n w t) := by
  refine ⟨GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin n),
    GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori (w.adicCompletion E) (Fin n),
    HasCompactSupport.of_support_subset_isCompact (GlobalTheory.CompanionTheory.IwFacts.isCompact_support_dcos w n t) fun g hg => hg,
    fun k₁ h₁ k₂ h₂ g => ?_⟩
  by_cases h : g ∈ dc (iwGL n w) t
  · have h' : k₁ * g * k₂ ∈ dc (iwGL n w) t := by
      obtain ⟨x, hx, z, hz, rfl⟩ := h
      exact ⟨k₁ * x, mul_mem h₁ hx, z * k₂, mul_mem hz h₂, by group⟩
    rw [(dcos_mem n w t _).1 h, (dcos_mem n w t _).1 h']
  · have h' : k₁ * g * k₂ ∉ dc (iwGL n w) t := by
      rintro ⟨x, hx, z, hz, e⟩
      refine h ⟨k₁⁻¹ * x, mul_mem (inv_mem h₁) hx, z * k₂⁻¹, mul_mem hz (inv_mem h₂), ?_⟩
      have : g = k₁⁻¹ * (k₁ * g * k₂) * k₂⁻¹ := by group
      rw [this, e]; group
    rw [(dcos_mem n w t _).2 h, (dcos_mem n w t _).2 h']

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (a : ℕ) (ϖ : (w.adicCompletion E)ˣ), ordL (ϖ : w.adicCompletion E) = 1 → ∀ (x x' : Fin a → ℤ), Antitone x → Antitone x' → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GLw a w) V) (v : V), (∀ k ∈ iwGL a w, π k v = v) → ∑ᶠ q : GLw a w ⧸ iwGL a w, dcos a w (tdiag ϖ (x + x')) q.out • π q.out v = ∑ᶠ q : GLw a w ⧸ iwGL a w, dcos a w (tdiag ϖ x) q.out • π q.out (∑ᶠ q' : GLw a w ⧸ iwGL a w, dcos a w (tdiag ϖ x') q'.out • π q'.out v) := by
  intro E _ _ _ w a ϖ hϖ x x' hx hx' V _ _ π v hv
  obtain ⟨-, -, h⟩ := GlobalTheory.CompanionTheory.HeckeAlg.hk_alg (w.adicCompletion E) (Fin a) (iwGL a w) (dcos a w (tdiag ϖ x))
    (dcos a w (tdiag ϖ x')) (isHk_dcos a w _) (isHk_dcos a w _)
  obtain ⟨-, hm, -⟩ := h V π v (by
    show ∀ k : iwGL a w, π (k : GLw a w) v = (((1 : iwGL a w →* ℂˣ) k : ℂˣ) : ℂ) • v
    intro k
    simpa using hv k k.2)
  have hc : hconv (iwGL a w) (dcos a w (tdiag ϖ x)) (dcos a w (tdiag ϖ x')) = dcos a w (tdiag ϖ (x + x')) := by
    funext g
    rw [tdiag_add]
    exact conv_dc (iw_fact hϖ hx hx') (iw_chain hϖ hx hx') (dcos_mem a w _) (dcos_mem a w _) (dcos_mem a w _) g
  rw [hc] at hm
  exact hm

end Local

end GlobalTheory.CompanionTheory.IwHeckeMul

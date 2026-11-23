import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeeps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.CloseLevi

variable {n : ℕ} {ε : Fin n → Bool}

theorem isClosed_stab {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) :
    IsClosed {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} := by
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) := GlobalTheory.FlagLeviGroup.continuous_uMat
  have h : {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} =
      ⋂ i, ⋂ y ∈ (W i : Set (Fin n → ℂ)),
        (fun g : Formalism.REAL.UJ ε => uMat g *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ)) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [h]
  refine isClosed_iInter fun i => isClosed_biInter fun y _ => ?_
  exact (W i).closed_of_finiteDimensional.preimage (hc.matrix_mulVec continuous_const)

theorem mem_flagM_of_keeps {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) {l : Formalism.REAL.UJ ε}
    (hl : l ∈ maxK ε) (h : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i) : l ∈ flagM ε W := by
  have hl' : (uMat l)ᴴ * uMat l = 1 := hl
  show ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i
  intro i y hy
  exact ⟨h i y hy, GlobalTheory.FlagLeviGroup.inv_keeps hl' (W i) (h i) y hy⟩

private theorem exists_unit_valuation_le_subset_nhds {G : Type} [Group G] [TopologicalSpace G] {f : G → ℝ}
    (hf : Continuous f) (h0 : ∀ g, 0 ≤ f g) (h1 : ∀ g, f g = 0 ↔ g = 1) (hB : IsCompact {g | f g ≤ 1})
    {O : Set G} (hO : IsOpen O) (h1O : (1 : G) ∈ O) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ g, f g < ρ → g ∈ O := by
  have hC : IsCompact ({g | f g ≤ 1} ∩ Oᶜ) := hB.inter_right hO.isClosed_compl
  rcases ({g | f g ≤ 1} ∩ Oᶜ).eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, fun g hg => ?_⟩
    by_contra hgO
    have hgC : g ∈ ({g | f g ≤ 1} ∩ Oᶜ) := ⟨le_of_lt hg, hgO⟩
    rw [hE] at hgC
    simpa using hgC
  · obtain ⟨c, ⟨_, hcO⟩, hmin⟩ := hC.exists_isMinOn hne hf.continuousOn
    have hc : 0 < f c := by
      rcases (h0 c).lt_or_eq with h | h
      · exact h
      · exfalso
        have hc1 : c = 1 := (h1 c).1 h.symm
        rw [hc1] at hcO
        exact absurd h1O hcO
    refine ⟨min 1 (f c), lt_min one_pos hc, fun g hg => ?_⟩
    by_contra hgO
    have hgC : g ∈ ({g | f g ≤ 1} ∩ Oᶜ) := ⟨(lt_of_lt_of_le hg (min_le_left _ _)).le, hgO⟩
    have hcg : f c ≤ f g := isMinOn_iff.1 hmin g hgC
    exact absurd (lt_of_lt_of_le hg (min_le_right _ _)) (not_lt.2 hcg)

theorem close_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {f : G → ℝ}
    (hf : Continuous f) (h0 : ∀ g, 0 ≤ f g) (h1 : ∀ g, f g = 0 ↔ g = 1) (hB : IsCompact {g | f g ≤ 1})
    {K P L : Set G} (hK : IsCompact K) (hP : IsClosed P) (hL : ∀ k ∈ K, k⁻¹ ∈ P → k⁻¹ ∈ L) {t : ℝ} (ht : 0 < t) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ P, ∀ k ∈ K, f (p * k) ≤ r → ∃ l ∈ L, f (l * k) < t := by

  have hloc : ∀ k ∈ K, ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k),
      ∀ p ∈ P, f (p * z.2) ≤ z.1 → ∃ l ∈ L, f (l * z.2) < t := by
    intro k hk
    by_cases hkP : k⁻¹ ∈ P
    ·
      have hkL := hL k hk hkP
      have hc : Continuous fun x : G => f (k⁻¹ * x) := hf.comp (continuous_const.mul continuous_id)
      have hopen : IsOpen {x : G | f (k⁻¹ * x) < t} := isOpen_lt hc continuous_const
      have hmem : k ∈ {x : G | f (k⁻¹ * x) < t} := by
        show f (k⁻¹ * k) < t
        rw [inv_mul_cancel, (h1 1).2 rfl]
        exact ht
      have hev : ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k), z.2 ∈ {x : G | f (k⁻¹ * x) < t} :=
        (continuous_snd.tendsto ((0 : ℝ), k)).eventually_mem (hopen.mem_nhds hmem)
      filter_upwards [hev] with z hz
      intro p _ _
      exact ⟨k⁻¹, hkL, hz⟩
    ·
      have hcont : Continuous (fun q : G × G => q.1 * q.2⁻¹) := continuous_fst.mul continuous_snd.inv
      have hopen : IsOpen ((fun q : G × G => q.1 * q.2⁻¹) ⁻¹' Pᶜ) := hP.isOpen_compl.preimage hcont
      have hmem : ((1 : G), k) ∈ (fun q : G × G => q.1 * q.2⁻¹) ⁻¹' Pᶜ := by
        show (1 : G) * k⁻¹ ∈ Pᶜ
        rw [one_mul]
        exact hkP
      obtain ⟨O, V, hO, hV, h1O, hkV, hOV⟩ := isOpen_prod_iff.1 hopen 1 k hmem
      obtain ⟨ρ, hρ, hρO⟩ := exists_unit_valuation_le_subset_nhds hf h0 h1 hB hO h1O
      have e1 : ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k), z.1 < ρ :=
        (continuous_fst.tendsto ((0 : ℝ), k)).eventually (gt_mem_nhds hρ)
      have e2 : ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k), z.2 ∈ V :=
        (continuous_snd.tendsto ((0 : ℝ), k)).eventually_mem (hV.mem_nhds hkV)
      filter_upwards [e1, e2] with z hz1 hz2
      intro p hp hpz
      exfalso
      have hO' : p * z.2 ∈ O := hρO _ (lt_of_le_of_lt hpz hz1)
      have hmem' := hOV (Set.mk_mem_prod hO' hz2)
      simp only [Set.mem_preimage, mul_inv_cancel_right, Set.mem_compl_iff] at hmem'
      exact hmem' hp
  have hev := hK.eventually_forall_of_forall_eventually (x₀ := (0 : ℝ))
    (P := fun r x => ∀ p ∈ P, f (p * x) ≤ r → ∃ l ∈ L, f (l * x) < t) hloc
  have hpos : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < r := eventually_mem_nhdsWithin
  obtain ⟨r, hr, hrK⟩ := (hpos.and (hev.filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨r, hr, fun p hp k hk hpk => hrK k hk p hp hpk⟩

theorem nrm_uMat_eq_zero (g : Formalism.REAL.UJ ε) : nrm (uMat g - 1) = 0 ↔ g = 1 := by
  rw [nrm_eq_zero, sub_eq_zero]
  constructor
  · intro h
    apply Subtype.ext
    exact Units.ext h
  · rintro rfl
    exact GlobalTheory.FlagLeviGroup.uMat_one

theorem close_levi : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ t : ℝ, 0 < t → ∃ r : ℝ, 0 < r ∧
    ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, nrm (uMat (u * m * k) - 1) ≤ r →
      ∃ l ∈ maxK ε ∩ flagM ε W, nrm (uMat (l * k) - 1) < t := by
  intro n ε a j W hW t ht

  have hL : ∀ k ∈ maxK ε, k⁻¹ ∈ {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} →
      k⁻¹ ∈ maxK ε ∩ flagM ε W := by
    intro k hk hkP
    have hk' : k⁻¹ ∈ maxK ε := (GlobalTheory.FlagLeviGroup.compactSub ε).inv_mem hk
    exact Set.mem_inter hk' (mem_flagM_of_keeps W hk' hkP)
  obtain ⟨r, hr, hrP⟩ := close_of_compact (G := Formalism.REAL.UJ ε) (f := fun g => nrm (uMat g - 1))
    (continuous_nrm_uMat ε) (fun g => nrm_nonneg _) (fun g => nrm_uMat_eq_zero g) (isCompact_hsBall ε 1)
    (isCompact_maxK ε) (isClosed_stab W) hL ht
  refine ⟨r, hr, fun u hu m hm k hk hle => ?_⟩
  have hm' : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i := hm
  have hum : u * m ∈ {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} := by
    rw [Set.mem_setOf_eq]
    intro i y hy
    rw [GlobalTheory.FlagLeviGroup.uMat_mul, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.FlagMeas.UnipRad.keeps hW u hu i _ (hm' i y hy).1
  exact hrP (u * m) hum k hk hle

end GlobalTheory.IwConst.CloseLevi

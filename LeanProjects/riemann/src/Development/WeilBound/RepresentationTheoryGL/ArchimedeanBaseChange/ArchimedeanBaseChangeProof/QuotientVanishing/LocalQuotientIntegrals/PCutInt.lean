import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableSdot

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.CV.AdelicTopology

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem twConj_mul_eq {G : Type} [Group G] (θ : Monoid.End G) (a b δ : G) :
    twConj θ (a * b) δ = twConj θ b (twConj θ a δ) := by
  simp only [twConj, map_mul]
  group

theorem twConj_ratGL (g d : GL (Fin n) E) :
    twConj (thetaA E n) (ratGL E n g) (ratGL E n d) = ratGL E n (twConj (thetaE E n) g d) := by
  simp only [twConj, GlobalTheory.CompanionTheory.RatDisc.thetaA_ratGL, map_mul, map_inv]

theorem chiT_ratGL_mul (hM : Mahler) (τ : ℝ) (c : GL (Fin n) E) (x : GA E n) :
    chiT τ (ratGL E n c * x) = chiT τ x := by
  have h := ((hM E n τ).2.1 c x)
  by_cases hx : x ∈ cutSet E n τ
  · unfold chiT
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem (h.2 hx)]
    rfl
  · unfold chiT
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt h.1 hx)]

theorem norm_chiT_le (τ : ℝ) (x : GA E n) : ‖chiT τ x‖ ≤ 1 := by
  unfold chiT
  by_cases hx : x ∈ cutSet E n τ
  · rw [Set.indicator_of_mem hx]; simp
  · rw [Set.indicator_of_notMem hx]; simp

end PositivityTheory.Rg.BcB.CV.AdelicTopology

open PositivityTheory.Rg.BcB.CV.AdelicTopology in
theorem PositivityTheory.Rg.BcB.CV.pf_CutInt : PositivityTheory.Rg.BcB.D4.KerFin → PositivityTheory.Rg.BcB.Mahler → PositivityTheory.Rg.BcB.CV.QInt → PositivityTheory.Rg.BcB.CV.AdTop → PositivityTheory.Rg.BcB.CV.CutInt := by
  classical
  intro hK hM hQ hA E _ _ _ n _ _ μ _ τ φ d hφ
  obtain ⟨hLC, hT2, hSC, hθ, -, hrat⟩ := hA E n
  obtain ⟨hcl, hinv, C, hC, hsub⟩ := hM E n τ
  obtain ⟨hRc, hRd, -⟩ := hrat d
  have hcont : Continuous fun x : GA E n => twConj (thetaA E n) x (ratGL E n d) := by
    unfold twConj
    exact (continuous_inv.mul continuous_const).mul hθ
  have hmeas : Measurable fun x => chiT τ x * φ (twConj (thetaA E n) x (ratGL E n d)) := by
    refine Measurable.mul ?_ (hφ.cont.comp hcont).measurable
    exact (measurable_one.indicator hcl.measurableSet : Measurable ((cutSet E n τ).indicator (1 : GA E n → ℂ)))
  have hinvF : ∀ g ∈ ratCent d, ∀ x, chiT τ (g * x) * φ (twConj (thetaA E n) (g * x) (ratGL E n d)) =
      chiT τ x * φ (twConj (thetaA E n) x (ratGL E n d)) := by
    rintro _ ⟨c, hc, rfl⟩ x
    rw [chiT_ratGL_mul hM τ c x,
      twConj_mul_left _ _ (GlobalTheory.CompanionTheory.RatDisc.ratCent_le d ⟨c, hc, rfl⟩) x]
  refine ⟨hmeas, hinvF, ?_⟩

  set S := {d' : GL (Fin n) E | ∃ x ∈ C, φ (twConj (thetaA E n) x (ratGL E n d')) ≠ 0} with hSdef
  have hS : S.Finite := hK E n φ hφ C hC
  let pick : GL (Fin n) E → GL (Fin n) E := fun d' =>
    if h : ∃ g, twConj (thetaE E n) g d = d' then h.choose else 1
  set C' : Set (GA E n) := ⋃ d' ∈ S, (fun c => ratGL E n (pick d') * c) '' C with hC'def
  have hC' : IsCompact C' :=
    hS.isCompact_biUnion fun d' _ => hC.image (continuous_const.mul continuous_id)
  have hsupp : ∀ x, chiT τ x * φ (twConj (thetaA E n) x (ratGL E n d)) ≠ 0 → x ∈ (ratCent d : Set (GA E n)) * C' := by
    intro x hx
    have hxc : x ∈ cutSet E n τ := by
      by_contra h
      apply hx
      simp only [chiT, Set.indicator_of_notMem h, zero_mul]
    have hφx : φ (twConj (thetaA E n) x (ratGL E n d)) ≠ 0 := fun h => hx (by rw [h, mul_zero])
    obtain ⟨γ, ⟨g, rfl⟩, c, hcC, hγc⟩ := hsub hxc
    subst hγc
    have hd' : twConj (thetaE E n) g d ∈ S := by
      refine ⟨c, hcC, ?_⟩
      rwa [twConj_mul_eq, twConj_ratGL] at hφx
    have hex : ∃ g', twConj (thetaE E n) g' d = twConj (thetaE E n) g d := ⟨g, rfl⟩
    have hpick : pick (twConj (thetaE E n) g d) = hex.choose := dif_pos hex
    set g₀ := hex.choose with hg₀
    have hg₀d : twConj (thetaE E n) g₀ d = twConj (thetaE E n) g d := hex.choose_spec
    have hcent : g * g₀⁻¹ ∈ twCent (thetaE E n) d := by
      change twConj (thetaE E n) (g * g₀⁻¹) d = d
      rw [twConj_mul_eq, ← hg₀d, ← twConj_mul_eq, mul_inv_cancel]
      simp [twConj]
    refine ⟨ratGL E n (g * g₀⁻¹), ⟨g * g₀⁻¹, hcent, rfl⟩, ratGL E n g₀ * c, ?_, ?_⟩
    · refine Set.mem_biUnion hd' ⟨c, hcC, ?_⟩
      simp only [hpick]
    · rw [map_mul, map_inv]
      group
  obtain ⟨B, hB⟩ := hφ.cont.bounded_above_of_compact_support hφ.supp
  have hbound : ∀ x ∈ C', ‖chiT τ x * φ (twConj (thetaA E n) x (ratGL E n d))‖ ≤ max B 0 := by
    intro x _
    rw [norm_mul]
    calc ‖chiT τ x‖ * ‖φ (twConj (thetaA E n) x (ratGL E n d))‖
        ≤ 1 * ‖φ (twConj (thetaA E n) x (ratGL E n d))‖ :=
          mul_le_mul_of_nonneg_right (norm_chiT_le τ x) (norm_nonneg _)
      _ ≤ max B 0 := by rw [one_mul]; exact (hB _).trans (le_max_left _ _)
  have := hLC
  have := hT2
  have := hSC
  have := hRd
  have : IsFiniteMeasureOnCompacts (Measure.count : Measure (ratCent d)) :=
    ⟨fun K hK => Measure.count_apply_lt_top.2 hK.finite_of_discrete⟩
  have : (Measure.count : Measure (ratCent d)).IsOpenPosMeasure :=
    ⟨fun U _ hne h => hne.ne_empty (Measure.count_eq_zero_iff.1 h)⟩
  have : (Measure.count : Measure (ratCent d)).IsHaarMeasure := {}
  obtain ⟨A, -, hQA⟩ := hQ (GA E n) μ (ratCent d) Measure.count C' hRc hC'
  exact (hQA _ (max B 0) (le_max_right _ _) hmeas hinvF hsupp hbound).1

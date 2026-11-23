import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceE
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceF

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

open SliceClasses in

theorem slice_of : Dict → FinTr → Slice := by
  intro hD hFin E _ _ _ r s hr hs V hV c hc
  obtain ⟨φ₀, hφ₀V, F₀, hCT, F, hFspan, hFne, hFeig⟩ := hc
  have hA₀ := hV.aut φ₀ hφ₀V
  obtain ⟨κ, -, rfl⟩ := ((hD E (r + s)).2.2.2 φ₀ hA₀ r hr (by omega)).2 F₀ hCT
  obtain ⟨cs, hcs⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hFspan
  obtain ⟨a, ha⟩ : ∃ a : ℝ → ℂ, a = fun t => cs t * κ := ⟨_, rfl⟩
  have hFval : ∀ g, F g = ∑ t ∈ cs.support, a t * An.ctn r φ₀.1 (aT E (r + s) r t * g) := by
    intro g
    rw [← hcs, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, ha, mul_assoc]
  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring V hV.aut r cs.support a
  have hTval : ∀ φ ∈ V, ∀ g, (T φ).1 g = ∑ t ∈ cs.support, a t * An.ctn r φ.1 (aT E (r + s) r t * g) := by
    intro φ hφ g
    rw [hT φ hφ, Aop_apply, ctSm_val r (hV.aut φ hφ)]
  have hequiv : ∀ o, ∀ φ ∈ V, T (act o φ) = act o (T φ) := by
    intro o φ hφ
    rw [hT _ (hV.stable o φ hφ), hT φ hφ, ctSm_act r (hV.aut φ hφ) o (hV.aut _ (hV.stable o φ hφ)), Aop_act]
  have hT₀ : (T φ₀).1 = F := funext fun g => (hTval φ₀ hφ₀V g).trans (hFval g).symm

  let W : Submodule ℂ (Sm E (r + s)) :=
    { carrier := {φ | φ ∈ V ∧ ∀ (t : ℝ) g, (T φ).1 (aT E (r + s) r t * g) = Complex.exp (c * t) * (T φ).1 g}
      add_mem' := fun {φ ψ} hφ hψ => ⟨V.add_mem hφ.1 hψ.1, fun t g => by
        simp only [map_add, Submodule.coe_add, Pi.add_apply, hφ.2 t g, hψ.2 t g, mul_add]⟩
      zero_mem' := ⟨V.zero_mem, fun t g => by simp⟩
      smul_mem' := fun b φ hφ => ⟨V.smul_mem b hφ.1, fun t g => by
        simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hφ.2 t g]
        ring⟩ }
  have hWst : IsStable W := by
    rintro o φ ⟨hφ, he⟩
    refine ⟨hV.stable o φ hφ, fun t g => ?_⟩
    have e1 : ltS (aT E (r + s) r t) (T φ) = Complex.exp (c * t) • T φ := Subtype.ext (funext fun g => he t g)
    have e2 := congrArg (fun G : Sm E (r + s) => G.1 g) (congrArg (act o) e1)
    simp only [← ltS_act, map_smul] at e2
    rw [hequiv o φ hφ]
    exact e2
  have hWV : W = V := by
    rcases hV.irred W (fun φ hφ => hφ.1) hWst with h | h
    · exfalso
      have h0 : φ₀ ∈ W := ⟨hφ₀V, fun t g => by rw [hT₀]; exact hFeig t g⟩
      rw [h, Submodule.mem_bot] at h0
      apply hFne
      rw [← hT₀, h0, map_zero]
      rfl
    · exact h
  have heig : ∀ φ ∈ V, ∀ (t : ℝ) g, (T φ).1 (aT E (r + s) r t * g) = Complex.exp (c * t) * (T φ).1 g := by
    intro φ hφ
    rw [← hWV] at hφ
    exact hφ.2
  have hsplit : ∀ φ ∈ V, ∀ (t : ℝ) g, (T φ).1 (splitCentre E (r + s) t * g) = (T φ).1 g := by
    intro φ hφ t g
    rw [hTval φ hφ, hTval φ hφ]
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 1
    rw [← mul_assoc, ← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t (aT E (r + s) r u), mul_assoc,
      ctn_splitCentre (hV.sqInt φ hφ).1]
  refine ⟨T, ⟨hequiv, ⟨φ₀, hφ₀V, fun h => hFne ?_⟩, ?_, ?_, ?_⟩⟩
  · rw [← hT₀, h]
    rfl
  · intro φ hφ x g
    rw [hTval φ hφ, hTval φ hφ]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨y, hy⟩ := aT_mul_unip (r + s) r t x
    congr 1
    rw [← mul_assoc, hy, mul_assoc, ctn_unip (hV.aut φ hφ)]
  · intro φ hφ k g m₂
    obtain ⟨ψ, hψA, hψ⟩ := (F_slices V hV T hequiv cs.support a hTval φ hφ k g).1 m₂
    refine ⟨ψ, hψA, hψ, fun t m₁ => ?_, fun r₁ h1 h2 c₁ hc₁ =>
      ⟨φ, hφ, exp_left hD hFin hr hs φ (hV.aut φ hφ) cs.support a (T φ).1 (hTval φ hφ) ψ hψA m₂ _ hψ r₁ h1 h2 c₁ hc₁⟩⟩
    have e : lev (Ad E) r s (splitCentre E r t * m₁, m₂) = aT E (r + s) r t * lev (Ad E) r s (m₁, m₂) := by
      rw [show ((splitCentre E r t * m₁, m₂) : GA E r × GA E s) = (splitCentre E r t, 1) * (m₁, m₂) by simp,
        map_mul, splitCentre_eq_aT, lev_aT_left r s r le_rfl]
    rw [hψ, hψ, e, mul_assoc, heig φ hφ]
  · intro φ hφ k g m₁
    obtain ⟨ψ, hψA, hψ⟩ := (F_slices V hV T hequiv cs.support a hTval φ hφ k g).2 m₁
    refine ⟨ψ, hψA, hψ, fun t m₂ => ?_, fun r₂ h1 h2 c₂ hc₂ =>
      ⟨φ, hφ, exp_right hD hFin hr hs φ (hV.aut φ hφ) cs.support a (T φ).1 (hTval φ hφ) c (heig φ hφ) ψ hψA m₁ _ hψ
        r₂ h1 h2 c₂ hc₂⟩⟩
    have e : lev (Ad E) r s (m₁, splitCentre E s t * m₂) =
        splitCentre E (r + s) t * (aT E (r + s) r (-t) * lev (Ad E) r s (m₁, m₂)) := by
      rw [show ((m₁, splitCentre E s t * m₂) : GA E r × GA E s) = (1, splitCentre E s t) * (m₁, m₂) by simp,
        map_mul, splitCentre_eq_aT, lev_aT_right r s s le_rfl, splitCentre_eq_aT, mul_assoc]
    rw [hψ, hψ, e, mul_assoc, hsplit φ hφ, mul_assoc, heig φ hφ]
    congr 2
    push_cast
    ring

end PositivityTheory.Rg.Rs

end

import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PNoLogSt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PSliceUA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.ExpChar
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSlice
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUniqueness

open LieSumUnipotentSlice PositivityTheory.Rg.Rs.SliceClasses in

theorem sliceU_of_noLog2 (hNL : NoLog) : SliceU := by
  intro E _ _ _ r s hr hs U hU hFG hSI hReg φ hφU c hc
  have hD := dict_holds
  have hFin := finTr_holds
  obtain ⟨F₀, hCT, F, hFspan, hFne, hFeig⟩ := hc
  have hAφ := hU.2 φ hφU
  obtain ⟨κ, -, rfl⟩ := ((hD E (r + s)).2.2.2 φ hAφ r hr (by omega)).2 F₀ hCT
  obtain ⟨cs, hcs⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hFspan
  obtain ⟨b, hb⟩ : ∃ b : ℝ → ℂ, b = fun t => cs t * κ := ⟨_, rfl⟩
  have hFval : ∀ g, F g = ∑ t ∈ cs.support, b t * An.ctn r φ.1 (aT E (r + s) r t * g) := by
    intro g
    rw [← hcs, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, hb, mul_assoc]

  obtain ⟨S, hSU, hSgen⟩ := hFG
  have hregψ : ∀ ψ ∈ U, ∀ τ : E →+* ℂ, ∃ m, HasInfCharGL (Submodule.span ℂ {ψ}) τ m ∧ m.Nodup := by
    intro ψ hψ τ
    obtain ⟨m, ⟨hcard, hm⟩, hnd⟩ := hReg τ
    exact ⟨m, ⟨hcard, fun u χ hχ => hm u χ ((Submodule.span_singleton_le_iff_mem ψ U).2 hψ hχ)⟩, hnd⟩
  have hdec : ∀ ψ ∈ S, ∃ (C : Finset ℂ) (G : ℂ → GA E (r + s) → ℂ), An.ctn r ψ.1 = ∑ c ∈ C, G c ∧
      ∀ c ∈ C, ∀ (t : ℝ) g, G c (aT E (r + s) r t * g) = Complex.exp (c * t) * G c g := fun ψ hψ =>
    hNL E (r + s) r ψ (hU.2 ψ (hSU hψ)) (hSI ψ (hSU hψ)) (hregψ ψ (hSU hψ)) hr (by omega)
  choose! Cs Gs hsum hGeig using hdec
  obtain ⟨τs, a, ha⟩ := SliceUB2.lagrange (insert c (S.biUnion Cs)) c
  have ha1 : ∑ t ∈ τs, a t * Complex.exp (c * t) = 1 := by
    rw [ha c (Finset.mem_insert_self _ _), if_pos rfl]

  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring U hU.2 r τs a
  have hTval : ∀ ψ ∈ U, ∀ g, (T ψ).1 g = ∑ t ∈ τs, a t * An.ctn r ψ.1 (aT E (r + s) r t * g) := by
    intro ψ hψ g
    rw [hT ψ hψ, Aop_apply, ctSm_val r (hU.2 ψ hψ)]
  have hequiv : ∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ) := by
    intro o ψ hψ
    rw [hT _ (hU.1 o ψ hψ), hT ψ hψ, ctSm_act r (hU.2 ψ hψ) o (hU.2 _ (hU.1 o ψ hψ)), Aop_act]

  have hgen : ∀ ψ ∈ S, ∀ g, (T ψ).1 g = ∑ c' ∈ Cs ψ, (if c' = c then 1 else 0) * Gs ψ c' g := by
    intro ψ hψ g
    rw [hTval ψ (hSU hψ), hsum ψ hψ]
    calc ∑ t ∈ τs, a t * (∑ c' ∈ Cs ψ, Gs ψ c') (aT E (r + s) r t * g)
        = ∑ t ∈ τs, ∑ c' ∈ Cs ψ, a t * (Complex.exp (c' * t) * Gs ψ c' g) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl fun c' hc' => by rw [hGeig ψ hψ c' hc']
      _ = ∑ c' ∈ Cs ψ, (∑ t ∈ τs, a t * Complex.exp (c' * t)) * Gs ψ c' g := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c' _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun t _ => by ring
      _ = ∑ c' ∈ Cs ψ, (if c' = c then 1 else 0) * Gs ψ c' g := by
          refine Finset.sum_congr rfl fun c' hc' => ?_
          rw [ha c' (Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨ψ, hψ, hc'⟩))]

  let W : Submodule ℂ (Sm E (r + s)) :=
    { carrier := {ψ | ψ ∈ U ∧ ∀ (t : ℝ) g, (T ψ).1 (aT E (r + s) r t * g) = Complex.exp (c * t) * (T ψ).1 g}
      add_mem' := fun {φ ψ} hφ hψ => ⟨U.add_mem hφ.1 hψ.1, fun t g => by
        simp only [map_add, Submodule.coe_add, Pi.add_apply, hφ.2 t g, hψ.2 t g, mul_add]⟩
      zero_mem' := ⟨U.zero_mem, fun t g => by simp⟩
      smul_mem' := fun b φ hφ => ⟨U.smul_mem b hφ.1, fun t g => by
        simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hφ.2 t g]
        ring⟩ }
  have hWst : IsStable W := by
    rintro o ψ ⟨hψ, he⟩
    refine ⟨hU.1 o ψ hψ, fun t g => ?_⟩
    have e1 : ltS (aT E (r + s) r t) (T ψ) = Complex.exp (c * t) • T ψ := Subtype.ext (funext fun g => he t g)
    have e2 := congrArg (fun G : Sm E (r + s) => G.1 g) (congrArg (act o) e1)
    simp only [← ltS_act, map_smul] at e2
    rw [hequiv o ψ hψ]
    exact e2
  have hSW : (↑S : Set (Sm E (r + s))) ⊆ W := by
    intro ψ hψ
    refine ⟨hSU hψ, fun t g => ?_⟩
    rw [hgen ψ hψ, hgen ψ hψ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' hc' => ?_
    rw [hGeig ψ hψ c' hc']
    split_ifs with h
    · subst h
      ring
    · simp
  have hUW : U ≤ W := hSgen W hWst hSW
  have heig : ∀ ψ ∈ U, ∀ (t : ℝ) g, (T ψ).1 (aT E (r + s) r t * g) = Complex.exp (c * t) * (T ψ).1 g :=
    fun ψ hψ => (hUW hψ).2

  have hTφ : T φ ≠ 0 := by
    intro h0
    have hz : ∀ g, ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g) = 0 := by
      intro g
      rw [← hTval φ hφU g, h0]
      rfl
    apply hFne
    funext g
    have hcomm : ∀ t t' : ℝ, aT E (r + s) r t' * (aT E (r + s) r t * g) =
        aT E (r + s) r t * (aT E (r + s) r t' * g) := by
      intro t t'
      rw [← mul_assoc, ← mul_assoc, ← aT_add, ← aT_add, add_comm t' t]
    calc F g = (∑ t' ∈ τs, a t' * Complex.exp (c * t')) * F g := by rw [ha1, one_mul]
      _ = ∑ t' ∈ τs, a t' * F (aT E (r + s) r t' * g) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun t' _ => by rw [hFeig t' g]; ring
      _ = ∑ t ∈ cs.support, b t * ∑ t' ∈ τs, a t' * An.ctn r φ.1 (aT E (r + s) r t' * (aT E (r + s) r t * g)) := by
          simp_rw [hFval, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
          rw [hcomm]
          ring
      _ = 0 := by simp [hz]
  have hsplit : ∀ ψ ∈ U, ∀ (t : ℝ) g, (T ψ).1 (splitCentre E (r + s) t * g) = (T ψ).1 g := by
    intro ψ hψ t g
    rw [hTval ψ hψ, hTval ψ hψ]
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 1
    rw [← mul_assoc, ← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t (aT E (r + s) r u), mul_assoc,
      ctn_splitCentre (hSI ψ hψ)]
  have hsc : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ z : ℂ, ∀ ψ ∈ U, cap τ u ψ = z • ψ := by
    intro τ u
    obtain ⟨m, ⟨-, hm⟩, -⟩ := hReg τ
    exact ⟨_, hm u⟩
  refine ⟨T, ⟨hequiv, ⟨φ, hφU, hTφ⟩, ?_, ?_, ?_⟩, hTφ⟩
  · intro ψ hψ x g
    rw [hTval ψ hψ, hTval ψ hψ]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨y, hy⟩ := aT_mul_unip (r + s) r t x
    congr 1
    rw [← mul_assoc, hy, mul_assoc, ctn_unip (hU.2 ψ hψ)]
  · intro ψ hψ k g m₂
    obtain ⟨χ, hχA, hχ⟩ := (F_slicesU U hU.1 hU.2 hsc T hequiv τs a hTval ψ hψ k g).1 m₂
    refine ⟨χ, hχA, hχ, fun t m₁ => ?_, fun r₁ h1 h2 c₁ hc₁ =>
      ⟨ψ, hψ, exp_left hD hFin hr hs ψ (hU.2 ψ hψ) τs a (T ψ).1 (hTval ψ hψ) χ hχA m₂ _ hχ r₁ h1 h2 c₁ hc₁⟩⟩
    have e : lev (Ad E) r s (splitCentre E r t * m₁, m₂) = aT E (r + s) r t * lev (Ad E) r s (m₁, m₂) := by
      rw [show ((splitCentre E r t * m₁, m₂) : GA E r × GA E s) = (splitCentre E r t, 1) * (m₁, m₂) by simp,
        map_mul, splitCentre_eq_aT, lev_aT_left r s r le_rfl]
    rw [hχ, hχ, e, mul_assoc, heig ψ hψ]
  · intro ψ hψ k g m₁
    obtain ⟨χ, hχA, hχ⟩ := (F_slicesU U hU.1 hU.2 hsc T hequiv τs a hTval ψ hψ k g).2 m₁
    refine ⟨χ, hχA, hχ, fun t m₂ => ?_, fun r₂ h1 h2 c₂ hc₂ =>
      ⟨ψ, hψ, exp_right hD hFin hr hs ψ (hU.2 ψ hψ) τs a (T ψ).1 (hTval ψ hψ) c (heig ψ hψ) χ hχA m₁ _ hχ
        r₂ h1 h2 c₂ hc₂⟩⟩
    have e : lev (Ad E) r s (m₁, splitCentre E s t * m₂) =
        splitCentre E (r + s) t * (aT E (r + s) r (-t) * lev (Ad E) r s (m₁, m₂)) := by
      rw [show ((m₁, splitCentre E s t * m₂) : GA E r × GA E s) = (1, splitCentre E s t) * (m₁, m₂) by simp,
        map_mul, splitCentre_eq_aT, lev_aT_right r s s le_rfl, splitCentre_eq_aT, mul_assoc]
    rw [hχ, hχ, e, mul_assoc, hsplit ψ hψ, mul_assoc, heig ψ hψ]
    congr 2
    push_cast
    ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUniqueness

end

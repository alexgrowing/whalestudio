import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PTypesW
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PTypesK

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem typeB_lt {n : ℕ} {K' : Subgroup (GL (Fin n) (Af E))} {W' : Submodule ℂ (Kinf E n → ℂ)} {f : Sm E n}
    (h : SpectralAccumulation.TypeB K' W' f) (g : GA E n) :
    (fun κ : Kinf E n => f.1 (g * infGL E n (Unitary.toUnits κ))) ∈ lt W' := by
  rw [mem_lt]
  intro k₀
  have := h.2 (g * infGL E n (Unitary.toUnits k₀))
  simpa only [map_mul, mul_assoc] using this

open ParabolicProjection in
theorem main_ind {N : ℕ} (K : Subgroup (GL (Fin N) (Af E))) (hK : IsOpen (K : Set (GL (Fin N) (Af E))))
    (W : Submodule ℂ (Kinf E N → ℂ)) {n : ℕ} (t : SpectralAccumulation.Tr E n) : n ≤ N → ∀ f ∈ t.space, f ≠ 0 →
      SpectralAccumulation.TypeB (Kf N K n) (Wf N W n) f →
      t.AllLeaves (fun M V => ∃ K' ∈ ({Kf N K M} : Set (Subgroup (GL (Fin M) (Af E)))),
        ∃ W' ∈ ({Wf N W M} : Set (Submodule ℂ (Kinf E M → ℂ))), SpectralAccumulation.HasType K' W' V) := by
  induction t with
  | leaf V z =>
    intro _ f hf hf0 hT
    obtain ⟨χ, hχ, hχ0, hχT⟩ := untw hf hf0 hT (Kf_le_det _)
    exact ⟨_, rfl, _, rfl, χ, hχ, hχ0, hχT⟩
  | @node r s t₁ t₂ ih₁ ih₂ =>
    intro hN f hf hf0 hT
    rw [SpectralAccumulation.Tr.space] at hf
    have hI : MemInd2 (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) f := memInd2_of_span (Submodule.span_mono (fun φ h => h.1) hf)
    obtain ⟨g₀, hg₀⟩ : ∃ g₀, f.1 g₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hf0 (Subtype.ext (funext hc))
    have hopen := isOpen_Kf hK (r + s)
    obtain ⟨x, m, t, k, l, ht, hl, hg⟩ := Tset_spec hopen g₀
    have e₀ : g₀ = unip x * (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t)) *
        finGL E (r + s) l := by
      rw [hg, infGL_comm]
      simp only [mul_assoc]
    have hfm : f.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t)) ≠ 0 := by
      rw [e₀, hT.1 l hl, hI.1] at hg₀
      exact hg₀
    obtain ⟨n', ψ₁, ψ₂, h₁, h₂, hsum⟩ := tensor_pair_finite_sum (hI.2 k t)
    have hne : ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 ≠ 0 := (hsum m) ▸ hfm

    have hχ₁' : ∑ i, (ψ₂ i).1 m.2 • ψ₁ i ∈ tw t₁.space ((s : ℂ) / 2) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₁ i)
    have hχ₁'0 : ∑ i, (ψ₂ i).1 m.2 • ψ₁ i ≠ 0 := sum_left_ne hne
    have hval₁ : ∀ x₁, (∑ i, (ψ₂ i).1 m.2 • ψ₁ i).1 x₁ =
        f.1 (lev (Ad E) r s (x₁, m.2) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t)) := by
      intro x₁
      have e := hsum (x₁, m.2)
      rw [e]
      simp [Finset.sum_apply, mul_comm]
    have hT₁ : SpectralAccumulation.TypeB (Kf N K r) (Wf N W r) (∑ i, (ψ₂ i).1 m.2 • ψ₁ i) := by
      refine ⟨fun u hu x₁ => ?_, fun x₁ => ?_⟩
      · rw [hval₁, hval₁]
        have h1 : lev (Ad E) r s (x₁ * finGL E r u, m.2) =
            lev (Ad E) r s (x₁, m.2) * finGL E (r + s) (lev (Af E) r s (u, 1)) := by
          rw [← Slice1.lev_finGL, map_one, ← map_mul, Prod.mk_mul_mk, mul_one]
        have hc := infGL_comm (Unitary.toUnits k) (lev (Af E) r s (u, 1))
        have e : lev (Ad E) r s (x₁ * finGL E r u, m.2) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) =
            lev (Ad E) r s (x₁, m.2) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) *
              finGL E (r + s) (t⁻¹ * lev (Af E) r s (u, 1) * t) := by
          rw [h1, map_mul, map_mul, map_inv]
          simp only [mul_assoc]
          rw [← mul_assoc (finGL E (r + s) (lev (Af E) r s (u, 1))), ← hc]
          group
        rw [e, hT.1 _ (Kf_left hN ht hu)]
      · have hw := typeB_lt hT (lev (Ad E) r s (x₁, m.2) * finGL E (r + s) t)
        have hW₁ := Wf_left (W := W) hN hw k
        convert hW₁ using 1
        funext k₁
        rw [hval₁]
        rw [infGL_comm, ← mul_assoc, Slice1.lev_infGL_right]
        simp only [map_mul, Slice1.toUnits_levK]
    obtain ⟨χ₁, hχ₁, hχ₁0, hχ₁T⟩ := untw hχ₁' hχ₁'0 hT₁ (Kf_le_det r)

    have hχ₂' : ∑ i, (ψ₁ i).1 m.1 • ψ₂ i ∈ tw t₂.space (-(r : ℂ) / 2) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₂ i)
    have hχ₂'0 : ∑ i, (ψ₁ i).1 m.1 • ψ₂ i ≠ 0 := sum_right_ne hne
    have hval₂ : ∀ x₂, (∑ i, (ψ₁ i).1 m.1 • ψ₂ i).1 x₂ =
        f.1 (lev (Ad E) r s (m.1, x₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t)) := by
      intro x₂
      have e := hsum (m.1, x₂)
      rw [e]
      simp [Finset.sum_apply]
    have hT₂ : SpectralAccumulation.TypeB (Kf N K s) (Wf N W s) (∑ i, (ψ₁ i).1 m.1 • ψ₂ i) := by
      refine ⟨fun u hu x₂ => ?_, fun x₂ => ?_⟩
      · rw [hval₂, hval₂]
        have h1 : lev (Ad E) r s (m.1, x₂ * finGL E s u) =
            lev (Ad E) r s (m.1, x₂) * finGL E (r + s) (lev (Af E) r s (1, u)) := by
          rw [← Slice2.lev_finGL_one, ← map_mul, Prod.mk_mul_mk, mul_one]
        have hc := infGL_comm (Unitary.toUnits k) (lev (Af E) r s (1, u))
        have e : lev (Ad E) r s (m.1, x₂ * finGL E s u) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) =
            lev (Ad E) r s (m.1, x₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) *
              finGL E (r + s) (t⁻¹ * lev (Af E) r s (1, u) * t) := by
          rw [h1, map_mul, map_mul, map_inv]
          simp only [mul_assoc]
          rw [← mul_assoc (finGL E (r + s) (lev (Af E) r s (1, u))), ← hc]
          group
        rw [e, hT.1 _ (Kf_right hN ht hu)]
      · have hw := typeB_lt hT (lev (Ad E) r s (m.1, x₂) * finGL E (r + s) t)
        have hW₂ := Wf_right (W := W) hN hw k
        convert hW₂ using 1
        funext k₂
        rw [hval₂]
        have h1 : lev (Ad E) r s (m.1, x₂ * infGL E s (Unitary.toUnits k₂)) =
            lev (Ad E) r s (m.1, x₂) * infGL E (r + s) (lev (Cinf E) r s (1, Unitary.toUnits k₂)) := by
          rw [← Slice2.lev_infGL_one, ← map_mul, Prod.mk_mul_mk, mul_one]
        rw [h1]
        simp only [map_mul, Slice2.toUnits_levK]
        rw [infGL_comm (Unitary.toUnits k) t]
        simp only [← mul_assoc]
        rw [mul_assoc (lev (Ad E) r s (m.1, x₂)) (infGL E (r + s) (lev (Cinf E) r s (1, Unitary.toUnits k₂))),
          infGL_comm (lev (Cinf E) r s (1, Unitary.toUnits k₂)) t, ← mul_assoc]
    obtain ⟨χ₂, hχ₂, hχ₂0, hχ₂T⟩ := untw hχ₂' hχ₂'0 hT₂ (Kf_le_det s)
    exact ⟨ih₁ (by omega) χ₁ hχ₁ hχ₁0 hχ₁T, ih₂ (by omega) χ₂ hχ₂ hχ₂0 hχ₂T⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

theorem types_holds : Types := by
  intro E _ _ _ N W hW
  refine ⟨fun M => {KTypeSlices.Wf N W M}, fun M => ⟨Set.finite_singleton _, ?_⟩, ?_⟩
  · rintro _ rfl
    exact KTypeSlices.fd_Wf hW M
  intro K hK
  refine ⟨fun M => {KTypeSlices.Kf N K M}, fun M => ⟨Set.finite_singleton _, ?_⟩, ?_⟩
  · rintro _ rfl
    exact KTypeSlices.isOpen_Kf hK M
  intro t f _ hf hf0 hT
  exact KTypeSlices.main_ind K hK W t le_rfl f hf hf0
    ⟨fun u hu g => hT.1 u (KTypeSlices.Kf_top hu) g, fun g => KTypeSlices.lt_le_Wf (KTypeSlices.typeB_lt hT g)⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

end

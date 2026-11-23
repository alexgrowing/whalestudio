import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ReadLimit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PackOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbK
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbC
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbConv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbAlg
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.GelfandValueContinuity.FinSt

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rd

theorem sup_one_ne_bot {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (W : Submodule ℂ (Kinf E a → ℂ)) :
    W ⊔ Submodule.span ℂ {fun _ => (1 : ℂ)} ≠ ⊥ := by
  intro h
  have hm : (fun _ => (1 : ℂ)) ∈ W ⊔ Submodule.span ℂ {fun _ : Kinf E a => (1 : ℂ)} :=
    Submodule.mem_sup_right (Submodule.subset_span rfl)
  rw [h, Submodule.mem_bot] at hm
  have := congrFun hm 1
  simp at this

theorem kTypes_insert {E : Type} [Field E] [NumberField E] [IsCMField E] {Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))}
    (h : KTypes E Ω) : KTypes E (fun M => insert ⊥ (Ω M)) := by
  intro M
  refine ⟨(h M).1.insert _, fun W hW => ?_⟩
  rcases hW with rfl | hW
  · infer_instance
  · exact (h M).2 W hW

set_option maxHeartbeats 4000000 in
theorem readLimit_main (hPack : Pack) (hEF : EFinal) (hAV : ActVal) (hFH : FinHecke) (hVC : ValCont) (hIC : InfConv)
    (hIL : InfLim) (hRE : ReproEx) (hBO : BlockOperatorsProductAdjoint) (hCM : ConvMulSt) (hFin : FinSt) (hReal : RealiseSt) : ReadLimit := by
  intro E _ _ _
  choose Wf₁ Wf₂ hWfd₁ hWfd₂ hP using fun a b (Ma : Mods E a) (Mb : Mods E b) => hPack E a b Ma Mb
  let V₁ : ∀ a b : ℕ, Mods E a → Mods E b → Submodule ℂ (Kinf E a → ℂ) := fun a b Ma Mb =>
    Wf₁ a b Ma Mb ⊔ Submodule.span ℂ {fun _ => (1 : ℂ)}
  let V₂ : ∀ a b : ℕ, Mods E a → Mods E b → Submodule ℂ (Kinf E b → ℂ) := fun a b Ma Mb =>
    Wf₂ a b Ma Mb ⊔ Submodule.span ℂ {fun _ => (1 : ℂ)}
  have hV₁ : ∀ a b Ma Mb, FiniteDimensional ℂ (V₁ a b Ma Mb) := fun a b Ma Mb => by
    haveI := hWfd₁ a b Ma Mb; exact Submodule.finiteDimensional_sup _ _
  have hV₂ : ∀ a b Ma Mb, FiniteDimensional ℂ (V₂ a b Ma Mb) := fun a b Ma Mb => by
    haveI := hWfd₂ a b Ma Mb; exact Submodule.finiteDimensional_sup _ _
  choose Ωf₁ Ωf₂ hΩ₁ hΩ₂ hEr using fun a b (Ma : Mods E a) (Mb : Mods E b) =>
    hEF E a b (V₁ a b Ma Mb) (V₂ a b Ma Mb) (hV₁ a b Ma Mb) (hV₂ a b Ma Mb)
  let Θf₁ : ∀ a b : ℕ, Mods E a → Mods E b → Subgroup (GL (Fin a) (Af E)) → Subgroup (GL (Fin b) (Af E)) → ∀ M : ℕ,
      Set (Subgroup (GL (Fin M) (Af E))) := fun a b Ma Mb K₁ K₂ =>
    if h : IsOpen (K₁ : Set (GL (Fin a) (Af E))) ∧ IsOpen (K₂ : Set (GL (Fin b) (Af E))) then
      (hEr a b Ma Mb K₁ K₂ h.1 h.2).choose else fun _ => ∅
  let Θf₂ : ∀ a b : ℕ, Mods E a → Mods E b → Subgroup (GL (Fin a) (Af E)) → Subgroup (GL (Fin b) (Af E)) → ∀ M : ℕ,
      Set (Subgroup (GL (Fin M) (Af E))) := fun a b Ma Mb K₁ K₂ =>
    if h : IsOpen (K₁ : Set (GL (Fin a) (Af E))) ∧ IsOpen (K₂ : Set (GL (Fin b) (Af E))) then
      (hEr a b Ma Mb K₁ K₂ h.1 h.2).choose_spec.choose else fun _ => ∅
  have hΘ₁ : ∀ a b Ma Mb (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
      (o₁ : IsOpen (K₁ : Set (GL (Fin a) (Af E)))) (o₂ : IsOpen (K₂ : Set (GL (Fin b) (Af E)))),
      Θf₁ a b Ma Mb K₁ K₂ = (hEr a b Ma Mb K₁ K₂ o₁ o₂).choose := fun a b Ma Mb K₁ K₂ o₁ o₂ => dif_pos ⟨o₁, o₂⟩
  have hΘ₂ : ∀ a b Ma Mb (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
      (o₁ : IsOpen (K₁ : Set (GL (Fin a) (Af E)))) (o₂ : IsOpen (K₂ : Set (GL (Fin b) (Af E)))),
      Θf₂ a b Ma Mb K₁ K₂ = (hEr a b Ma Mb K₁ K₂ o₁ o₂).choose_spec.choose := fun a b Ma Mb K₁ K₂ o₁ o₂ => dif_pos ⟨o₁, o₂⟩
  refine ⟨V₁, V₂, fun a b Ma Mb M => insert ⊥ (Ωf₁ a b Ma Mb M), fun a b Ma Mb M => insert ⊥ (Ωf₂ a b Ma Mb M),
    Θf₁, Θf₂, fun a b Ma Mb => ⟨hV₁ a b Ma Mb, hV₂ a b Ma Mb, kTypes_insert (hΩ₁ a b Ma Mb),
      kTypes_insert (hΩ₂ a b Ma Mb), fun M => ⟨⟨⊥, Set.mem_insert _ _⟩, ⟨⊥, Set.mem_insert _ _⟩⟩,
      sup_one_ne_bot _, sup_one_ne_bot _⟩, fun a b Ma Mb K₁ K₂ o₁ o₂ => ?_, ?_⟩
  · rw [hΘ₁ a b Ma Mb K₁ K₂ o₁ o₂, hΘ₂ a b Ma Mb K₁ K₂ o₁ o₂]
    exact ⟨(hEr a b Ma Mb K₁ K₂ o₁ o₂).choose_spec.choose_spec.1, (hEr a b Ma Mb K₁ K₂ o₁ o₂).choose_spec.choose_spec.2.1⟩
  intro B K₁ K₂ o₁ c₁ o₂ c₂ Γ _ g a₀ t₀ bump cK der X tX jX χ _hab hok htX hXe hjX ha₀ hbump _htype hka0 hkb0
    hcK hψ₀ hderA hderB hcomm hXc hXs hχn hχ0 hreg
  rw [hΘ₁ _ _ _ _ K₁ K₂ o₁ o₂, hΘ₂ _ _ _ _ K₁ K₂ o₁ o₂]
  have hEB := (hEr B.a B.b B.Ma B.Mb K₁ K₂ o₁ o₂).choose_spec.choose_spec.2.2
  have hK := perK hAV hBO hCM hFin hReal B (Wf₁ B.a B.b B.Ma B.Mb) (Wf₂ B.a B.b B.Ma B.Mb) K₁ K₂ o₁ c₁ o₂ c₂
    (hP B.a B.b B.Ma B.Mb) Γ g a₀ t₀ bump cK der X tX jX χ hok htX hXe hjX ha₀ hbump hka0 hkb0 hcK hψ₀ hderA hderB
    hcomm hXc hXs hχn hχ0
  exact blockOut_lim hFH hVC hIC hIL hRE hBO hFin B (Wf₁ B.a B.b B.Ma B.Mb) (V₁ B.a B.b B.Ma B.Mb)
    (Wf₂ B.a B.b B.Ma B.Mb) (V₂ B.a B.b B.Ma B.Mb) le_sup_left le_sup_left (Ωf₁ B.a B.b B.Ma B.Mb) (Ωf₂ B.a B.b B.Ma B.Mb)
    (fun M => insert ⊥ (Ωf₁ B.a B.b B.Ma B.Mb M)) (fun M => insert ⊥ (Ωf₂ B.a B.b B.Ma B.Mb M))
    (fun M => Set.subset_insert _ _) (fun M => Set.subset_insert _ _) K₁ K₂ _ _ o₁ c₁ o₂ c₂ hEB Γ g a₀ t₀ cK der X tX jX χ
    hok htX ha₀ hcK hψ₀ hχ0 hreg hK

theorem convMulSt_holds : ConvMulSt := fun _ _ _ _ _ _ D _ _ Φ₁ Φ₂ h₁ h₂ f hf => conv_mulM D Φ₁ Φ₂ h₁ h₂ f hf

theorem readLimit_of (e2 : PositivityTheory.Rg.BcB.E.E2) (pk : Pack) (ef : EFinal) (av : ActVal) (fh : FinHecke) (vc : ValCont)
    (ic : InfConv) (il : InfLim) (re : ReproEx) (tm : TensMul) (bo : BlockOperatorsProductAdjoint) (bw : BlockWordOperators) (bs : BlockLinearCombinations)
    (aw : AdjWords) : ReadLimit :=
  readLimit_main pk ef av fh vc ic il re bo convMulSt_holds finSt (realise e2 tm bo bw bs aw)

end PositivityTheory.Rg.BcB.F.Rd.B

end

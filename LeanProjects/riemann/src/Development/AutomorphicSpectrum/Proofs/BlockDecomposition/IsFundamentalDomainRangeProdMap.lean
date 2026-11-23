import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ProperRatH
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightHaarMeasure

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.PairDom

theorem isFundamentalDomain_range_prodMap {A B X Y : Type} [Group A] [Group B] [Group X] [Group Y]
    [TopologicalSpace X] [TopologicalSpace Y] [IsTopologicalGroup X] [IsTopologicalGroup Y]
    [SecondCountableTopology X] [SecondCountableTopology Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant] (f : A →* X) (g : B →* Y) (F : Set X) (G : Set Y)
    (hF : IsFundamentalDomain f.range F μ) (hG : IsFundamentalDomain g.range G ν) :
    IsFundamentalDomain (f.prodMap g).range (F ×ˢ G) (μ.prod ν) := by
  have hmp : ∀ z : X × Y, MeasurePreserving (z * ·) (μ.prod ν) (μ.prod ν) := fun z =>
    measurePreserving_mul_left (μ.prod ν) z
  refine IsFundamentalDomain.mk'' (hF.nullMeasurableSet.prod hG.nullMeasurableSet) ?_ ?_
    (fun γ => (hmp γ).quasiMeasurePreserving)
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hF.ae_covers,
      Measure.quasiMeasurePreserving_snd.ae hG.ae_covers] with z h1 h2
    obtain ⟨⟨_, a, rfl⟩, ha⟩ := h1
    obtain ⟨⟨_, b, rfl⟩, hb⟩ := h2
    exact ⟨⟨(f a, g b), (a, b), rfl⟩, ha, hb⟩
  · rintro ⟨_, ⟨a, b⟩, rfl⟩ hγ
    by_cases ha : f a = 1
    · have hb : (⟨g b, b, rfl⟩ : g.range) ≠ 1 := by
        intro h
        apply hγ
        apply Subtype.ext
        exact Prod.ext ha (congrArg Subtype.val h)
      have h3 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).preimage_null (hG.aedisjoint hb)
      refine measure_mono_null ?_ h3
      rintro z ⟨⟨w, hw, rfl⟩, hz⟩
      exact ⟨⟨w.2, hw.2, rfl⟩, ⟨_, hz.2, one_smul _ _⟩⟩
    · have ha' : (⟨f a, a, rfl⟩ : f.range) ≠ 1 := by
        intro h
        exact ha (congrArg Subtype.val h)
      have h3 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).preimage_null (hF.aedisjoint ha')
      refine measure_mono_null ?_ h3
      rintro z ⟨⟨w, hw, rfl⟩, hz⟩
      exact ⟨⟨w.1, hw.1, rfl⟩, ⟨_, hz.1, one_smul _ _⟩⟩

theorem exists_measure_of_eq {X Y : Type} [Group X] [Group Y] [TopologicalSpace X] [TopologicalSpace Y]
    [IsTopologicalGroup X] [IsTopologicalGroup Y] [LocallyCompactSpace X] [LocallyCompactSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y] (μ₁ : Measure X) (μ₂ : Measure Y)
    [μ₁.IsHaarMeasure] [μ₂.IsHaarMeasure] [μ₁.IsMulRightInvariant] [μ₂.IsMulRightInvariant]
    (Γ : Subgroup (X × Y)) (F : Set (X × Y)) (hF : IsFundamentalDomain Γ F (μ₁.prod μ₂))
    (m : MeasurableSpace (X × Y)) (e : Prod.instMeasurableSpace = m) :
    ∃ μ : @Measure (X × Y) m,
      (@Measure.IsMulLeftInvariant _ m _ μ ∧ @Measure.IsMulRightInvariant _ m _ μ ∧
        @Measure.IsOpenPosMeasure _ _ m μ ∧ @IsLocallyFiniteMeasure _ m _ μ) ∧
      @IsFundamentalDomain Γ (X × Y) _ _ m F μ ∧
      ∀ f : X × Y → ℂ, @integral _ _ _ _ m (@Measure.restrict _ m μ F) f =
        @integral _ _ _ _ Prod.instMeasurableSpace ((μ₁.prod μ₂).restrict F) f := by
  subst e
  haveI : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  exact ⟨μ₁.prod μ₂, ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hF, fun _ => rfl⟩

theorem isMulRightInvariant_GA (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    [m : MeasurableSpace (GA E a)] [hm : BorelSpace (GA E a)] (μ : Measure (GA E a)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  obtain ⟨ν, h1, h2⟩ := GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant E a
  have e : m = CuspidalL2GL.measurableSpace_GA E a := hm.measurable_eq
  subst e
  haveI := CuspidalL2GL.t2Space_GA E a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  rw [Measure.isMulLeftInvariant_eq_smul μ ν]
  infer_instance

theorem prodDom : RatProper → ProdDom := by
  intro _ E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ F₁ F₂ h₁ h₂
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E b
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E b
  haveI := isMulRightInvariant_GA E a μ₁
  haveI := isMulRightInvariant_GA E b μ₂
  haveI : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  obtain ⟨μ, hh, hf, hi⟩ := exists_measure_of_eq μ₁ μ₂ (ratH E a b) (F₁ ×ˢ F₂)
    (isFundamentalDomain_range_prodMap μ₁ μ₂ (ratGL E a) (ratGL E b) F₁ F₂ h₁ h₂) (borelH E a b)
    Prod.borelSpace.measurable_eq
  exact ⟨⟨μ, hh, F₁ ×ˢ F₂, hf⟩, rfl, fun f => hi f⟩

end GlobalTheory.CompanionTheory.PairDom

import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairChangedDualVectorsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesLocalHeightEqResidueCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairAmplitudeMassRepsEqOrbits
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.WCoordTerms

theorem terms_orbits_heights_amps : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : WCoord P S), (∀ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t → S.IsTerm (c.dat d) (c.lat t.abelian₂) ∧ LocNG.om P t = S.om (c.dat d) (c.lat t.abelian₂) ∧ (LocNG.BBne (H := H) t ↔ ¬ S.BBzero (c.dat d) (c.lat t.abelian₂))) ∧ (∀ d d' : LocNG.Datum P, LocNG.Datum.Rel d d' ↔ ∃ h ∈ S.H0, h • c.dat d = c.dat d') ∧ P.Hp = S.Hp ∧ (P.PrimeTo → S.Hp = 1) ∧ ∀ (R : LocNG.Reps P) (d : LocNG.Datum P), LocNG.amp R d (LocNG.BBne (H := H)) = S.amp (c.dat d) (fun Λ => ¬ S.BBzero (c.dat d) Λ) ∧ LocNG.amp R d (fun t => ¬ LocNG.BBne (H := H) t) = S.amp (c.dat d) (S.BBzero (c.dat d)) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  obtain ⟨P₂, c₂, φ, he, hSt, hK0, hUW, hHp, hPT, hdat, hterm, hom, hmov⟩ := GlobalTheory.T.framePair_changed_dualVectors M hM H r k P S c
  have hlat : ∀ Λ, c₂.lat Λ = c.lat Λ := fun Λ => by simp only [Coord.lat, WCoord.lat, he]
  have hrel : ∀ d d', LocNG.Datum.Rel d d' ↔ LocNG.Datum.Rel (φ d) (φ d') := by
    intro d d'
    unfold LocNG.Datum.Rel
    rw [hUW]
    exact exists_congr fun g => and_congr_right fun _ => hmov g d d'
  have hTR : LocNG.TRel P₂ = LocNG.TRel P := by
    funext t t'
    unfold LocNG.TRel
    rw [hSt]
  have hmu : ∀ t, LocNG.mu P₂ t = LocNG.mu P t := fun t => by
    unfold LocNG.mu
    rw [hSt, hK0]
  have T2 := GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P₂ S c₂
  have TD := GlobalTheory.HL.CoordDatum.transport M hM H r k P₂ S c₂
  have TH := GlobalTheory.HL.CoordHeight.height_eq M hM H r k P₂ S c₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d t ht
    have h := T2.1 (φ d) t ((hterm d t).1 ht)
    rw [hdat, hlat, hom d t ht] at h
    exact h
  · intro d d'
    rw [hrel, TD.2.2.1, hdat, hdat]
  · rw [← hHp]
    exact TH.1
  · intro hp
    obtain ⟨h1, h2, h3⟩ := TH.2.2 ((hPT).2 hp)
    have hvth : S.vth = 0 := by simp [Frames.vth, h1]
    have ha : S.a = 0 := by simp [Frames.a, h2, hvth]
    have hvD : S.vD = 0 := Finset.sum_eq_zero fun l _ => by
      split_ifs with h
      · exact h3 l h.2
      · rfl
    simp [Frames.Hp, hvth, ha, hvD]
  · intro R d
    let R₂ : LocNG.Reps P₂ :=
      { RD := φ '' R.RD
        RT := fun d₂ => R.RT (φ.symm d₂)
        hRD := by
          refine ⟨Set.subset_univ _, fun x _ => ?_, ?_⟩
          · obtain ⟨y, hy, hr⟩ := R.hRD.2.1 (φ.symm x) trivial
            refine ⟨φ y, ⟨y, hy, rfl⟩, ?_⟩
            have := (hrel y (φ.symm x)).1 hr
            rwa [φ.apply_symm_apply] at this
          · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
            exact congrArg φ (R.hRD.2.2 a ha b hb ((hrel a b).2 h))
        hRT := fun d₂ => by
          have hs : {t | LocNG.IsTermOver P₂ d₂ t} = {t | LocNG.IsTermOver P (φ.symm d₂) t} := by
            ext t
            simp only [Set.mem_setOf_eq]
            rw [hterm, φ.apply_symm_apply]
          rw [hs, hTR]
          exact R.hRT _ }
    have hamp : ∀ Q, LocNG.amp R d Q = LocNG.amp R₂ (φ d) Q := by
      intro Q
      unfold LocNG.amp
      have e : R₂.RT (φ d) = R.RT d := by simp [R₂]
      rw [e]
      refine tsum_congr fun t => ?_
      rw [hmu, hom d t.1 ((R.hRT d).1 t.2.1)]
    have A := GlobalTheory.HL.CoordAmp.amp_mass_eq M hM H r k P₂ S c₂ R₂ (φ d)
    rw [hdat] at A
    exact ⟨(hamp _).trans A.1, (hamp _).trans A.2.1⟩

end GlobalTheory.HL.WCoordTerms

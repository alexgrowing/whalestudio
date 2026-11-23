import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairAmplitudeMassRepsEqOrbitsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairTsumRepsEqConstMulOrbitsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumOrbitNormaliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordSq

open scoped Pointwise ENNReal Classical in
open ValuativeRel in
open scoped Pointwise ENNReal Classical in

theorem _root_.GlobalTheory.HL.CoordSq.sums_eq : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : _root_.Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : _root_.Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ)
    (P : _root_.Formalism.MainNotions.S.LocNG.FPair H r), ∀ (S : _root_.GlobalTheory.HL.Frames M.L r k) (c : _root_.GlobalTheory.HL.Coord P S),
    ∀ (R : _root_.Formalism.MainNotions.S.LocNG.Reps P) (d0 : _root_.Formalism.MainNotions.S.LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧
      _root_.Formalism.MainNotions.S.LocNG.sumSq R d0 (_root_.Formalism.MainNotions.S.LocNG.BBne (H := H))
        = ENNReal.ofReal κ * S.ampSq (fun d Λ => ¬ S.BBzero d Λ) ∧
      _root_.Formalism.MainNotions.S.LocNG.sumSq R d0 (fun t => ¬ _root_.Formalism.MainNotions.S.LocNG.BBne (H := H) t)
        = ENNReal.ofReal κ * S.ampSq S.BBzero ∧
      _root_.Formalism.MainNotions.S.LocNG.sumSq R d0 (fun _ => True) = ENNReal.ofReal κ * S.ampSq (fun _ _ => True) ∧
      _root_.Formalism.MainNotions.S.LocNG.nn R d0 = ENNReal.ofReal κ * S.nn := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c R d0
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨κ, hκ, hsum⟩ := _root_.GlobalTheory.HL.CoordSum.tsum_reps_eq M hM H r k P S c R d0
  have hamp := _root_.GlobalTheory.HL.CoordAmp.amp_mass_eq M hM H r k P S c R
  have hvanA : ∀ (δ : S.Datum) (Q : Submodule M.L.O S.V → Prop),
      (¬ ∃ Λ, S.IsTerm δ Λ) → S.amp δ Q = 0 := by
    intro δ Q hδ
    unfold _root_.GlobalTheory.HL.Frames.amp
    refine (tsum_congr fun o => ?_).trans tsum_zero
    rw [if_neg fun h => hδ ⟨_, h.1⟩]
  have hvanM : ∀ (δ : S.Datum) (Q : Submodule M.L.O S.V → Prop),
      (¬ ∃ Λ, S.IsTerm δ Λ) → S.mass δ Q = 0 := by
    intro δ Q hδ
    unfold _root_.GlobalTheory.HL.Frames.mass
    refine (tsum_congr fun o => ?_).trans tsum_zero
    rw [if_neg fun h => hδ ⟨_, h.1⟩]
  have hinv : ∀ h ∈ S.H0, ∀ (δ : S.Datum) (Q : S.Datum → Submodule M.L.O S.V → Prop),
      (∀ δ', ∀ s ∈ S.St, ∀ Λ, S.IsTerm δ' Λ → Q δ' Λ → Q δ' (s • Λ)) →
      (∀ δ' Λ, S.IsTerm δ' Λ → (Q δ' Λ ↔ Q (h • δ') (h • Λ))) →
      S.amp (h • δ) (Q (h • δ)) = S.amp δ (Q δ) ∧
        S.mass (h • δ) (Q (h • δ)) = S.mass δ (Q δ) :=
    fun h hh δ Q h1 h2 => _root_.GlobalTheory.InvH.amp_mass_smul M.L r k S h hh δ (Q δ)
      (Q (h • δ)) (fun s hs Λ hΛ => h1 δ s hs Λ hΛ) (fun Λ hΛ => h2 δ Λ hΛ)
  have hBBst : ∀ δ', ∀ s ∈ S.St, ∀ Λ, S.IsTerm δ' Λ →
      (S.BBzero δ' (s • Λ) ↔ S.BBzero δ' Λ) :=
    fun δ' s hs Λ hΛ =>
      (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S δ' Λ hΛ s hs).2.2.2.2.2.2.2.1
  have hBBh : ∀ h ∈ S.H0, ∀ δ' Λ, S.IsTerm δ' Λ →
      (S.BBzero δ' Λ ↔ S.BBzero (h • δ') (h • Λ)) := by
    intro h hh δ' Λ hΛ
    obtain ⟨-, -, -, hM', hsat, -⟩ :=
      _root_.GlobalTheory.HL.ComplAct.main M.L r k S δ' Λ hΛ h hh
    unfold _root_.GlobalTheory.HL.Frames.BBzero
    rw [hM', hsat]
  have hsq : ∀ z : ℂ, ((‖z‖₊ : ℝ≥0∞) ^ 2) = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  have hA : ∀ (p : _root_.Formalism.MainNotions.S.Loc.Term V M r → Prop) (Q : S.Datum → Submodule M.L.O S.V → Prop),
      (∀ d, _root_.Formalism.MainNotions.S.LocNG.amp R d p
        = S.amp (c.dat d) (Q (c.dat d))) →
      (∀ δ', ∀ s ∈ S.St, ∀ Λ, S.IsTerm δ' Λ → Q δ' Λ → Q δ' (s • Λ)) →
      (∀ h ∈ S.H0, ∀ δ' Λ, S.IsTerm δ' Λ → (Q δ' Λ ↔ Q (h • δ') (h • Λ))) →
      _root_.Formalism.MainNotions.S.LocNG.sumSq R d0 p = ENNReal.ofReal κ * S.ampSq Q := by
    intro p Q hpQ h1 h2
    unfold _root_.Formalism.MainNotions.S.LocNG.sumSq _root_.GlobalTheory.HL.Frames.ampSq
    rw [← hsum (fun δ => ENNReal.ofReal (‖S.amp δ (Q δ)‖ ^ 2))
      (fun h hh δ => by rw [(hinv h hh δ Q h1 (h2 h hh)).1])
      (fun δ hδ => by rw [hvanA δ _ hδ, norm_zero]; simp)]
    refine tsum_congr fun d => ?_
    rw [hpQ, hsq]
  refine ⟨κ, hκ, ?_, ?_, ?_, ?_⟩
  · exact hA _ (fun δ Λ => ¬ S.BBzero δ Λ) (fun d => (hamp d).1)
      (fun δ' s hs Λ hΛ hq => by rwa [hBBst δ' s hs Λ hΛ])
      (fun h hh δ' Λ hΛ => not_congr (hBBh h hh δ' Λ hΛ))
  · exact hA _ S.BBzero (fun d => (hamp d).2.1)
      (fun δ' s hs Λ hΛ hq => (hBBst δ' s hs Λ hΛ).2 hq)
      (fun h hh δ' Λ hΛ => hBBh h hh δ' Λ hΛ)
  · exact hA _ (fun _ _ => True) (fun d => (hamp d).2.2.1)
      (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ => Iff.rfl)
  · unfold _root_.Formalism.MainNotions.S.LocNG.nn _root_.GlobalTheory.HL.Frames.nn
    rw [← hsum (fun δ => S.mass δ (fun _ => True))
      (fun h hh δ => (hinv h hh δ (fun _ _ => True) (fun _ _ _ _ _ _ => trivial)
        (fun _ _ _ => Iff.rfl)).2)
      (fun δ hδ => hvanM δ _ hδ)]
    refine tsum_congr fun d => ?_
    rw [(hamp d).2.2.2]

end GlobalTheory.HL.CoordSq

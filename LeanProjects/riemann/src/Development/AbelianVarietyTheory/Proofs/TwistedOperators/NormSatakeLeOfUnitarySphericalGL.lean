import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SatakeTrivialRangeBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.LFun.SatBoundGL

private theorem mem_adicCompletionIntegers_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) :
    letI := GlobalTheory.LocalData.complRel w
    x ∈ Valuation.integer (ValuativeRel.valuation (w.adicCompletion E)) ↔ x ∈ w.adicCompletionIntegers E := by
  letI := GlobalTheory.LocalData.complRel w
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [Valuation.mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  simpa using h x 1

open ValuativeRel in

theorem resCard_completion {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    GlobalTheory.SplitWeil.resCard (w.adicCompletion E) = Ideal.absNorm w.asIdeal := by
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w

  let e : Valuation.integer (ValuativeRel.valuation (w.adicCompletion E)) ≃+* w.adicCompletionIntegers E :=
    { toFun := fun x => ⟨x.1, (mem_adicCompletionIntegers_iff w x.1).1 x.2⟩
      invFun := fun y => ⟨y.1, (mem_adicCompletionIntegers_iff w y.1).2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  unfold GlobalTheory.SplitWeil.resCard
  rw [Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv, Formalism.UG.P.tjcosets_card_residue w]
  rfl

theorem norm_le_of_hasSatGL : GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.SatakeTrivialBound → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (B : Multiset ℂˣ), GlobalTheory.LGrp.IsIrrSmooth ρ → GlobalTheory.LGrp.IsUnitarisable ρ → HasSatGL w ρ B → ∀ b ∈ B, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  intro hT E _ _ w n V _ _ ρ B hirr hun hsat b hb
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  obtain ⟨hsph, hvec⟩ := hsat

  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hsph
  have hG : LGrp.HasSatakeGL ρ B := GlobalTheory.LFun.SatCompare.hasSatakeGL_of_isSatVecGL hirr (hvec x hx hx0)
  obtain ⟨α, hαB, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ ρ B).mp hG
  have hR := hT (w.adicCompletion E) n V ρ α hirr.1 hirr.2 ((GlobalTheory.LGrp.isUnitarisable_iff ρ).mp hun) ?_ hα
  · rw [← hαB] at hb
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hb
    have hi := (hR i).2
    rwa [resCard_completion] at hi
  · unfold GlobalTheory.SmGL.IsSpherical
    exact (GlobalTheory.LGrp.isSpherical_iff ρ _).mp hG.2

end GlobalTheory.LFun.SatBoundGL

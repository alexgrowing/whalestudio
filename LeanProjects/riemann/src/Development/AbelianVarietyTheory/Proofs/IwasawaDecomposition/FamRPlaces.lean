import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3

theorem famR_places : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    (∀ t P, P ∈ (famR X I hX U Xg tr).A.ok t ↔
      Bridge.SplitOff (P.1 : Pl X.toD7.host.E) ((L.Pg : Set (Pl X.toD7.host.E)) ∪ (L.Q t : Set (Pl X.toD7.host.E)))) ∧
    (∀ PP, Bridge.SplitOff PP (L.Pg : Set (Pl X.toD7.host.E)) → ∃ P : PlS X.B px, (P.1 : Pl X.toD7.host.E) = PP) ∧
    Bridge.InertTie (famR X I hX U Xg tr) (fun Q : PlI X.B px => (Q.1 : Pl X.toD7.host.E)) (L.Pg : Set (Pl X.toD7.host.E)) L.Q ∧
    (∀ PP, Bridge.InertOff PP (L.Pg : Set (Pl X.toD7.host.E)) → ∃ Q : PlI X.B px, (Q.1 : Pl X.toD7.host.E) = PP) := by
  intro X px I hX U Xg tr L eG _ _ hL _
  have hS : ∀ t : TupU I U, ((∅ : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      ((∅ : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      ((Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) :
        Set (HeightOneSpectrum (𝓞 X.B.fields.E)))) =
      (L.Pg : Set (Pl X.toD7.host.E)) ∪ (L.Q t : Set (Pl X.toD7.host.E)) := by
    intro t
    rw [hL.Pg, hL.Q t]
    have e : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel (t.1 : Chr X.B.fields.F X.B.fields.E X.B.fields.K) := by
      show Formalism.L2.Col.QE I.sel (I.tup (ixOf I U t) : Chr X.B.fields.F X.B.fields.E X.B.fields.K) = _
      rw [tup_ixOf I t]
    rw [e]
    simp [Formalism.L2.Col.rowSG, Formalism.L2.Col.uSG]
    rfl
  have hS0 : ((∅ : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      ((∅ : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      (((X.B.primes px).vGs : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) : Set (HeightOneSpectrum (𝓞 X.B.fields.E)))) =
      (L.Pg : Set (Pl X.toD7.host.E)) := by
    rw [hL.Pg]
    simp
    rfl
  refine ⟨fun t P => ?_, fun PP hPP => ?_, ⟨Subtype.val_injective, fun t Q => ?_⟩, fun PP hPP => ?_⟩
  · show P.1 ∈ Formalism.L2.DIV.offSet ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ∅ ↔ _
    unfold Formalism.L2.DIV.offSet Formalism.IndefR.Bridge.SplitOff
    rw [Set.mem_setOf_eq, hS t]
    exact Iff.rfl
  · obtain ⟨h1, h2, h3⟩ := hPP
    refine ⟨⟨PP, h1, ?_, fun Q hQ => h3 Q ?_⟩, rfl⟩
    · rw [hS0]; exact h2
    · rw [← hS0]; exact hQ
  · show Q.1 ∉ _ ↔ _
    unfold Formalism.IndefR.Bridge.InertOff
    rw [hS t]
    have hc : ∀ P : Pl X.toD7.host.E, Formalism.L2.Col.conjPrime₂ P = P →
        Formalism.HermitianLatticesTheory.conjIdeal (K := X.toD7.host.E) P.asIdeal = P.asIdeal := fun P hP => by
      rw [Formalism.L2.Col.conjIdeal_asIdeal, hP]
    exact ⟨fun h => ⟨hc Q.1 Q.2.1, h⟩, fun h => h.2⟩
  · obtain ⟨h1, h2⟩ := hPP
    have hc : Formalism.L2.Col.conjPrime₂ PP = PP := HeightOneSpectrum.ext (by rw [← Formalism.L2.Col.conjIdeal_asIdeal]; exact h1)
    have hin : ∃ x : 𝓞 X.toD7.host.E, Formalism.L2.Col.cO X.toD7.host.E x - x ∉ PP.asIdeal := by
      obtain ⟨θ, t, ht, hθ⟩ := X.toD7.sp.cm.cmUnram.2.2 PP.asIdeal PP.isMaximal
      have e : Formalism.L2.Col.cO X.toD7.host.E θ = t := RingOfIntegers.ext ht.symm
      refine ⟨θ, fun h => hθ ?_⟩
      rw [e] at h
      rw [← neg_sub]
      exact PP.asIdeal.neg_mem h
    refine ⟨⟨PP, hc, hin, ?_⟩, rfl⟩
    rw [hS0]; exact h2

end GlobalTheory.Mem.R3

end

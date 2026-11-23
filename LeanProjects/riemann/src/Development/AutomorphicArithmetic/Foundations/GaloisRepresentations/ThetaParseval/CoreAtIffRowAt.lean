import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRegAlgTwistOfHalfIntegral
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.TP

open Sub

theorem map_wtJumps {a : ℕ} (lam : DomWeight a) :
    (wtJumps lam).map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map fun z => ((a : ℂ) - 1) / 2 - z := by
  simp only [wtJumps, infOfWeight, Multiset.map_map]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp_apply]
  push_cast
  ring

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]

theorem sphG_iff_cl (hS : SatPol) {a : ℕ} (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E))
    (B : Multiset ℂˣ) (lam : (E →+* ℂ) → DomWeight a) :
    (∀ c, GlobalTheory.Row9.SphG c ι r w B fun τ => infOfWeight (lam τ)) ↔
      Cl ι r w (algSat a (normV w) B) (GlobalTheory.GalDef.jumpsOf ι lam) := by
  constructor
  · intro h
    refine ⟨h .unr, fun P AI hT A hA O _ _ _ Bw hj => ⟨h .crys P AI hT A hA O Bw hj, (h .dR P AI hT A hA O Bw hj).1,
      fun τ LL' τ' hi => (h .dR P AI hT A hA O Bw hj).2 τ LL' τ' hi _ (map_wtJumps _), fun g => ?_⟩⟩
    rw [← hS E Ω A w hA a B g]
    exact h .phi P AI hT A hA O Bw hj g
  · rintro ⟨h1, h2⟩ c
    cases c with
    | unr => exact h1
    | dR =>
      intro P AI hT A hA O _ _ _ Bw hj
      refine ⟨(h2 P AI hT A hA O Bw hj).2.1, fun τ LL' τ' hi J hJ => ?_⟩
      have e : J = wtJumps (lam (ι.toRingHom.comp τ)) :=
        Multiset.map_injective Int.cast_injective (hJ.trans (map_wtJumps _).symm)
      rw [e]
      exact (h2 P AI hT A hA O Bw hj).2.2.1 τ LL' τ' hi
    | crys => exact fun P AI hT A hA O _ _ _ Bw hj => (h2 P AI hT A hA O Bw hj).1
    | phi =>
      intro P AI hT A hA O _ _ _ Bw hj g
      rw [hS E Ω A w hA a B g]
      exact (h2 P AI hT A hA O Bw hj).2.2.2 g

variable (E Ω) in

def CoreAt (ι : Qbar l ≃+* ℂ) (m : ℕ) : Prop :=
  ∀ U : Submodule ℂ (UA E m → ℂ), IsAutRepU U → ∀ lam : (E →+* ℂ) → DomWeight m, (∀ τ, HasWeightAt U τ (lam τ)) →
    ∃ r : G E Ω →* GL (Fin m) (Qbar l), Continuous r ∧ IsSSRep r ∧
      ∀ w B, GlobalTheory.Row9.SatU U w B → ∀ c, GlobalTheory.Row9.SphG c ι r w B fun τ => infOfWeight (lam τ)

end UpperTheory.Gal.TP

end

import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundOfDuality
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CardOfAddEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ArGlob
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ArchH0Card
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CkCastMod
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ArUr
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.DegSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CohAxIso

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa.B2

namespace UpperTheory.V.Pa

private theorem mem_of_over {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {B : ValuationSubring Ω} {w : Plc L} {v : Plc (Lp L)} (hw : IsPlaceOver B w) (hv : IsPlaceOver B v) (l : ℕ) :
    ((l : ℕ) : 𝓞 L) ∈ w.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ v.asIdeal := by
  have h := hw ((l : ℕ) : 𝓞 L)
  have h' := hv ((l : ℕ) : 𝓞 (Lp L))
  have e : algebraMap L Ω (((l : ℕ) : 𝓞 L) : L) = (l : Ω) := by simp
  have e' : algebraMap (Lp L) Ω (((l : ℕ) : 𝓞 (Lp L)) : Lp L) = (l : Ω) := by simp
  rw [e] at h
  rw [e'] at h'
  exact h.symm.trans h'

theorem B2.cohAxAr (hP : CohP) (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) :
    CohAx (globOf r V) (Module.finrank ℚ (Lp L)) fun v => locDeg (s.w (Subtype.val v)) := by
  have hg := arGlob hP (Lp L) Ω l V.S' s.odd V.fin fun v hv => V.sub (Or.inl hv)
  have hl := fun v => arLoc hP L Ω l (s.A v) (s.w v) (s.hw v)
  exact
    { sum := arSum l L Ω s V0 V O n r
      fin := hg.1
      finV := fun v => (hl (Subtype.val v)).1
      finU := fun u => (hl (Subtype.val u)).1
      onto := hg.2
      ge := arGE hP l L Ω s V0 V O n r
      leV := fun v => (hl (Subtype.val v)).2.2.1 ((mem_of_over (s.hw _) (s.hA _) l).2 (Subtype.property v))
      leU := fun u => (hl (Subtype.val u)).2.2.2 fun h =>
        s.St_l _ (Subtype.property u) ((mem_of_over (s.hw _) (s.hA _) l).1 h)
      ur := arUr hP l L Ω s V0 V O n r
      ck := arCk hP l L Ω s V0 V O n r }

theorem b2Ar : TaylorWilesObstructionBound := fun hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r T P x k al _ _ hPL hE =>
  obstructionBound_of_duality l _ _ T n x k al (Module.finrank ℚ (Lp L)) s.odd ⟨_, B2.cohAxAr hP l L Ω s V0 V0 O n r⟩
    (fun N => ⟨_, cohAxIso l _ _ _ (P.e N) _ _ (P.e_inj N) (B2.cohAxAr hP l L Ω s V0 (P.V N) O n r)⟩) hPL hE

end UpperTheory.V.Pa

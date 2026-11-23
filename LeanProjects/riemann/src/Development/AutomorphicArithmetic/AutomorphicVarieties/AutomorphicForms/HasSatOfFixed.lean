import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HasFixedVector

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG

namespace UpperTheory.V.Af

variable {F : Type} [Field F] [NumberField F]

private theorem sLoc_mem (w : HeightOneSpectrum (𝓞 F)) (x : Ov F w) : sLoc F w x ∈ Ohat F := by
  classical
  refine Subring.mem_iInf.2 fun v => ?_
  change (Pi.single w (x : w.adicCompletion F) : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) v ∈
    v.adicCompletionIntegers F
  by_cases h : v = w
  · subst h
    rw [Pi.single_eq_same]
    exact x.2
  · rw [Pi.single_eq_of_ne h]
    exact zero_mem _

private def sInt (w : HeightOneSpectrum (𝓞 F)) : Ov F w →ₙ+* Ohat F where
  toFun x := ⟨sLoc F w x, sLoc_mem w x⟩
  map_mul' x y := Subtype.ext (map_mul (sLoc F w) x.1 y.1)
  map_zero' := Subtype.ext (map_zero (sLoc F w))
  map_add' x y := Subtype.ext (map_add (sLoc F w) x.1 y.1)

theorem LocIsotypic.hasFixed {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) (Af F)) V} {w : HeightOneSpectrum (𝓞 F)}
    {σ : SmIrr (GL (Fin n) (w.adicCompletion F))} (h : LocIsotypic ρ w σ)
    {U : Subgroup (GL (Fin n) (w.adicCompletion F))} (hU : IsCompact (U : Set (GL (Fin n) (w.adicCompletion F))))
    (hf : HasFixed (ρ.comp (locGL F n w)) U) : HasFixed σ.ρ U :=
  _root_.UpperTheory.Reformulated.B.HasFixedVector.hasFixed h hU hf

end UpperTheory.V.Af

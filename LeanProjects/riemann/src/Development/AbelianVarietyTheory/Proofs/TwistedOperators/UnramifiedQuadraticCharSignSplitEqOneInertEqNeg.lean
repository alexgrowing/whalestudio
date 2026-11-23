import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QuadSignLocal

theorem primesOver_eq_image (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Ideal.primesOver v.asIdeal (𝓞 D.host.E) =
      HeightOneSpectrum.asIdeal '' {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = v} := by
  ext P
  constructor
  · rintro ⟨hP, hlo⟩
    refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, ?_, rfl⟩
    ext1
    simp only [HeightOneSpectrum.under_asIdeal]
    exact (Ideal.LiesOver.over (P := P) (p := v.asIdeal)).symm
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.isPrime, ⟨?_⟩⟩
    have := congrArg HeightOneSpectrum.asIdeal hu
    simp only [HeightOneSpectrum.under_asIdeal] at this
    exact this.symm

theorem ncard_primesOver (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (Ideal.primesOver v.asIdeal (𝓞 D.host.E)).ncard =
      {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = v}.ncard := by
  rw [primesOver_eq_image]
  exact Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)

theorem quadSign_split_inert : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w w' : HeightOneSpectrum (𝓞 D.host.E), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') → quadSign D v = 1) ∧ (∀ w : HeightOneSpectrum (𝓞 D.host.E), (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w) → quadSign D v = -1) := by
  intro D v
  constructor
  · intro w w' hne h
    have hs : {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = v} = {w, w'} := by
      ext u; simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]; exact h u
    have h2 : (Ideal.primesOver v.asIdeal (𝓞 D.host.E)).ncard = 2 := by
      rw [ncard_primesOver, hs, Set.ncard_pair hne]
    unfold quadSign
    rw [if_pos h2]
  · intro w h
    have hs : {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = v} = {w} := by
      ext u; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]; exact h u
    have h1 : (Ideal.primesOver v.asIdeal (𝓞 D.host.E)).ncard = 1 := by
      rw [ncard_primesOver, hs, Set.ncard_singleton]
    unfold quadSign
    rw [if_neg (by rw [h1]; decide)]

end GlobalTheory.QuadSignLocal

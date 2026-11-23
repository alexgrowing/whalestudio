import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithResidueCharFibreStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLoweringFibreDimensionStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.NoethGens

theorem exists_cover (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsArithVar p D) (P : Pair p) (hP : IsAmpleLB P.L.B) (d : ℕ) :
    ∀ Z : Set X, IsClosed Z → (∀ ℓ : ℕ, topologicalKrullDim ↥(Z ∩ fib X ℓ) < d) →
      ∃ (e : ℕ) (x : Fin d → X.functionField), 0 < e ∧ (∀ l, x l ∈ P.H e 0) ∧ ∀ z ∈ Z, ∃ l, z ∈ NV P e 0 (x l) := by
  induction d with
  | zero =>
    intro Z _ h
    refine ⟨1, Fin.elim0, one_pos, fun l => l.elim0, fun z hz => ?_⟩
    exfalso
    have h₁ := h (ringChar (X.residueField z))
    have hne : Nonempty ↥(Z ∩ fib X (ringChar (X.residueField z))) := ⟨⟨z, hz, rfl⟩⟩
    obtain ⟨w⟩ := hne
    have hne' : Nonempty (IrreducibleCloseds ↥(Z ∩ fib X (ringChar (X.residueField z)))) :=
      ⟨⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have h₂ : (0 : WithBot ℕ∞) ≤ topologicalKrullDim ↥(Z ∩ fib X (ringChar (X.residueField z))) :=
      Order.krullDim_nonneg
    exact absurd h₁ (not_lt.2 (by simpa using h₂))
  | succ d ih =>
    intro Z hZ h
    obtain ⟨e, he, f, hf, hlt⟩ := GlobalTheory.T.exists_section_lowering_fibre_dimension k X p D hX P hP d Z hZ fun ℓ =>
      ENat.WithBot.lt_add_one_iff.1 (by simpa using h ℓ)
    have hnf := GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 f hf
    obtain ⟨e', x, he', hx, hc⟩ := ih (Z \ NV P e 0 f) (hZ.sdiff hnf.1) hlt
    have c₁ : ((e' * e : ℕ) : ℤ) = (e' : ℤ) * (e : ℤ) := Nat.cast_mul _ _
    have c₂ : ((e' * e : ℕ) : ℤ) = (e : ℤ) * (e' : ℤ) := by rw [c₁, mul_comm]
    refine ⟨e' * e, Fin.cons (f ^ e') fun l => x l ^ e, Nat.mul_pos he' he, fun l => ?_, fun z hz => ?_⟩
    · refine Fin.cases ?_ (fun l => ?_) l
      · have := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 f hf e').1
        rw [mul_zero, ← c₁] at this
        simpa only [Fin.cons_zero] using this
      · have := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e' 0 (x l) (hx l) e).1
        rw [mul_zero, ← c₂] at this
        simpa only [Fin.cons_succ] using this
    · by_cases hzf : z ∈ NV P e 0 f
      · refine ⟨0, ?_⟩
        have := hnf.2.2.1 e' he'
        rw [mul_zero, ← c₁] at this
        rw [Fin.cons_zero, this]
        exact hzf
      · obtain ⟨l, hl⟩ := hc z ⟨hz, hzf⟩
        refine ⟨l.succ, ?_⟩
        have := (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e' 0 (x l) (hx l)).2.2.1 e he
        rw [mul_zero, ← c₂] at this
        rw [Fin.cons_succ, this]
        exact hl

theorem exists_gens (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsArithVar p D) (P : Pair p) (hP : IsAmpleLB P.L.B) :
    ∃ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x := by
  obtain ⟨e, x, he, hx, hc⟩ := exists_cover k X p D hX P hP (D + 1) Set.univ isClosed_univ fun ℓ => by
    rw [Set.univ_inter, Nat.cast_add_one]
    exact ENat.WithBot.lt_add_one_iff.2 ((GlobalTheory.T.projArith_residueCharFibre_structure k X p D hX).2.2.2.1 ℓ)
  exact ⟨e, x, he, hx, fun z => hc z trivial⟩

end GlobalTheory.HSAmp.NoethGens

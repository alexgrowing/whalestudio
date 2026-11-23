import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepSplitIntertwinerStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepJacquetWordMultiplicityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursProductInterleaveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityNonzeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwKerWhitCharReflect
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdMapInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentQuotientOfTwoSegment

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.BZSeg.TwoSegWhit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem arith {Δ Δ' : Segment k} (hpre : Δ'.Precedes Δ) :
    ∃ j : ℕ, 0 < j ∧ j ≤ Δ'.len ∧ Δ'.len < j + Δ.len ∧ Δ.first = Δ'.first.nu (j : ℂ) := by
  obtain ⟨⟨⟨Γ, hΓ⟩, -, h2⟩, j, hj, e⟩ := hpre
  have hc : 0 < Δ'.first.1 := Δ'.isCusp_first.1
  have inj : ∀ a b : ℕ, Δ'.first.nu (a : ℂ) = Δ'.first.nu (b : ℂ) → a = b :=
    fun a b h => (IrrGL.nu_natCast_inj hc).1 h
  have memΔ' : ∀ n : ℕ, Δ'.first.nu (n : ℂ) ∈ Δ'.carrier ↔ n < Δ'.len := fun n =>
    ⟨fun h => by
      obtain ⟨a, ha, h⟩ := Segment.mem_carrier.1 h
      rwa [← inj _ _ h], fun h => Segment.mem_carrier.2 ⟨n, h, rfl⟩⟩
  have memΔ : ∀ n : ℕ, Δ'.first.nu (n : ℂ) ∈ Δ.carrier ↔ j ≤ n ∧ n < j + Δ.len := fun n => by
    constructor
    · intro h
      obtain ⟨a, ha, h⟩ := Segment.mem_carrier.1 h
      rw [e, IrrGL.nu_nu] at h
      have h' := inj (j + a) n (by push_cast; exact h)
      omega
    · rintro ⟨h1, h3⟩
      refine Segment.mem_carrier.2 ⟨n - j, by omega, ?_⟩
      rw [e, IrrGL.nu_nu]
      congr 1
      rw [← Nat.cast_add]
      congr 1
      omega
  have hρ : Δ'.first ∈ Γ.carrier := by
    rw [hΓ]
    exact Or.inl (Segment.mem_carrier.2 ⟨0, Δ'.len_pos, by simp⟩)
  have hΓ0 : Γ.first ∈ Γ.carrier := Segment.mem_carrier.2 ⟨0, Γ.len_pos, by simp⟩
  have hcΓ : ∃ c : ℕ, Γ.first = Δ'.first.nu (c : ℂ) := by
    rw [hΓ] at hΓ0
    rcases hΓ0 with h | h
    · obtain ⟨a, -, h⟩ := Segment.mem_carrier.1 h
      exact ⟨a, h.symm⟩
    · obtain ⟨a, -, h⟩ := Segment.mem_carrier.1 h
      refine ⟨j + a, ?_⟩
      rw [← h, e, IrrGL.nu_nu]
      push_cast
      rfl
  obtain ⟨c, hcΓ⟩ := hcΓ
  have hΓf : Γ.first = Δ'.first := by
    obtain ⟨a, -, h⟩ := Segment.mem_carrier.1 hρ
    rw [hcΓ, IrrGL.nu_nu] at h
    have h' := inj (c + a) 0 (by push_cast; simpa using h)
    have hc0 : c = 0 := by omega
    rw [hcΓ, hc0]
    simp
  have memΓ : ∀ n : ℕ, Δ'.first.nu (n : ℂ) ∈ Γ.carrier ↔ n < Γ.len := fun n =>
    ⟨fun h => by
      obtain ⟨a, ha, h⟩ := Segment.mem_carrier.1 h
      rw [hΓf] at h
      rwa [← inj _ _ h], fun h => Segment.mem_carrier.2 ⟨n, h, by rw [hΓf]⟩⟩
  have key : ∀ n : ℕ, n < Γ.len ↔ n < Δ'.len ∨ (j ≤ n ∧ n < j + Δ.len) := fun n => by
    rw [← memΓ, hΓ, Set.mem_union, memΔ', memΔ]
  have hlp := Δ.len_pos
  refine ⟨j, hj, ?_, ?_, e⟩
  · by_contra hlt
    have h1 := (key (j + Δ.len - 1)).2 (Or.inr ⟨by omega, by omega⟩)
    have h3 := (key Δ'.len).1 (by omega)
    omega
  · by_contra hge
    refine h2 fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 hx
    rw [e, IrrGL.nu_nu]
    have h3 := (memΔ' (j + a)).2 (by omega)
    push_cast at h3
    exact h3

end GlobalTheory.CompanionTheory.BZSeg.TwoSegWhit

end

import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.TraceForm
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.NilCore
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.Imports

namespace PositivityTheory.RgUd.TP.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem traceForm : TraceForm k := Loc.Final.traceForm k
theorem unimod : TraceForm k → PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) := Loc.Final.unimod k
theorem desc (p : ℕ) [Fact p.Prime] [CharP k p] : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) → Desc k := PositivityTheory.RgUd.TP.Desc.Final.desc k p
theorem locOff : LocOff k := Loc.Final.locOff k
theorem locAll : LocAll k := Loc.Final.locAll k
theorem transl : Transl k := Loc.Final.transl k
theorem nilCore :
    TraceForm k → PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) → NilCore k := Nil.Final.nilCore k

theorem van_of (hD : Desc k) (h1 : LocOff k) (h2 : LocAll k) (h3 : Transl k) (h4 : NilCore k) :
    ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → Van Z := by
  obtain ⟨μ, hμ⟩ := hD
  suffices h : ∀ (m n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), μ n Z = m → CR Z → Van Z from
    fun n Z hZ => h _ n Z rfl hZ
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n Z hm hZ
    have hP : ∀ χ : Polynomial k, ∃ (r : ℕ) (F : Fin r → Set (Matrix (Fin n) (Fin n) k)), IsPieces Z χ F ∧ ∀ i,
        (∃ c ∈ Z, ∀ x ∈ F i, IsNilpotent (x - c)) ∨ FibVan Z (F i) := fun χ => by
      obtain ⟨r, F, hF, hi⟩ := hμ n Z hZ χ
      exact ⟨r, F, hF, fun i => (hi i).imp_right fun h => h fun n' Z' hZ' hlt => ih _ (hm ▸ hlt) n' Z' rfl hZ'⟩
    have hN := h4 n Z hZ (h1 n Z hZ hP)
    refine h2 n Z hZ fun χ => ?_
    obtain ⟨r, F, hF, hi⟩ := hP χ
    exact ⟨r, F, hF, fun i => (hi i).elim (fun ⟨c, hc, hx⟩ => h3 n Z hZ hN c hc _ (hF.1 i).2.1 hx) id⟩

theorem thmT (p : ℕ) [Fact p.Prime] [CharP k p] : PositivityTheory.RgUd.ThmT k := by
  intro n Z hcomm hred ξ hsupp hinv f hf
  have hU := unimod k (traceForm k)
  exact van_of k (desc k p hU) (locOff k) (locAll k) (transl k) (nilCore k (traceForm k) hU) n Z ⟨hcomm, hred⟩ ξ
    (fun g hg h0 => hsupp g hg fun p hp => h0 p ⟨hp, Set.mem_univ _⟩) (fun g hg f hf => hinv g hg f hf) f hf

end PositivityTheory.RgUd.TP.Final

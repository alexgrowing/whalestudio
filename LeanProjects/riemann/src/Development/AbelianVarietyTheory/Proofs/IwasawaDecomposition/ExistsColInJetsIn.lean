import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegreeEqTotDeg

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Col2

namespace JetEx

theorem hasLetters_of_over {K : Ctx} {P : Pre} (h : K.Over P) : StagesInhab.HasLetters P := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  have hx : 0 < K.s.x := zero_lt_one.trans K.s.one_lt_alt
  refine ⟨(Delv K.s K.cD : ℚ), K.c, Nat.cast_pos.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hx _)), K.ok.inj,
    fun w τ l hl => ?_, K.ok.code⟩
  have h1 := (K.ok.hc w).1 τ
  change l + 1 < K.P.R.k - 1 at hl
  show (K.P.hcW w τ).v ⟨l, by omega⟩ - (K.P.hcW w τ).v ⟨l + 1, hl⟩ = _
  rw [h1, h1, show K.P.R.k - 2 - l = K.P.R.k - 2 - (l + 1) + 1 by omega]
  push_cast
  ring

theorem lg_gens (K : Ctx) : large₂ K fun B f T => ∀ z ∈ gens B.toPre f.chiPsi (T.set f), z ∈ B.embLL.fieldRange :=
  ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun P f _ _ Ξ => gens P f.chiPsi Ξ, by simp,
    fun P f _ _ Ξ => gens_algebraic P f.chiPsi Ξ, fun _ _ _ _ h _ _ => h.2⟩

end JetEx

theorem exists_bound_jetsIn : ∃ Z : ∀ P : Pre, HChar P.host.E → Set (HChar P.host.E) → Finset ℂ,
    (∀ P χ Ξ, ∀ z ∈ Z P χ Ξ, IsAlgebraic ℚ z) ∧
    ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), StagesInhab.HasLetters B.toPre → I.Ok →
      (∀ z ∈ Z B.toPre I.C.chiPsi (Set.range I.xi), z ∈ B.embLL.fieldRange) →
      ∃ I' : ColIn B X, I'.Ok ∧ I'.JetsIn ∧ I'.C = I.C ∧ I'.S = I.S ∧ Set.range I'.xi = Set.range I.xi :=
  ⟨JetEx.gens, JetEx.gens_algebraic, fun _ _ _ hL h hK => JetEx.exists_jetsIn hL h hK⟩

end GlobalTheory.Mem.Col2

end

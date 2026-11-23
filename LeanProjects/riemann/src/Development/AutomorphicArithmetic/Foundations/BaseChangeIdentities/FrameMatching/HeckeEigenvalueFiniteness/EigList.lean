import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.EigFin

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

def dimI {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) : ℕ :=
  Module.finrank ℂ (fixed (pairAt Pa Pb w) (I2 a b w))

theorem eig_fin (hII : IsoInv) (hSPr : StrictProd) {E : Type} [Field E] [NumberField E] [IsCMField E] {a b kA kB : ℕ}
    (PA : Fin kA → Pre E a) (PB : Fin kB → Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) :
    ∃ (Z : Set ((Fin a → ℂˣ) × (Fin b → ℂˣ))) (m : ℕ), Z.Finite ∧ ∀ (Pa : Pre E a) (Pb : Pre E b),
      (∃ ja, Strict Pa (PA ja)) → (∃ jb, Strict Pb (PB jb)) →
      dimI Pa Pb w ≤ m ∧ ∀ ξa ξb, JEig Pa Pb w ϖ ξa ξb → (ξa, ξb) ∈ Z := by
  have h0 : ∀ x : Fin kA × Fin kB, ∃ (Z : Set ((Fin a → ℂˣ) × (Fin b → ℂˣ))) (m : ℕ), Z.Finite ∧ ∀ (Pa : Pre E a) (Pb : Pre E b),
      Strict Pa (PA x.1) → Strict Pb (PB x.2) → dimI Pa Pb w ≤ m ∧ ∀ ξa ξb, JEig Pa Pb w ϖ ξa ξb → (ξa, ξb) ∈ Z :=
    fun x => eig_one hII hSPr (PA x.1) (PB x.2) w ϖ
  choose Z mZ hZ using h0
  refine ⟨⋃ x, Z x, Finset.univ.sup mZ, Set.finite_iUnion fun x => (hZ x).1, ?_⟩
  rintro Pa Pb ⟨ja, ha⟩ ⟨jb, hb⟩
  have h := (hZ (ja, jb)).2 Pa Pb ha hb
  exact ⟨le_trans h.1 (Finset.le_sup (Finset.mem_univ (ja, jb))), fun ξa ξb hj => Set.mem_iUnion.2 ⟨(ja, jb), h.2 ξa ξb hj⟩⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end

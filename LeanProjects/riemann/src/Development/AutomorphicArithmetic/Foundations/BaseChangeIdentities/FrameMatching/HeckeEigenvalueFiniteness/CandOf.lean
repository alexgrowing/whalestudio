import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.Imports
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.ImportsAlt
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.ClsFin

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

theorem all_parts (hFS : FinStrict) (hSPr : StrictProd) (hSJ : StrictJoin) (hCP : CandParts) (hII : IsoInv) (hAd : AdmProd)
    {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (T' : Finset (Pl E))
    (hO : ∀ i : F₀.C.ι, IsOpen (lev₁ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (F₀.C.a i)) (Af E))) ∧
      IsOpen (lev₂ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (n - F₀.C.a i)) (Af E)))) :
    (∀ i w, ∃ Z : Set ((Fin (F₀.C.a i) → ℂˣ) × (Fin (n - F₀.C.a i) → ℂˣ)), Z.Finite ∧
      ∀ s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → w ∈ T' → ∀ ξa ξb, JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb → (ξa, ξb) ∈ Z) ∧
    (∀ w ∈ F₀.d₀.S₀, ∃ (k : ℕ) (Dl : Fin k → Pre E n), ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D →
      ∃ j, Same w (F₀.d₀.K' w) D (Dl j)) ∧
    ∃ m₀ : ℕ, ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → ∀ w ∈ T', dimI Pa Pb w ≤ m₀ := by
  choose kA kB PA PB hcls using fun i : F₀.C.ι => cls_fin hFS hCP F₀ d i (hO i).1 (hO i).2
  have h1 := part1 hII hSPr F₀ d kA kB PA PB hcls T'
  exact ⟨h1.1, part2 hSPr hSJ hII hAd F₀ d kA kB PA PB hcls, h1.2⟩

theorem candFin_of (hFS : FinStrict) (hSPr : StrictProd) (hSJ : StrictJoin) (hCP : CandParts)
    (hLO : LevOpen) (hII : IsoInv) (hAd : AdmProd) : CandFin := by
  intro hR E _ _ _ hU n hn π hπ S F₀ T' c e b hT'
  have hO := fun i : F₀.C.ι => hLO hR E n π S F₀ T' c e b (F₀.C.a i) (F₀.C.le i)
  exact all_parts hFS hSPr hSJ hCP hII hAd F₀ (F₀.loc T' c e b) T' hO

end UpperTheory.HeckeLevelFrameExistence.CF

end

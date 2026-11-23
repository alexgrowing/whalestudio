import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.StrictCommon

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

theorem joins_fin (hSJ : StrictJoin)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (μ : HChar E) {ι : Type} [Finite ι] (a : ι → ℕ) (kA kB : ι → ℕ)
    (PA : ∀ i, Fin (kA i) → Pre E (a i)) (PB : ∀ i, Fin (kB i) → Pre E (n - a i)) :
    ∃ (k : ℕ) (Dl : Fin k → Pre E n), ∀ i (Pa : Pre E (a i)) (Pb : Pre E (n - a i)) (D : Pre E n),
      IsJoin (μ ^ (n - a i)) (μ ^ a i) Pa Pb D → (∃ ja, Strict Pa (PA i ja)) → (∃ jb, Strict Pb (PB i jb)) →
      ∃ j, Strict D (Dl j) := by
  let J : Type := {x : Σ i, Fin (kA i) × Fin (kB i) // ∃ D : Pre E n, ∃ (Pa : Pre E (a x.1)) (Pb : Pre E (n - a x.1)),
    IsJoin (μ ^ (n - a x.1)) (μ ^ a x.1) Pa Pb D ∧ Strict Pa (PA x.1 x.2.1) ∧ Strict Pb (PB x.1 x.2.2)}
  haveI : Finite J := Subtype.finite
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  choose Df Paf Pbf hf using fun x : J => x.2
  refine ⟨k, fun j => Df (e.symm j), fun i Pa Pb D hj ⟨ja, ha⟩ ⟨jb, hb⟩ => ?_⟩
  let x : J := ⟨⟨i, ja, jb⟩, D, Pa, Pb, hj, ha, hb⟩
  refine ⟨e x, ?_⟩
  show Strict D (Df (e.symm (e x)))
  rw [e.symm_apply_apply]
  exact hSJ E n _ _ _ _ Pa (Paf x) Pb (Pbf x) D _ hj (hf x).1 (strict_common ha (hf x).2.1) (strict_common hb (hf x).2.2)

theorem same_of_strict (hSPr : StrictProd) (hII : IsoInv) (hAd : AdmProd)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E) (K : Subgroup (GLw n w))
    (ho : IsOpen (K : Set (GLw n w))) (hle : K ≤ GlobalTheory.LFun.KGL w n) (D D' : Pre E n) (hs : Strict D D') :
    (∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) ↔ GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D' w)) ∧
      Module.finrank ℂ ↥(fixed (prodAt D w) K) = Module.finrank ℂ ↥(fixed (prodAt D' w) K) ∧
      FiniteDimensional ℂ ↥(fixed (prodAt D' w) K) := by
  have h := hII (GLw n w) _ _ (prodAt D w) (prodAt D' w) (hSPr E n D D' hs w) K
  exact ⟨fun τ => h.1 τ.V τ.ρ, h.2.1, hAd E n D' w K ho hle⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end

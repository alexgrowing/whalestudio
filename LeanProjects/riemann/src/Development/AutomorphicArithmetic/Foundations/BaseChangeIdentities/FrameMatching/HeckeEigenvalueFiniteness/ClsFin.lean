import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.SameOfStrict

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

theorem rl_levels (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a)
    (Mb : Mods E b) (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (h1 : IsOpen (K₁ : Set (GL (Fin a) (Af E)))) (h2 : IsOpen (K₂ : Set (GL (Fin b) (Af E)))) :
    Levels E (rlΘ₁ hR E a b Ma Mb K₁ K₂) ∧ Levels E (rlΘ₂ hR E a b Ma Mb K₁ K₂) :=
  (hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1 a b Ma Mb K₁ K₂ h1 h2

theorem rl_ktypes (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a)
    (Mb : Mods E b) : KTypes E (rlΩ₁ hR E a b Ma Mb) ∧ KTypes E (rlΩ₂ hR E a b Ma Mb) :=
  ⟨((hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1 a b Ma Mb).2.2.1,
    ((hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1 a b Ma Mb).2.2.2.1⟩

theorem cls_fin (hFS : FinStrict) (hCP : CandParts)
    {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (i : F₀.C.ι)
    (h1 : IsOpen (lev₁ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (F₀.C.a i)) (Af E))))
    (h2 : IsOpen (lev₂ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (n - F₀.C.a i)) (Af E)))) :
    ∃ (kA kB : ℕ) (PA : Fin kA → Pre E (F₀.C.a i)) (PB : Fin kB → Pre E (n - F₀.C.a i)), ∀ s₁ s₂ Pa Pb D,
      F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA ja)) ∧ ∃ jb, Strict Pb (PB jb) := by
  have hL := rl_levels hR E _ _ (F₀.A i).Ma (F₀.A i).Mb _ _ h1 h2
  have hK := rl_ktypes hR E _ _ (F₀.A i).Ma (F₀.A i).Mb
  obtain ⟨kA, PA, hPA⟩ := hFS E _ _ _ hL.1 hK.1 (mOf (F₀.A i).χa)
  obtain ⟨kB, PB, hPB⟩ := hFS E _ _ _ hL.2 hK.2 (mOf (F₀.A i).χb)
  refine ⟨kA, kB, PA, PB, fun s₁ s₂ Pa Pb D hc => ?_⟩
  have hp := hCP hR E n π S F₀ d i s₁ s₂ Pa Pb D hc
  have hm := LemDd.cand_sum hc
  exact ⟨hPA Pa hp.1 hm.1, hPB Pb hp.2 hm.2⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end

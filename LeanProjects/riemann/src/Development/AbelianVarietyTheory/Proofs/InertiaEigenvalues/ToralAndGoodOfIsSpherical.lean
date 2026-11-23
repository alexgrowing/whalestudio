import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters

open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT

namespace GlobalTheory.SphSupport

theorem toral_of_isSpherical (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k)
    (hs : IsSpherical x.rep) :
    ∃ s, HasSupport x.rep s ∧ ∀ y ∈ s, ∃ (χ : kˣ →* ℂˣ) (hχ : IsUnram χ), y = IrrGL.ofChar χ
      (isSmoothChar_of_isUnram hχ) := by
  have hadm : IsAdmissible x.rep := (hBZ k).1 (Fin x.1) x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr
  have hI : fixed x.rep (iwahori k (Fin x.1)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm x.2.rep.irr hI
  have hχ : ∀ i, IsSmoothChar (unrChar k (α i)) := fun i =>
    isSmoothChar_of_isUnram (isUnram_unrChar k (α i))
  have H : IsCuspSupport x.rep (fun _ : Fin x.1 => 1) fun a => detRep (Fin 1) (unrChar k (α a)) :=
    ⟨x.2.rep.irr, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hχ a)⟩, _,
      hα.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k x.1 fun i => unrChar k (α i))⟩
  refine ⟨_, hasSupport_of_isCuspSupport H, ?_⟩
  intro y hy
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  exact ⟨unrChar k (α i), isUnram_unrChar k (α i), rfl⟩

theorem toral_and_good_of_isSpherical : GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k),
      IsSpherical x.rep → Toral x ∧ Good x := by
  intro hBZ k _ _ _ _ x hs
  obtain ⟨s, hsup, hs1⟩ := toral_of_isSpherical hBZ k x hs
  have h1 : ∀ y ∈ s, y.1 = 1 := fun y hy => by
    obtain ⟨χ, -, rfl⟩ := hs1 y hy
    rfl
  exact ⟨⟨s, hsup, h1⟩, ⟨s, hsup, fun y hy => Or.inl (h1 y hy)⟩⟩

end GlobalTheory.SphSupport

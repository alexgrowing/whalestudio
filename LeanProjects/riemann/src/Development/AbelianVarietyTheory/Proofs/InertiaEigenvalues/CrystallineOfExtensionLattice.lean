import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ExtLatCrys

theorem isCrys_comp_extRep {l : ℕ} [Fact l.Prime] {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] (K : FinExt l) (Pl : LocPrime l)
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL (Gl l) V)
    (hT : IsCrys (Pl.PD K) (ρ.comp (inclG K) : Representation LL ↥(GK K) V)) (z : ↥(continuousCocycles ρ))
    (hz : (z : Gl l → V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ) :
    IsCrys (Pl.PD K) ((GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep ρ z).comp (inclG K) : Representation LL ↥(GK K) (V × LL)) := by
  let ρ' : Representation LL ↥(GK K) V := ρ.comp (inclG K)
  have hρ' : ∀ g, ρ' g = ρ (inclG K g) := fun _ => rfl
  have hc : (fun g => (z : Gl l → V) (inclG K g)) ∈ continuousCocycles ρ' :=
    ⟨z.2.1.comp (continuous_subtype_val.subtype_mk _), fun g k => by
      have := z.2.2 (inclG K g) (inclG K k)
      rw [← map_mul] at this
      exact this⟩
  have h0 := GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep_isExt ρ' ⟨_, hc⟩
  have h2 : ∀ (g : ↥(GK K)) (y : V ⊗[ℚ_[l]] Pl.R.B), actVB (Pl.PD K) ρ' g y =
      actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ (inclG K g) y := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, Pl.PD_actB, hρ']; rfl
    | add u w hu hw => rw [map_add, map_add, hu, hw]
  have h1 := (GlobalTheory.CrysExt.isCrystalline_iff_mem_H1f (Pl.PD K) (ρ := ρ') hT h0.1 ⟨_, hc⟩ h0.2).mpr
    ((GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.mk_mem_H1fSub (Pl.PD K) ρ' ⟨_, hc⟩).mpr (by
      obtain ⟨-, x, hx⟩ := hz
      refine ⟨hc, x, fun g => ?_⟩
      rw [h2]
      exact hx (inclG K g)))
  exact h1

theorem isCrys_comp_extRep_lat {l : ℕ} [Fact l.Prime] {LL O : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (K : FinExt l) (Pl : LocPrime l)
    (T : LocLat (Gl l) ℚ_[l] LL O)
    (hT : IsCrys (Pl.PD K) (T.ρ.comp (inclG K) : Representation LL ↥(GK K) T.V)) (z : ↥(continuousCocycles T.ρ))
    (hz : (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ) :
    IsCrys (Pl.PD K) ((GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep T.ρ z).comp (inclG K) : Representation LL ↥(GK K) (T.V × LL)) :=
  isCrys_comp_extRep K Pl T.ρ hT z hz

theorem isCrys_resF_extLat : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (T : QLat LL), IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ → ∀ z : ↥(latticeCocycles T.L), (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ → IsCrys (Pl.PD (ϖ.field a)) (resF (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a)).ρ := by
  intro l _ a e _ _ ϖ LL _ _ Pl T hT z hz
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact isCrys_comp_extRep_lat (ϖ.field a) Pl T hT ⟨z, z.2.1⟩ hz

end GlobalTheory.ExtLatCrys

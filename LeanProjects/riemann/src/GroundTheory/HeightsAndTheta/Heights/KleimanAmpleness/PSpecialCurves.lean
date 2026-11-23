import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsModelWithBaseExOPnPt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailLast
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeBaseComap
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

theorem rename_mem_mIdealOver (S : Type) [CommRing S] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]
    [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {x : Fin (N + 1) → Ω}
    (hx : x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) {f : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) S}
    (hf : f ∈ mIdealOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) :
    rename (fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) f ∈ mIdealOver S y := by
  subst hx
  have hcomp : (mConeMapOver S y).comp
      (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) =
      ((rename (R := Ω) fun _ : Unit => k₀).restrictScalars S).comp
        (mConeMapOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  have hf' : mConeMapOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) f = 0 := hf
  have h1 := AlgHom.congr_fun hcomp f
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hf', map_zero] at h1
  exact h1

theorem specialIdeal_le_baseComap (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type}
    [DecidableEq K] {ι : K → Type} {Ω : Type}
    [Field Ω] [Algebra O Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    {x : Fin (N + 1) → Ω} (hx : x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)
    {W : Ideal (NumbersDVR.MRing ι (IsLocalRing.ResidueField O))}
    (hW : NumbersDVR.specialIdeal (mIdealOver O y) ≤ W) :
    NumbersDVR.specialIdeal (mIdealOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) ≤
      baseComap (IsLocalRing.ResidueField O) k₀ e W := by
  rw [NumbersDVR.specialIdeal, Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap, baseComap, Ideal.mem_comap, ← map_rename]
  exact hW (Ideal.mem_map_of_mem _ (rename_mem_mIdealOver O y k₀ e hx hf))

theorem SpecialCurves.proof (hdim : SpecialCurvesDim.Statement) (hlift : SpecialCurvesLift.Statement) :
    SpecialCurves.Statement := by
  intro O _ _ _ K _ _ ι _ Ω _ _ _ _ y k₀ N e x hx hy d
  refine ⟨fun W hW hyW hd => ⟨isMultiProjPrime_baseComap _ k₀ e hW,
    specialIdeal_le_baseComap O y k₀ e hx hyW, ?_⟩, fun P hP hxP hd => ?_⟩
  · rw [hdim O K ι Ω y k₀ N e hy W hW hyW, hd]
  · obtain ⟨W, hW, hyW, rfl⟩ := hlift O K ι Ω y k₀ N e x hx hy P hP hxP
    exact ⟨W, hW, hyW, by rw [← hdim O K ι Ω y k₀ N e hy W hW hyW, hd], rfl⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

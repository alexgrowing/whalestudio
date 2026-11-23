import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemThPsiOfMemSpan
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlNeOfSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ResTwist

theorem res_twist_spec : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) →
    ∀ (PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) (x : (kP PP.1)ˣ),
      (((ρ.tw i b k Q (χ.comp (Y.delU i Q M))).resC PP.1 x : ℂˣ) : ℂ) =
        ρ.eOk i b k ((χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i)
          (Pi.single PP (Multiplicative.toAdd ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1 x))))) : (X.Ok i k)ˣ) : X.Ok i k) := by
  intro D N X ρ hρ Y hY i b k Q M χ hT PP x
  let χc : Multiplicative (↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) →* Circle :=
    unitPart.comp ((Units.map (ρ.eOk i b k).toMonoidHom).comp (χ.comp (AddMonoidHom.toMultiplicative (spread Y i Q M (ρ.ch i)))))
  have hgood := GlobalTheory.UnivGood.univOf_good D N X ρ hρ Y i Q M

  have hchar : charOf ρ.rc (ρ.eOk i b k) (χ.comp (Y.delU i Q M)) = χc.comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) := by
    ext1 y
    obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym y
    have hψ : IsOpen ((χ.comp (Y.delU i Q M)).ker : Set (G D.host.E N.Om)) :=
      Subgroup.isOpen_mono (H₁ := (Y.delU i Q M).ker) (fun g hg => by simp [MonoidHom.mem_ker.1 hg]) (Y.delU_open i Q M)
    have hco : ∀ P : Pl D.host.E, IsOpen ((coord Y i (admissibleConjugatePairPlaces X i Q M) M P).ker : Set (G D.host.E N.Om)) := by
      intro P
      by_cases hP : P ∈ admissibleConjugatePairPlaces X i Q M
      · refine Subgroup.isOpen_mono (H₁ := (Y.delU i (admissibleConjugatePairPlaces X i Q M) M).ker) (fun g hg => ?_) (Y.delU_open i (admissibleConjugatePairPlaces X i Q M) M)
        refine MonoidHom.mem_ker.2 (Multiplicative.toAdd.injective ?_)
        rw [coord_apply Y i (admissibleConjugatePairPlaces X i Q M) M hP, MonoidHom.mem_ker.1 hg]
        rfl
      · rw [coord, dif_neg hP]
        simp
    have e1 : (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) y = Multiplicative.ofAdd fun P : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ) := by
      change Multiplicative.ofAdd (fun PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => Multiplicative.toAdd (ρ.rc.pull (coord Y i (admissibleConjugatePairPlaces X i Q M) M PP.1) y)) = _
      congr 1
      funext P
      exact congrArg Multiplicative.toAdd (ρ.rc.pull_eq (hco P.1) hσ)
    have e2 : Y.delU i Q M σ = AddMonoidHom.toMultiplicative (spread Y i Q M (ρ.ch i))
        (Multiplicative.ofAdd fun P : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ)) :=
      Multiplicative.toAdd.injective (delU_eq_spread hY (twSet_of_twOK hT) (hρ.ch i) σ)
    simp only [charOf, MonoidHom.comp_apply]
    rw [ρ.rc.pull_eq hψ hσ, e1, MonoidHom.comp_apply, e2]
    rfl
  have hspec := GlobalTheory.ExportSeries.SpecGood.spec_good D (ZMod (X.l i ^ M)) Circle (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc hgood
  have hres : IsResAt (χc.comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)))) PP.1 (((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).spec (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc).res PP.1) := hspec.res PP.1 PP.2
  have hidem := hgood.1.isIdemAt PP.2
  have htres : (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).res PP.1 = ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).spec (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc).res PP.1 := by
    change resOf (charOf ρ.rc (ρ.eOk i b k) (χ.comp (Y.delU i Q M))) PP.1 = _
    rw [hchar]
    exact GlobalTheory.ConjTwist.isResAt_unique hidem (isResAt_resOf ⟨_, hres⟩) hres
  have hs : ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).spec (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc).res PP.1 = χc.comp ((AddMonoidHom.toMultiplicative
      (AddMonoidHom.single (fun _ : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => ZMod (X.l i ^ M)) ⟨PP.1, PP.2⟩)).comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1)) := dif_pos PP.2
  have hz : ∀ z : Multiplicative (DelQM D.host (X.l i) Q M), z ^ (X.l i ^ M) = 1 := by
    intro z
    rw [← ofAdd_toAdd z, ← ofAdd_nsmul]
    refine congrArg Multiplicative.ofAdd (funext fun v => ?_)
    simp [nsmul_eq_mul, ZMod.natCast_self]
  change (((ρ.tw i b k Q (χ.comp (Y.delU i Q M))).res PP.1 x : Circle) : ℂ) = _
  rw [htres, hs]
  simp only [χc, MonoidHom.comp_apply]
  rw [unitPart_of_pow (n := X.l i ^ M) (pow_ne_zero _ (X.lPrime i).out.ne_zero)
    (by rw [← map_pow, ← map_pow, hz, map_one, map_one])]
  rfl

end GlobalTheory.ResTwist

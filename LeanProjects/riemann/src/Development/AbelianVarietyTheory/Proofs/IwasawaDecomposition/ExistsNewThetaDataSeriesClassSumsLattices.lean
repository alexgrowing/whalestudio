import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSetupPinnedCh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadingRealSide
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTieWithSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MtLatFgOfReps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotDvdDiscrIffRamificationIdx
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondStepHeckeOperatorsNormalisedSumsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteHomEqOfFramesKeepMatricesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.HeightCounting.SerCopy

theorem ncard_eq_of_splits {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = p) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  refine GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq E p hp fun P hP hpP => ?_
  have := hP.isPrime
  refine ⟨h ⟨P, hP.isPrime, fun h0 => ?_⟩ hpP, GlobalTheory.Mem.RaySplit.not_mem_sq hp hpP
    ((GlobalTheory.Mem.RaySplit.not_dvd_discr_iff_ramificationIdx E hp).1 hd P hP.isPrime hpP)⟩
  rw [h0] at hpP
  exact hp.ne_zero (by simpa using hpP)

theorem exists_preTie : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0) (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Rw : RowSide D) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) hL eig θ (Bs : SideB D R.C Rw (lowAll D) Pq (ratDatR R cG kKs hk) hL eig θ) (Sb : Finset (PlE D.host)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → (∀ j, FWT.IsChosenExtremalVector R.toRealDat j (sg0 D A3.A) (v₀ j _)) → (∀ j : Fin D.R.m, (R.FW j).IsKsForm) → GlobalTheory.HeightCounting.SerCopy.HkAd R Sb hL → (∀ i, Sb ⊆ D.ntw.S0 i) → TauTrue Bs.exp → CharSide D R.C → ValLL0 D R.C → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → (∀ v, NG.OverPl (Pq v) v) → IsChoice (D := D) (Set.range Pq) → (∀ t, ∀ P ∈ R.Q t, P ∈ Set.range Pq) → (∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok) → (∀ j, FWT.VStd D j) → Nonempty (GlobalTheory.HeightCounting.SerCopy.PreTie (GlobalTheory.HeightCounting.SerCopy.ysOf Bs) v₀ Bs.exp hF Pq) := by
  intro hA D Γ _ _ Pl0 I0 T A3 Ks _ _ _ R F cG kKs hk Rw Pq hL eig θ Bs Sb v₀ hF pins intersectionNumber_baseChange hv hK hH hSb hτ cs hV hsp hPq hch hQ
    ⟨Z, hZ⟩ hstd
  have hC : R.Char3 F := RealDat3.characterisation_of_weak pins.char intersectionNumber_baseChange.aux.ex
  obtain ⟨p1, -, d1, n1⟩ := hZ.places.splits D.host.pde (by simp)
  obtain ⟨p2, -, d2, n2⟩ := hZ.places.splits D.host.pde' (by simp)
  have hq : ∀ p : ℕ, ¬ (p : ℤ) ∣ discr D.host.E → p ≠ D.host.q := fun p h e =>
    h (Int.natCast_dvd.2 (e ▸ SetupPin.q_dvd_discr D))
  have h2 : 2 ∈ lowAll D := by simp [lowAll, lowPr]
  have hd : (discr D.host.E).natAbs.primeFactors ⊆ lowAll D := fun p hp =>
    Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hp)))
  have hc : (Ideal.absNorm D.host.ccK).primeFactors ⊆ lowAll D := fun p hp =>
    Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hp)))
  obtain ⟨ρ, hρ, hp, hlv, hρch, hbad⟩ := GlobalTheory.SeriesTie.ComplexCh.exists_setup_ch R cG F hC GlobalTheory.weilRepresentationUnitaryPair
    (SetupPin.goodSetup_badPlaces_conj _ Bs.tw) (SetupPin.goodSetup_placesOverTwo_subset _ Bs.tw h2) (SetupPin.goodSetup_count_eq_zero_off_badPlaces _ Bs.tw h2 hd hc)
    (SetupPin.exists_art_gal hA _ Bs.deltaRead) (SetupPin.mk_frac_Ok Bs.twF)
    ⟨ncard_eq_of_splits p1 d1 n1, ncard_eq_of_splits p2 d2 n2⟩ ⟨hq _ d1, hq _ d2⟩ (fun _ => Set.range Pq) (fun _ => hch)
    (fun i P ⟨t, h1, _⟩ => hQ t P h1)
  have hch' : ∀ i P, IsSplitPl D.host P → (P ∈ ρ.ch i ↔ P ∈ Set.range Pq) := fun i P _ => by rw [hρch]
  choose ν hν using fun i j b => exists_isScalar (ysOf Bs) v₀ hρ i j b
  have hFa : ∀ i j b, Faithful (realRd (ysOf Bs) v₀ hρ i j b (ν i j b)) := fun i j b =>
    GlobalTheory.SeriesTie.realRd_faithful D _ _ _ _ _ _ R cG _ (ysOf Bs) v₀ ρ hρ i j b _ (hν i j b).ne intersectionNumber_baseChange.prim.unif hC.models.HW
      (hv j) (hK (idxOf D ((j : ℕ) + 1)))
  choose PV₀ hPV₀ _ using fun j => GlobalTheory.MtRead.exists_idFrame D hF j (hstd j)
  obtain ⟨rdV, hon, hjoin⟩ := GlobalTheory.MtRead.exists_reading hA D R.C Rw (lowAll D) Pq _ hL eig θ Bs hτ cs hV hsp hPq Γ Pl0 I0 T A3 Ks R F
    cG hC.lev rfl pins.keep hF PV₀ hPV₀ ρ hρ hp hlv hch'
  obtain ⟨Dat, th, lev, thPsi, h1, thU, thP, MtLat, g2, g3, -, t, ht⟩ := GlobalTheory.SeriesInstall.exists_tie_withSeries D ρ hρ
    (fun i j b => realRd (ysOf Bs) v₀ hρ i j b (ν i j b)) hFa hlv (GlobalTheory.SeriesTie.latFG_of_good D _ _ ρ hρ) rdV hon
  refine ⟨{
    Dat := Dat, th := th, lev := lev, thPsi := thPsi, h1 := h1, thU := thU, thP := thP, MtLat := MtLat, h2 := g2, h3 := g3
    ρ := ρ, good := hρ, pin := hp, vec := hv, ν := ν, scalar := hν, tie := t
    hecke := fun i j b => (heckeRead_iff_tie.1 (GlobalTheory.T.secondStep_heckeOperators_normalisedSums D Γ Pl0 I0 T A3 Ks R cG kKs hk R.C Rw (lowAll D) Pq hL eig θ Bs Sb v₀
      ρ hρ hp hC.lev hC.allPl hH hSb i j b (ν i j b))).1
    bad := hbad, ch := hch'
    join := fun PV hPV i j b k Q ψ hAd hT => ?_ }⟩
  obtain ⟨ω, hω, he⟩ := hjoin i j b k Q ψ hAd hT
  refine ⟨ω, hω, fun f g => ?_⟩
  rw [← he f g, GlobalTheory.T.finiteHom_eq_of_frames_keep_matrices D _ _ hF (PV j) (PV₀ j) (hPV j) (hPV₀ j) g]
  exact congrFun (congrArg (fun r => r k Q ψ f) (ht i j b)) _

end GlobalTheory.HeightCounting.SerCopy

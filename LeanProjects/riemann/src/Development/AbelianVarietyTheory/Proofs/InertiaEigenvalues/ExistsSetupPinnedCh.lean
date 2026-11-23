import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodSetupCountEqZeroOffBadPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSetup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeriesTie.ComplexCh

variable {D : D7}

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open GlobalTheory.SeriesTie.Complex (eGc levOf castG levOf_mem levOf_chi)

theorem exists_setup_ch (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (F3 : Face3 D A3) (hC : Rl.Char3 F3)
    (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair)
    (hS0c : ∀ i, ∀ P ∈ D.ntw.S0 i, ∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∈ D.ntw.S0 i)
    (hS02 : ∀ i, placesOver D.host.E 2 ⊆ ↑(D.ntw.S0 i))
    (hS0A : ∀ i P, P ∉ D.ntw.S0 i → FractionalIdeal.count D.host.E P D.host.AA = 0)
    (hδ : ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧ ∀ i b,
      ∃ (κ : FractionRing (D.ntw.O0 i) →+* Qbar (D.ntw.l i)) (ι : Qbar (D.ntw.l i) ≃+* ℂ),
        (∀ x, ι (κ ((if b then D.ntw.emb0 i else D.ntw.emb0b i) x)) = embLL0 D x) ∧
        GlobalTheory.GalChar.IsGal art κ ι (Rl.C.delAt (D.ntw.l i)) (fun _ => 0) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)))
    (hcard : ∀ i k, Cardinal.mk (FractionRing (D.ntw.Ok i k)) ≤ Cardinal.continuum)
    (hspl : (Ideal.primesOver (Ideal.span {(D.host.pde : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E ∧
      (Ideal.primesOver (Ideal.span {(D.host.pde' : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E)
    (hq : D.host.pde ≠ D.host.q ∧ D.host.pde' ≠ D.host.q)
    (ch : D.ntw.Tw → Set (PlE D.host)) (hch1 : ∀ i, IsChoice (D := D) (ch i))
    (hch2 : ∀ i, {P : Pl D.host.E | ∃ t, P ∈ Rl.Q t ∧ P ∈ D.ntw.pD i} ⊆ ch i) :
    ∃ ρ : Setup D.ntw, ρ.Good ∧ RealPin Rl cG ρ ∧ ρ.LevelOf D.nexp ∧ ρ.ch = ch ∧
      ∀ i, ρ.bad i = GlobalTheory.SeriesTie.normProd (D.ntw.S0 i) := by
  classical
  obtain ⟨art, hart, hδ⟩ := hδ
  choose κ ι hκι hG using hδ
  obtain ⟨κA, hκ1, hκ2, hκ3⟩ := GlobalTheory.CharTransport.exists_hom D
  let rc : Recip D D.nd.Om := ⟨κA, art⟩
  have hrc : rc.Good := ⟨hκ1, hκ2, hκ3, hart⟩
  obtain ⟨e, ek, he1, he2, he3⟩ := GlobalTheory.T.exists_ladicCoefficientField_embeddings_complex D D.nd D.ntw (fun i b => (ι i b).toRingHom.comp (κ i b)) hκι hcard
  choose F hF hFstd hFψ hFθ hFsT hFBS hFBT hFΛS hFΛT hFβS hFβT hFf hFlS hFlT using GlobalTheory.T.exists_good_frame_realisation D Γ Pl0 I0 T A3 Ks Rl F3 hC
  let f : ∀ i, Bool → (D.ntw.O0 i →+* ℂ) := fun i b =>
    ((e i b).comp (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)))).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))
  have hfi : ∀ i b, Function.Injective (f i b) := fun i b =>
    ((e i b).injective.comp (IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i)))).comp (D.ntw.O_inj i)
  let de : D.ntw.Tw → Bool → Twist D Circle := fun i b =>
    twistOf rc (f i b) (ch i) (D.ntw.pD i) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))
  have hde : ∀ i b, (de i b).Good := fun i b => GlobalTheory.T.artin_twisting_character_delta_good D rc hrc i (ch i) (hch1 i) (f i b) (hfi i b) b
  have hpl : ∀ i b, PlacesOK Rl.Pg (de i b).Q := fun i _ =>
    GlobalTheory.T.typePlaces_twistPlaces_goodPosition D Γ Pl0 I0 T A3 Ks Rl A3.A.μ0 hC.lev hspl hq i (ch i) (hch1 i)
  have hB := fun i j b => GlobalTheory.T.liftBaseData_isGood_twist D Γ Pl0 I0 T A3 Ks Rl F3 hC j (F j) (hF j) (de i b) (hde i b) (hpl i b)
  choose w mu hwp hwm hBg using hB
  let P : D.ntw.Tw → ∀ j : Fin D.R.m, Bool → LevelP Rl.Pg (Wc D j).rank ℂ := fun i j b =>
    ⟨(levOf (eGc Rl cG j) D.nexp.U ((Units.map (e i b).toMonoidHom).comp (D.nexp.psiU i b))).1,
      (levOf (eGc Rl cG j) D.nexp.U ((Units.map (e i b).toMonoidHom).comp (D.nexp.psiU i b))).2⟩
  let B : D.ntw.Tw → ∀ j : Fin D.R.m, Bool → Base (Vc D j) (Wc D j) := fun i j b =>
    ⟨(hF j).rank_le, F j, ⟨Rl.Pg, P i j b, mu i j b⟩, de i b, w i j b, Rl.mu0 ((j : ℕ) + 1), Rl.eta⟩
  have hBG : ∀ i j b, (B i j b).Good := fun i j b => hBg i j b (P i j b)
  have hom : ∀ i j b (χ : (AE D)ˣ →* Circle), ∃ ω : PairRep (Vc D j) (Wc D j),
      ∀ t : Twist D Circle, t.Good → t.chi = χ → (B i j b).IsWeil χ ω := by
    intro i j b χ
    by_cases h : ∃ t : Twist D Circle, t.Good ∧ t.chi = χ
    · obtain ⟨t, ht, rfl⟩ := h
      obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_weilRep_good_twist D _ _ (B i j b) hW (hBG i j b) (hFstd j) t ht
      exact ⟨ω, fun _ _ _ => hω⟩
    · exact ⟨1, fun t ht h' => absurd ⟨t, ht, h'⟩ h⟩
  choose om hom using hom
  have hcl : ∀ i j b (t : Twist D Circle), ∃ (m : ℕ) (h : Fin m → GA D (Vc D j)),
      IsClassSystem (Vc D j) ((B i j b).levJ t) h := fun i j b t =>
    exists_isClassSystem (B i j b) (hBG i j b).frame t
  choose m rep hrep using hcl
  let ρ : Setup D.ntw :=
    { rc := rc
      ch := ch
      bad := fun i => ∏ P ∈ D.ntw.S0 i, Ideal.absNorm P.asIdeal
      e := e
      ek := ek
      B := B
      om := om
      Cl := fun i j b t => Fin (m i j b t)
      rep := rep
      β := fun j P => DetBases.std _ _ _
      eG := fun _ j _ => eGc Rl cG j }
  refine ⟨ρ, ?_, ?_, ?_, rfl, fun _ => rfl⟩
  · exact
      { rc := hrc
        ch := hch1
        bad_ne := fun i => Finset.prod_ne_zero_iff.2 fun P _ h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
        goodSetup_bad_mem_badPlaces := fun i P hP => by
          obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun Q : Pl D.host.E => Ideal.absNorm Q.asIdeal) hP
          change ((∏ P ∈ D.ntw.S0 i, Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
          rw [hc, Nat.cast_mul]
          exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
        goodSetup_badPlaces_conj := hS0c
        goodSetup_placesOverTwo_subset := hS02
        goodSetup_count_eq_zero_off_badPlaces := hS0A
        e_LL0 := he1
        ek_e := fun i b k x => he2 i b k x
        base := hBG
        latS := fun _ j _ => hFlS j
        latT := fun _ j _ => hFlT j
        Pg := fun _ _ _ P hP => GlobalTheory.T.typePlaces_mem_placesOver_generators D Γ Pl0 I0 T A3 Ks Rl F3 hC P hP
        delta := fun _ _ _ => rfl
        weil := fun i j b t ht => hom i j b t.chi t ht rfl
        classes := fun i j b t _ _ => hrep i j b t }
  · exact
      { psi := fun _ j _ => hFψ j
        inf := fun _ j _ => hFθ j
        cartT := fun _ j _ => hFsT j
        onbS := fun _ j _ τ => hFBS j τ
        onbT := fun _ j _ => hFBT j
        latS := fun _ j _ => hFΛS j
        latT := fun _ j _ => hFΛT j
        frS := fun _ j _ => hFβS j
        frT := fun _ j _ => hFβT j
        vac := fun _ j _ => hFf j
        Pg := fun _ _ _ => rfl
        grp := fun _ j _ g P h h' a c => rfl
        mu0 := fun _ _ _ => rfl
        eta := fun _ _ _ => rfl
        delta := fun i j b => by
          exact GlobalTheory.T.twistingCharacter_ladicGaloisCharacter_eq_hecke D rc i (κ i b) (ι i b) (Rl.C.delAt (D.ntw.l i)) (D.ntw.delta i) b hrc (D.ntw.delta_open i) (hG i b)
            (f i b) (fun y hy => he3 i b y hy) (ch i) (D.ntw.pD i)
        deltaPl := fun i t P hP hPD => hch2 i ⟨t, hP, hPD⟩
        ap := fun i j b τ => hwp i j b τ
        am := fun i j b τ => hwm i j b τ }
  · exact
      { U_eq := fun i j b g => levOf_mem (eGc Rl cG j) D.nexp.U ((Units.map (e i b).toMonoidHom).comp (D.nexp.psiU i b)) g
        psiU_eq := fun i j b u hu => congrArg Units.val
          (levOf_chi (eGc Rl cG j) D.nexp.U ((Units.map (e i b).toMonoidHom).comp (D.nexp.psiU i b)) u hu) }

end GlobalTheory.SeriesTie.ComplexCh

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs.SetupPinCh

end GlobalTheory.TwInputs.SetupPinCh

end

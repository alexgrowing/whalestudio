import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellQPlacesOfAdmissibleTwistStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
namespace GlobalTheory.TameUnitOne
open Formalism.L2.NX
end GlobalTheory.TameUnitOne
namespace GlobalTheory.LevCmp
theorem tame_value_eq_one_at_wild_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ∀ u : 𝓞 (Dof x).host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ψ P'' l.b.Bs.exp.sgnT u = 1) ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ∀ u : 𝓞 (Dof x).host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ((Dof x).ntw.delta i) P'' (if b then l.b.Bs.exp.sgnT else -l.b.Bs.exp.sgnT) u = 1) := by
  intro _ hL
  refine StepW.of_all fun _ B _ T _ _ _ _ P x l v i b ψ hA j _ _ _ => ?_
  refine ⟨fun P'' hP'' u hu => ?_, fun P'' hP'' u hu => ?_⟩
  · have hQ : P'' ∈ QOf P v := (cell (D := Dof x) l.b.Bs.exp b hA j).QP_sub hP''
    exact GlobalTheory.TameUnitOne.tameVal_eq_one ψ P'' _ ((Dof x).ntw.l i) hA.2.2.1 (hA.1 P'' hQ).2
      (fun _ _ σ _ => hA.2.2.2.2.1 σ) u hu
  · have hD : P'' ∈ (Dof x).ntw.pD i := (cell (D := Dof x) l.b.Bs.exp b hA j).DP_sub hP''
    refine GlobalTheory.TameUnitOne.tameVal_eq_one ((Dof x).ntw.delta i) P'' _ 15 ((Dof x).ntw.delta_open i) ?_
      (fun A hA' σ hσ => ⟨1, ?_⟩) u hu
    · intro h
      have h1 := (Dof x).ntw.delta_tame i P'' hD
      have h2 : Ideal.absNorm P''.asIdeal ∣ 15 ^ Module.finrank ℤ (𝓞 (Dof x).host.E) := by
        have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
        rwa [Ideal.absNorm_span_natCast] at this
      have h3 : Nat.Coprime (Ideal.absNorm P''.asIdeal) 15 := by
        rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h1]
        rfl
      have h4 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right _ h3) h2
      exact P''.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h4)
    · have h1 := pow_card_eq_one' (x := (⟨(Dof x).ntw.delta i σ, σ, hσ, rfl⟩ :
        (ReciprocityTheory.Gal.Ine (F := (Dof x).host.E) A).map ((Dof x).ntw.delta i)))
      rw [(Dof x).ntw.delta_15 i P'' hD A hA'] at h1
      rw [pow_one]
      exact congrArg Subtype.val h1
end GlobalTheory.LevCmp
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tw_ok_value_trivial_at_twisted_place : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ∀ u : 𝓞 (Dof x).host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ψ P'' l.b.Bs.exp.sgnT u = 1) ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ∀ u : 𝓞 (Dof x).host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ((Dof x).ntw.delta i) P'' (if b then l.b.Bs.exp.sgnT else -l.b.Bs.exp.sgnT) u = 1) := by
  first | exact @_root_.GlobalTheory.LevCmp.tame_value_eq_one_at_wild_place_alt | exact _root_.GlobalTheory.LevCmp.tame_value_eq_one_at_wild_place_alt | (intros; apply _root_.GlobalTheory.LevCmp.tame_value_eq_one_at_wild_place_alt <;> assumption)
end
end

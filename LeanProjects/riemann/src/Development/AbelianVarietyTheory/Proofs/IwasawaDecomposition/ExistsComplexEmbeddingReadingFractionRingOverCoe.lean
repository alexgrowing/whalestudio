import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosedContinuumRingEquivComplexExtending
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardPadicAlgClPadicComplexEqComplex

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ReadingEmb

theorem exists_ringHom_complex_extending (A : Type) [Field A] (hA : Cardinal.mk A ≤ Cardinal.continuum)
    (K : Type) [Field K] [NumberField K] (i : K →+* A) (s : K →+* ℂ) :
    ∃ ι : A →+* ℂ, ∀ x, ι (i x) = s x := by
  haveI : CharZero A := (RingHom.charZero_iff i.injective).1 inferInstance
  let B := FractionRing (MvPolynomial ℝ A)
  have hB : Cardinal.mk B = Cardinal.continuum := by
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hA,
      max_eq_left Cardinal.aleph0_le_continuum]
  let C := AlgebraicClosure B
  have hC : Cardinal.mk C = Cardinal.continuum := by
    refine le_antisymm ((Algebra.IsAlgebraic.cardinalMk_le_max B C).trans
      (max_le hB.le Cardinal.aleph0_le_continuum)) ?_
    rw [← hB]
    exact Cardinal.mk_le_of_injective (algebraMap B C).injective
  let j : A →+* C := (algebraMap B C).comp ((algebraMap (MvPolynomial ℝ A) B).comp MvPolynomial.C)
  haveI : CharZero C := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e, he⟩ := GlobalTheory.algClosed_continuum_ringEquiv_complex_extending C hC K (j.comp i) s
  exact ⟨e.toRingHom.comp j, fun x => he x⟩

theorem mk_le_of_finite (R S : Type) [CommRing R] [AddCommGroup S] [Module R S] [Module.Finite R S]
    (h : Cardinal.mk R ≤ Cardinal.continuum) : Cardinal.mk S ≤ Cardinal.continuum := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R S
  refine (Cardinal.mk_le_of_surjective hf).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_fin]
  calc Cardinal.mk R ^ (n : Cardinal) ≤ Cardinal.continuum ^ (n : Cardinal) := Cardinal.power_le_power_right h
    _ ≤ Cardinal.continuum ^ Cardinal.aleph0 :=
        Cardinal.power_le_power_left Cardinal.continuum_ne_zero (Cardinal.natCast_le_aleph0)
    _ = Cardinal.continuum := Cardinal.continuum_power_aleph0

theorem exists_complex_emb : ∀ (D : D7) (F : TwFrameC D) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), ∃ ι : FractionRing ρ.Oe →+* ℂ, ∀ x, ι (ρ.emb x) = D.what₂.embLL x := by
  intro D F i k b v ρ
  haveI := D.ntw.lPrime i
  have h1 : Cardinal.mk (D.ntw.Ok i k) ≤ Cardinal.continuum := by
    have hinj : Function.Injective (fun x : D.ntw.Ok i k => ((F.eOk i k x : _) : ℂ_[D.ntw.l i])) :=
      Subtype.val_injective.comp (F.eOk i k).injective
    refine (Cardinal.mk_le_of_injective hinj).trans ?_
    rw [(GlobalTheory.PadicCard.card_padicAlgCl_padicComplex (D.ntw.l i)).2, Cardinal.mk_complex]
  haveI := ρ.fin
  have h2 : Cardinal.mk ρ.Oe ≤ Cardinal.continuum := mk_le_of_finite (D.ntw.Ok i k) ρ.Oe h1
  exact exists_ringHom_complex_extending (FractionRing ρ.Oe) (by rw [Cardinal.mk_fractionRing]; exact h2)
    D.what₂.LL ρ.emb D.what₂.embLL

end GlobalTheory.ReadingEmb

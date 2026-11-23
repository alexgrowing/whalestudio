import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsModelHolomorphicIntegralExtremalWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiOfOverK
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OneLeAPlLast

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem isEnum_unique {n : ℕ} {S : SPar} {lam lam' : Fin n → ℝ} {ε ε' : Fin n → Bool}
    (h : IsEnum S lam ε) (h' : IsEnum S lam' ε') : lam = lam' ∧ ε = ε' := by
  obtain ⟨hA, q, hq, hS⟩ := h
  obtain ⟨hA', q', hq', hS'⟩ := h'
  have hqA : StrictAnti q := fun a b hab => by
    have := hA hab; rw [hq, hq] at this; exact_mod_cast this
  have hqA' : StrictAnti q' := fun a b hab => by
    have := hA' hab; rw [hq', hq'] at this; exact_mod_cast this
  have himg : Finset.univ.image q = Finset.univ.image q' := by
    have e := congrArg (Finset.image Prod.fst) (hS.symm.trans hS')
    simpa [Finset.image_image, Function.comp_def] using e
  have hr : Set.range q = Set.range q' := by
    have := congrArg (fun s : Finset ℚ => (s : Set ℚ)) himg
    simpa [Finset.coe_image] using this
  have hqq : q = q' := (StrictAnti.range_inj hqA hqA').1 hr
  subst hqq
  refine ⟨funext fun a => by rw [hq, hq'], funext fun a => ?_⟩
  have hm : (q a, ε a) ∈ S := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
  rw [hS'] at hm
  obtain ⟨b, -, hb⟩ := Finset.mem_image.1 hm
  have hb1 : b = a := hqA.injective (congrArg Prod.fst hb)
  subst hb1
  exact (congrArg Prod.snd hb).symm

theorem parAt_overK {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ) (ρ : D.what₂.Tau) :
    parAt (Wc D i) σ ρ = parAt (Wc D i) (sg0 D A) (lab σ ρ) := by
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hsig : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) :=
    fun τ => D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have hl := ((GlobalTheory.GalLift.labels_overK σ).1 hK).2 ρ
  unfold parAt kapAt
  rw [if_pos hl, hs, GlobalTheory.ThetaFiresProbe.lab_fixed, if_pos (GlobalTheory.ThetaFiresProbe.labE_fixed _), hsig ρ, hsig (lab σ ρ)]

theorem model_overK {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ) (ρ : D.what₂.Tau) :
    (R.MW i σ).lam ρ = (R.MW i (sg0 D A)).lam (lab σ ρ) ∧ (R.MW i σ).ε ρ = (R.MW i (sg0 D A)).ε (lab σ ρ) := by
  have h1 := (R.MW i σ).enum ρ
  rw [parAt_overK R i σ hK ρ] at h1
  exact isEnum_unique h1 ((R.MW i (sg0 D A)).enum (lab σ ρ))

theorem holShape_overK : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F →
    ∀ i σ s, IsEmbOverK D σ s → HolShape (R.MW i σ) ∧ ∃ w, WtIs (R.MW i σ) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hc i σ s hE
  have hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ := hE.2
  obtain ⟨hH, w0, hw0⟩ := holShape_fixed D G Pl0 T A Ks R hc.models.order i
  have hm := model_overK R i σ hK
  refine ⟨fun ρ => ?_, fun ρ c => w0 (lab σ ρ) c, fun ρ c => ?_⟩
  · have h := hH (lab σ ρ)
    rw [← (hm ρ).1, ← (hm ρ).2] at h
    exact h
  · have h := hw0 (lab σ ρ) c
    unfold extWt at h ⊢
    rw [← (hm ρ).1, ← (hm ρ).2] at h
    exact h

end GlobalTheory.LowRow

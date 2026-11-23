import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistRamifiedIffScalarFormsRamifiedStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistTranslationsActAtLevelPrimeProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorBijectiveFiniteTranslationCombin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlacesStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.TwSProof

section Local

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem ramAt_fixed {p₀ : SplitPt D k} {β : Frame p₀ S n} {P : Pair k n} {φ₀ : GA D S → ℂ} (h : GlobalTheory.FinPl.RamAt β P φ₀) {g : GL n k}
    (hg : g • P = P) : rTrans (β.gl g) φ₀ = φ₀ := by
  obtain ⟨φ, ⟨heq, -, -⟩, rfl⟩ := h
  have := heq g P
  rw [hg] at this
  exact this.symm

theorem comb_foldr (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k) (χ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ i) 1) (η : ι → 𝓀[k]ˣ) (J : List ι) :
    ∃ c : GA D S →₀ ℂ, (∀ g ∈ c.support, g ∈ grpAt S fun x => ∃ i, x = (p i).v) ∧
      ∀ φ, J.foldr (fun i f => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) f) φ = trc c φ := by
  have hsub : ∀ i, grpAt S (· = (p i).v) ≤ grpAt S fun v => ∃ i, v = (p i).v :=
    fun i => AllBij.congGrp_mono S (AllBij.idAt_mono fun v hv => ⟨i, hv⟩)
  induction J with
  | nil =>
    refine ⟨Finsupp.single 1 1, fun g hg => ?_, fun φ => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg)]; exact Subgroup.one_mem _
    · exact (AllBij.act_single_one φ).symm
  | cons i l ih =>
    obtain ⟨c, hc, hl⟩ := ih
    obtain ⟨-, -, C, -, hC, -⟩ := ramBijective_holds D k (p i) n q (χ i) (hχ i) _ rfl (η i) S (β i) (Q i)
    refine ⟨AllBij.cmul (Finsupp.mapDomain (β i).gl C) c, fun g hg => ?_, fun φ => ?_⟩
    · exact AllBij.cmul_mem (S := grpAt S fun v => ∃ i, v = (p i).v)
        (fun g h => hsub i (AllBij.mapDomain_mem _ (AllBij.gl_mem (β i)) C g h))
        (fun g h => hc g (Finsupp.mem_support_iff.2 h)) g (Finsupp.mem_support_iff.1 hg)
    · show sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) (l.foldr _ φ) = _
      rw [hl, hC, AllBij.sum_rep_eq]
      exact (AllBij.act_cmul _ _ _).symm

theorem sOp_keeps (hinj : Function.Injective fun i => (p i).v) (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k)
    (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (ε : 𝓀[k]ˣ) (i : ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') φ) :
    IsContAut S (sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) ε φ) ∧
      ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') (sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) ε φ) := by
  obtain ⟨hbij, -, c, -, hc, -⟩ := ramBijective_holds D k (p i) n q (χ i) (hχ i) _ rfl ε S (β i) (Q i)
  have hT : ∀ φ, sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) ε φ = AllBij.act (Finsupp.mapDomain (β i).gl c) φ :=
    fun φ => (hc φ).trans (AllBij.sum_rep_eq _ _ _)
  have hC := AllBij.mapDomain_mem _ (AllBij.gl_mem (β i)) c
  refine ⟨by rw [hT]; exact AllBij.isContAut_act _ hφ.1, fun i' => ?_⟩
  rcases eq_or_ne i' i with rfl | hne
  · exact hbij.mapsTo (hφ.2 i')
  · rw [hT]
    exact AllBij.ramAt_act _ _ _ (fun x hx g => AllBij.grpAt_comm S (fun e => hne (hinj e)) (hC x hx)
      (AllBij.gl_mem _ g)) (hφ.2 i')

theorem foldr_keeps (hinj : Function.Injective fun i => (p i).v) (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k)
    (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (ε : ι → 𝓀[k]ˣ) (l : List ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') φ) :
    IsContAut S (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (ε i) φ') φ) ∧
      ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (ε i) φ') φ) := by
  induction l with
  | nil => exact hφ
  | cons i l ih => exact sOp_keeps hinj β Q q χ hχ (ε i) i ih

end Local

theorem twS : TwS' := by
  intro B X I hOk hPins l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hStd J q χ hχ
  have hinj : Function.Injective fun i => (p i).v := GlobalTheory.T.splitPoints_lie_over_distinct_places I hOk hPins l Z u p β Q L hStd
  have key : ∀ j (hj : j ≤ B.R.m) φ, RamT (I := I) (l := l) (u := u) (a := a) j φ → ∀ η : ι → 𝓀[k]ˣ,
      ∃ φ', RamT (I := I) (l := l) (u := u) (a := a) j φ' ∧ ∀ b y, A.rd θ j hj b φ' y =
        J.foldr (fun i f => sOp (β j i) (Q j i) q (resChar (χ i) (hχ i) q) (η i) f) (A.rd θ j hj b φ y) := by
    intro j hj φ hφ η
    obtain ⟨c, hc, hfold⟩ := comb_foldr (β j) (Q j) q χ hχ η J
    have hram := GlobalTheory.T.twistRamified_iff_scalarFormsRamified I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ hφ.1
    have hR : ∀ b y, IsContAut _ (trc c (A.rd θ j hj b φ y)) ∧
        ∀ i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (trc c (A.rd θ j hj b φ y)) := by
      intro b y
      rw [← hfold]
      exact foldr_keeps hinj (β j) (Q j) q χ hχ η J ⟨hram.1 b y, fun i => hram.2.1 hφ b y i⟩
    obtain ⟨φ', hφ'F, hφ'⟩ := GlobalTheory.T.twistTranslationsActAtLevelPrime_proof I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj c hc φ hφ.1
      (fun b y i g hg => ramAt_fixed ((hR b y).2 i) hg)
    refine ⟨φ', ?_, fun b y => (hφ' b y).trans (hfold _).symm⟩
    have hram' := GlobalTheory.T.twistRamified_iff_scalarFormsRamified I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ' hφ'F
    exact hram'.2.2 fun b y i => by rw [hφ' b y]; exact (hR b y).2 i
  classical
  refine ⟨fun j η φ => if h : j ≤ B.R.m ∧ RamT (I := I) (l := l) (u := u) (a := a) j φ then
    (key j h.1 φ h.2 η).choose else φ, ?_⟩
  intro j hj φ hφ
  have hram := GlobalTheory.T.twistRamified_iff_scalarFormsRamified I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ hφ.1
  refine ⟨fun b y => ⟨hram.1 b y, fun i => hram.2.1 hφ b y i⟩, fun η => ?_⟩
  have h : j ≤ B.R.m ∧ RamT (I := I) (l := l) (u := u) (a := a) j φ := ⟨hj, hφ⟩
  simp only [dif_pos h]
  exact (key j hj φ hφ η).choose_spec

end GlobalTheory.AdForm.TwSProof

end

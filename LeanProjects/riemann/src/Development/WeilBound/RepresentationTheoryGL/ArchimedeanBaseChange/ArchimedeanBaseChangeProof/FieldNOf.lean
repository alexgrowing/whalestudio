import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.SplitSatPre

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.F

namespace PositivityTheory.Rg.BcB.One

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def InertAt (π : Submodule ℂ (UA E n → ℂ)) (D : Pre E n) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ B, D.Sat w B ∧ ∀ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
    ∀ α, HasSatAt π w s ϖ q α → B = GlobalTheory.LGrp.bcParam n α

def Base (π : Submodule ℂ (UA E n → ℂ)) (D : Pre E n) : Prop :=
  (∀ τ lam, HasWeightAt π τ lam → ∑ i, D.m i τ = infOfWeight lam) ∧ {w | IsSplitAt w ∧ ¬ D.SplitAt π w}.Finite

def Full (π : Submodule ℂ (UA E n → ℂ)) (D : Pre E n) : Prop :=
  Base π D ∧ ∀ w, IsUnramU π w → ¬ IsSplitAt w → InertAt π D w

def RunFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S.card ≤ 1 →
    ∃ (k : ℕ) (D : Fin k → Pre E n), (∀ j, Base π (D j) ∧ ∀ w ∈ S, IsSplitAt w → (D j).SplitAt π w) ∧
      ∀ T : Finset (HeightOneSpectrum (𝓞 E)), ∃ j, ∀ w ∈ T, IsUnramU π w → ¬ IsSplitAt w → InertAt π (D j) w

def FullSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ)
  (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ D D' : Pre E n, Full π D → Full π D' →
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, D.Sat w B ∧ D'.Sat w B

def FullTheta : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ)
  (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ D : Pre E n, Full π D → D.ThetaStable

theorem full_of (h : RunFin) (hE : Unr E) (hn : 1 ≤ n) (π : Submodule ℂ (UA E n → ℂ)) (hπ : IsAutRepU π)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : S.card ≤ 1) :
    ∃ D : Pre E n, Full π D ∧ ∀ w ∈ S, IsSplitAt w → D.SplitAt π w := by
  classical
  obtain ⟨k, D, hD, hT⟩ := h E hE n hn π hπ S hS
  have key : ∃ j, ∀ w, IsUnramU π w → ¬ IsSplitAt w → InertAt π (D j) w := by
    by_contra hcon
    push Not at hcon
    choose w hw1 hw2 hw3 using hcon
    obtain ⟨j, hj⟩ := hT (Finset.univ.image w)
    exact hw3 j (hj (w j) (Finset.mem_image_of_mem w (Finset.mem_univ j)) (hw1 j) (hw2 j))
  obtain ⟨j, hj⟩ := key
  exact ⟨D j, ⟨(hD j).1, hj⟩, (hD j).2⟩

open GlobalTheory.PfBCI in
theorem fieldN_of (hR : RunFin) (hS : FullSat) (hT : FullTheta) (hW : WeightEx) (h1 : Strings) (h2 : CuspCsd)
    (hL : LocRigid) (hP : PermSub) : PositivityTheory.Rg.BcN.BaseChangeIsobaricN := by
  intro E _ _ _ hE n hn π hπ
  obtain ⟨D, hDf, -⟩ := full_of hR hE hn π hπ ∅ (by simp)
  have hReg : ∀ D' : Pre E n, Full π D' → D'.Reg := fun D' hD' τ => by
    obtain ⟨lam, hlam⟩ := hW E n π hπ τ
    exact ⟨lam, hD'.1.1 τ lam hlam⟩
  have hTh : D.ThetaStable := hT E hE n π hπ D hDf
  have hplace : ∀ w, ∃ P, GlobalTheory.PfBCI.AtPlace π D.h D.σ w P := by
    intro w
    by_cases hs : IsSplitAt w
    · obtain ⟨Dw, hDwf, hDws⟩ := full_of hR hE hn π hπ {w} (by simp)
      obtain ⟨P, hPsub, hPc⟩ := hDws w (Finset.mem_singleton_self w) hs
      obtain ⟨e, he⟩ := hL E n D Dw (hReg D hDf) (hReg Dw hDwf) (hS E hE n π hπ D Dw hDf hDwf)
      exact ⟨P, GlobalTheory.PfBCI.split_component D.h D.σ hs P (hP E n D Dw e w (fun i => he i w) P hPsub)
        (GlobalTheory.PfBCI.split_spherical hπ hs P hPc) hPc⟩
    · by_cases hu : IsUnramU π w
      · obtain ⟨B, hB, hBeq⟩ := hDf.2 w hu hs
        obtain ⟨b, hb, hbsum⟩ := hB
        obtain ⟨P, hPsub, hPsph, hPsat⟩ := GlobalTheory.PfBCI.unram_component D.h w (fun i => D.σ i w) b hb
        refine ⟨P, hPsub, fun _ => hPsph, ?_, fun h' => absurd h' hs⟩
        intro s ϖ q hsc hq α hα
        rw [← hBeq s ϖ q hsc hq α hα, ← hbsum]
        exact hPsat
      · obtain ⟨P, hPsub⟩ := GlobalTheory.PfBCI.local_subquotient D.h w (fun i => D.σ i w)
        exact ⟨P, hPsub, fun h' => absurd h' hu, GlobalTheory.PfBCI.inert_of_not_unram hu P, fun h' => absurd h' hs⟩
  choose P hPl using hplace
  refine ⟨D.c, D.N, D.h, D.V, D.σ, D.m, P, ?_⟩
  exact ⟨D.pos, D.discrete, PositivityTheory.Rg.BcB.F.Rig.csdAsc_of h1 h2 D (hReg D hDf) hTh, D.loc, D.inf,
    fun w => (hPl w).1, fun w => (hPl w).2.1, fun w => (hPl w).2.2.1, fun w => (hPl w).2.2.2, hDf.1.1⟩

end PositivityTheory.Rg.BcB.One

end

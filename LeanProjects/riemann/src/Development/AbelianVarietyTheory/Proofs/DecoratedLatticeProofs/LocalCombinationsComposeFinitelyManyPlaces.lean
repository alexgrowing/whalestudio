import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.LocComp

theorem combAt_o {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (l : GlobalTheory.SeeSaw.LocPl ψ S T M M') {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P l.q.v) : GlobalTheory.FinPl.CombAt P l.o :=
  fun x hx i j => GlobalTheory.LocMod.PinInhab.mem_idAt_of_supp l.q hP (l.o_at x hx i j)

theorem combAt_comp {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {P : GlobalTheory.FinPl.Pl D → Prop} {e e' : WO S T →₀ ℂ} (he : GlobalTheory.FinPl.CombAt P e) (he' : GlobalTheory.FinPl.CombAt P e') :
    ∃ e'', GlobalTheory.FinPl.CombAt P e'' ∧ ∀ f, comb ψ S T e'' f = comb ψ S T e (comb ψ S T e' f) := by
  have h4 := (GlobalTheory.DisjComb.main D ψ hψ S T P (fun _ => False) (fun _ _ h => h)).2.2.2.1
  have hm : ∀ {c : WO S T →₀ ℂ}, GlobalTheory.FinPl.CombAt P c → GlobalTheory.FinPl.CombAt (fun p => P p ∨ False) c :=
    fun hc x hx i j => by simpa only [or_false] using hc x hx i j
  obtain ⟨e'', h1, h2⟩ := h4 e e' (hm he) (hm he')
  exact ⟨e'', fun x hx i j => by simpa only [or_false] using h1 x hx i j, h2⟩

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ i, P (L i).q.v) → ∃ o' : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt P o' ∧ ∀ F, comb ψ S T o' F = (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F := by
  intro D ψ hψ S T M M' _ _ n
  induction n with
  | zero =>
    intro L _ P _
    refine ⟨Finsupp.single 0 1, GlobalTheory.FinPl.OffTest.combAt_single_zero P 1, fun F => ?_⟩
    rw [GlobalTheory.FinPl.OffTest.comb_single_zero]
    simp
  | succ n ih =>
    intro L hinj P hP
    obtain ⟨o₁, h₁, h₁'⟩ := ih (fun i => L i.succ) (fun a b h => Fin.succ_injective _ (hinj h)) P (fun i => hP i.succ)
    obtain ⟨o', h', h''⟩ := combAt_comp hψ (combAt_o (L 0) (hP 0)) h₁
    refine ⟨o', h', fun F => ?_⟩
    rw [h'', h₁', List.finRange_succ, List.foldr_cons, List.foldr_map]

end GlobalTheory.LocComp

end

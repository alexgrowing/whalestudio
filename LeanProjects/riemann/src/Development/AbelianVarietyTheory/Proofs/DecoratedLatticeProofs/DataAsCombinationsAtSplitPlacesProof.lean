import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChangeBaseVacuumHeisenbergCombinationStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.AllCombProof

variable {D : D7}

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P Q : Pl D → Prop}
    (h : ∀ x, Q x → P x) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) : Vac ψ S T LS LT Q f := by
  have hmono : latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) P := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (h v hq), rest⟩
  exact ⟨hf.1, fun u hu => hf.2.1 u (hmono hu), fun e he u hu hh => hf.2.2 e he u (hmono hu) hh⟩

theorem combAt_mono {S T : HSp D} {P Q : Pl D → Prop} (h : ∀ x, P x → Q x) {c : WO S T →₀ ℂ} (hc : CombAt P c) :
    CombAt Q c := fun x hx => GlobalTheory.DisjComb.mxAt_mono h (hc x hx)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n} {LS : Lat S}
  {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ}

theorem overAll_nil {f f' : WO S T → ℂ} : OverAll ψ α β LS LT Ψ [] f f' ↔ f' = f := Iff.rfl

theorem overAll_cons {i : ι} {J : List ι} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ (i :: J) f f' ↔
      ∃ g, OverAll ψ α β LS LT Ψ J f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' := Iff.rfl

theorem over_unique (hψ : IsStdChar D ψ (-1)) {i : ι} {g f' f'' : WO S T → ℂ}
    (h' : Over ψ (α i) (β i) LS LT g (Ψ i) f') (h'' : Over ψ (α i) (β i) LS LT g (Ψ i) f'') : f' = f'' :=
  ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k (p i) n n' ψ hψ S T (α i) (β i) LS LT h'.1 h'.2.1 g h'.2.2.1).1 (Ψ i) h'.2.2.2.1).unique h' h''

theorem overAll_unique (hψ : IsStdChar D ψ (-1)) (J : List ι) : ∀ f f' f'' : WO S T → ℂ,
    OverAll ψ α β LS LT Ψ J f f' → OverAll ψ α β LS LT Ψ J f f'' → f' = f'' := by
  induction J with
  | nil => intro f f' f'' h' h''; rw [overAll_nil.1 h', overAll_nil.1 h'']
  | cons i J ih =>
    intro f f' f'' h' h''
    obtain ⟨g, hg, h'⟩ := overAll_cons.1 h'
    obtain ⟨g', hg', h''⟩ := overAll_cons.1 h''
    obtain rfl := ih f g g' hg hg'
    exact over_unique hψ h' h''

theorem over_comb (hψ : IsStdChar D ψ (-1)) {i : ι} (hu : (p i).UnitAA) {Q : Pl D → Prop} (hQ : ¬ Q (p i).v)
    {d : WO S T →₀ ℂ} (hd : CombAt Q d) {g f : WO S T → ℂ} (h : Over ψ (α i) (β i) LS LT g (Ψ i) f) :
    Over ψ (α i) (β i) LS LT (comb ψ S T d g) (Ψ i) (comb ψ S T d f) := by
  obtain ⟨c, hc, hcf⟩ := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p i) n n' ψ hψ hu S T (α i) (β i) LS LS LT LT h.1 h.2.1 h.1 h.2.1).2
    (Ψ i) h.2.2.2.1
  have M := GlobalTheory.DisjComb.main D ψ hψ S T Q (· = (p i).v) (fun x hx hx' => hQ (hx' ▸ hx))
  have hf : f = comb ψ S T c g := over_unique hψ h (hcf g h.2.2.1)
  rw [hf, M.1 d c hd hc g]
  exact hcf _ ((M.2.1 d hd).2 LS LT g h.2.2.1)

theorem overAll_comb (hψ : IsStdChar D ψ (-1)) (hu : ∀ i, (p i).UnitAA) {Q : Pl D → Prop} (hQ : ∀ i, ¬ Q (p i).v)
    {d : WO S T →₀ ℂ} (hd : CombAt Q d) (J : List ι) (f : WO S T → ℂ) : ∀ f', OverAll ψ α β LS LT Ψ J f f' →
      OverAll ψ α β LS LT Ψ J (comb ψ S T d f) (comb ψ S T d f') := by
  induction J with
  | nil => intro f' h; rw [overAll_nil.1 h]; exact overAll_nil.2 rfl
  | cons i J ih =>
    intro f' h
    obtain ⟨g, hg, h⟩ := overAll_cons.1 h
    exact overAll_cons.2 ⟨_, ih g hg, over_comb hψ (hu i) (hQ i) hd h⟩

theorem exists_comb (hψ : IsStdChar D ψ (-1)) (hu : ∀ i, (p i).UnitAA) (hinj : Function.Injective fun i => (p i).v)
    (hLS : IsSelfDualC S LS) (hLT : IsSelfDualC T LT) (hΨ : ∀ i, Ψ i ∈ SB (Matrix n n' k)) (J : List ι) (hJ : J.Nodup) :
    ∃ c : WO S T →₀ ℂ, CombAt (fun x => ∃ i ∈ J, x = (p i).v) c ∧
      ∀ f, (∀ i ∈ J, Vac ψ S T LS LT (· = (p i).v) f) → OverAll ψ α β LS LT Ψ J f (comb ψ S T c f) := by
  induction J with
  | nil =>
    exact ⟨Finsupp.single 0 1, OffTest.combAt_single_zero _ _, fun f _ => overAll_nil.2 (OffTest.comb_single_zero ψ S T f)⟩
  | cons i J ih =>
    obtain ⟨hi, hJ'⟩ := List.nodup_cons.1 hJ
    obtain ⟨c', hc', hf'⟩ := ih hJ'
    obtain ⟨c, hc, hcf⟩ := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p i) n n' ψ hψ (hu i) S T (α i) (β i) LS LS LT LT hLS hLT hLS hLT).2
      (Ψ i) (hΨ i)
    have M := GlobalTheory.DisjComb.main D ψ hψ S T (fun x => ∃ j ∈ J, x = (p j).v) (· = (p i).v) (by
      rintro x ⟨j, hj, rfl⟩ hx
      exact hi (hinj hx ▸ hj))
    obtain ⟨c'', hc'', heq⟩ := M.2.2.2.1 c c' (combAt_mono (fun x hx => Or.inr hx) hc)
      (combAt_mono (fun x hx => Or.inl hx) hc')
    refine ⟨c'', combAt_mono ?_ hc'', fun f hf => ?_⟩
    · rintro x (⟨j, hj, rfl⟩ | rfl)
      · exact ⟨j, List.mem_cons_of_mem _ hj, rfl⟩
      · exact ⟨i, List.mem_cons_self, rfl⟩
    · rw [heq]
      exact overAll_cons.2 ⟨_, hf' f fun j hj => hf j (List.mem_cons_of_mem _ hj),
        hcf _ ((M.2.1 c' hc').2 LS LT f (hf i List.mem_cons_self))⟩

end GlobalTheory.FinPl.AllCombProof

namespace GlobalTheory.FinPl

open AllCombProof in

theorem allComb : ∀ D : D7, AllComb D := by
  intro D k _ _ _ _ ι p I P hP n n' _ _ _ _ ψ hψ S T α β LS LT hLS hLT Ψ
  refine ⟨fun hΨ => ?_, overAll_unique hψ I, fun d hd f hf => ⟨?_, ?_⟩⟩
  · obtain ⟨c, hc, hf⟩ := exists_comb (α := α) (β := β) hψ hP.unit hP.inj hLS hLT hΨ I hP.nodup
    refine ⟨c, combAt_mono ?_ hc, fun f h => hf f fun i _ => vac_mono ?_ h⟩
    · rintro x ⟨i, -, rfl⟩
      exact (hP.mem _).2 ⟨i, rfl⟩
    · rintro x rfl
      exact (hP.mem _).2 ⟨i, rfl⟩
  · exact ((GlobalTheory.DisjComb.main D ψ hψ S T (fun x => ¬ P x) P fun x hx => hx).2.1 d hd).2 LS LT f hf
  · exact overAll_comb hψ hP.unit (fun i h => h ((hP.mem _).2 ⟨i, rfl⟩)) hd I f

end GlobalTheory.FinPl

end

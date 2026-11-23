import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.FinReps

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem preEquiv_symm {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {P P' : Pre E n} (h : PreEquiv P P') :
    PreEquiv P' P := by
  obtain ⟨e, h1, h2⟩ := h
  refine ⟨e.symm, fun i w => ?_, fun i τ => ?_⟩
  · have := h1 (e.symm i) w; rw [Equiv.apply_symm_apply] at this; exact this.symm
  · have := h2 (e.symm i) τ; rw [Equiv.apply_symm_apply] at this; exact this.symm

theorem rl_levels (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a)
    (Mb : Mods E b) (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (h1 : IsOpen (K₁ : Set (GL (Fin a) (Af E)))) (h2 : IsOpen (K₂ : Set (GL (Fin b) (Af E)))) :
    Levels E (rlΘ₁ hR E a b Ma Mb K₁ K₂) ∧ Levels E (rlΘ₂ hR E a b Ma Mb K₁ K₂) :=
  (hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1 a b Ma Mb K₁ K₂ h1 h2

theorem rl_ktypes (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a)
    (Mb : Mods E b) : KTypes E (rlΩ₁ hR E a b Ma Mb) ∧ KTypes E (rlΩ₂ hR E a b Ma Mb) :=
  ⟨((hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1 a b Ma Mb).2.2.1,
    ((hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1 a b Ma Mb).2.2.2.1⟩

theorem ub_fin {α ι : Type} [Fintype ι] {κ : ι → Type} [∀ i, Fintype (κ i)] (T : Finset α) (f : ∀ i, κ i → α → ℕ) :
    ∃ m, ∀ i k, ∀ w ∈ T, f i k w ≤ m := by
  refine ⟨∑ i, ∑ k, ∑ w ∈ T, f i k w, fun i k w hw => ?_⟩
  calc f i k w ≤ ∑ w' ∈ T, f i k w' := Finset.single_le_sum (f := fun w' => f i k w') (fun _ _ => Nat.zero_le _) hw
    _ ≤ ∑ k', ∑ w' ∈ T, f i k' w' := Finset.single_le_sum (f := fun k' => ∑ w' ∈ T, f i k' w') (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    _ ≤ ∑ i', ∑ k', ∑ w' ∈ T, f i' k' w' := Finset.single_le_sum (f := fun i' => ∑ k', ∑ w' ∈ T, f i' k' w') (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

set_option maxHeartbeats 4000000 in
def ClauseA {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (T' : Finset (Pl E)) (d : LocData E n) : Prop :=
  ∀ i w, ∃ Z : Set ((Fin (F₀.C.a i) → ℂˣ) × (Fin (n - F₀.C.a i) → ℂˣ)), Z.Finite ∧
    ∀ s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → w ∈ T' →
      ∀ ξa ξb, JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb → (ξa, ξb) ∈ Z

set_option maxHeartbeats 4000000 in
def ClauseC {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (T' : Finset (Pl E)) (d : LocData E n) : Prop :=
  ∃ m₀ : ℕ, ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → ∀ w ∈ T',
    Module.finrank ℂ ↥(fixed (pairAt Pa Pb w) (I2 (F₀.C.a i) (n - F₀.C.a i) w)) ≤ m₀

set_option maxHeartbeats 4000000 in
theorem candFin_d (hJ : JEigFin) (hFS : FinStrict) (hEq : StrictEqv) (hSP : StrictPre) (hSPr : StrictProd)
    (hSJ : StrictJoin) (hCP : CandParts) (hII : IsoInv) (hAd : AdmProd)
    {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (T' : Finset (Pl E)) (d : LocData E n)
    (hO : ∀ i : F₀.C.ι, IsOpen (lev₁ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (F₀.C.a i)) (Af E))) ∧
      IsOpen (lev₂ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (n - F₀.C.a i)) (Af E)))) :
    ClauseA F₀ T' d ∧ He2.ClauseB F₀ d ∧ ClauseC F₀ T' d := by
  have hLA : ∀ i : F₀.C.ι, Levels E (rlΘ₁ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (lev₁ F₀.Sec d (F₀.C.a i)) (lev₂ F₀.Sec d (F₀.C.a i))) ∧
      Levels E (rlΘ₂ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (lev₁ F₀.Sec d (F₀.C.a i)) (lev₂ F₀.Sec d (F₀.C.a i))) := fun i =>
    rl_levels hR E _ _ _ _ _ _ (hO i).1 (hO i).2
  have hKA : ∀ i : F₀.C.ι, KTypes E (rlΩ₁ hR E (F₀.C.a i) (n - F₀.C.a i) (F₀.A i).Ma (F₀.A i).Mb) ∧
      KTypes E (rlΩ₂ hR E (F₀.C.a i) (n - F₀.C.a i) (F₀.A i).Ma (F₀.A i).Mb) := fun i => rl_ktypes hR E _ _ _ _
  choose kA PA hPA using fun i : F₀.C.ι => hFS E (F₀.C.a i) _ _ (hLA i).1 (hKA i).1 (mOf (F₀.A i).χa)
  choose kB PB hPB using fun i : F₀.C.ι => hFS E (n - F₀.C.a i) _ _ (hLA i).2 (hKA i).2 (mOf (F₀.A i).χb)

  have hcls : ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA i ja)) ∧ ∃ jb, Strict Pb (PB i jb) := by
    intro i s₁ s₂ Pa Pb D hc
    have hp := hCP hR E n π S F₀ d i s₁ s₂ Pa Pb D hc
    have hm := LemDd.cand_sum hc
    exact ⟨hPA i Pa hp.1 hm.1, hPB i Pb hp.2 hm.2⟩
  have hunif : ∀ w, ordL ((F₀.d₀.ϖ w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := fun w => (F₀.unif w).1.1
  choose Z mZ hZ using fun (i : F₀.C.ι) (w : Pl E) (ja : Fin (kA i)) (jb : Fin (kB i)) =>
    hJ E _ _ (PA i ja) (PB i jb) w (F₀.d₀.ϖ w) (hunif w)
  obtain ⟨m₀, hub⟩ := ub_fin (κ := fun i => Fin (kA i) × Fin (kB i)) T' (fun i k w => mZ i w k.1 k.2)
  refine ⟨fun i w => ⟨⋃ ja, ⋃ jb, Z i w ja jb, Set.finite_iUnion fun ja => Set.finite_iUnion fun jb => (hZ i w ja jb).1,
    fun s₁ s₂ Pa Pb D hc _ ξa ξb hj => ?_⟩, fun w hw => ?_, ⟨m₀,
    fun i s₁ s₂ Pa Pb D hc w hw => ?_⟩⟩
  · obtain ⟨⟨ja, ha⟩, ⟨jb, hb⟩⟩ := hcls i s₁ s₂ Pa Pb D hc
    have := ((hZ i w ja jb).2 Pa Pb (preEquiv_symm (hSP E _ _ _ ha)) (preEquiv_symm (hSP E _ _ _ hb))).2 ξa ξb hj
    exact Set.mem_iUnion.2 ⟨ja, Set.mem_iUnion.2 ⟨jb, this⟩⟩
  · exact He2.candB hEq hSPr hSJ hII hAd F₀ d kA kB PA PB hcls w hw
  · obtain ⟨⟨ja, ha⟩, ⟨jb, hb⟩⟩ := hcls i s₁ s₂ Pa Pb D hc
    have h1 := ((hZ i w ja jb).2 Pa Pb (preEquiv_symm (hSP E _ _ _ ha)) (preEquiv_symm (hSP E _ _ _ hb))).1
    exact h1.trans (hub i (ja, jb) w hw)

set_option maxHeartbeats 4000000 in
theorem candFin_of : CandFinOf := by
  intro hJ hFS hEq hSP hSPr hSJ hCP hLO hII hAd
  intro hR E _ _ _ hU n hn π hπ S F₀ T' c e b hT'
  exact candFin_d hJ hFS hEq hSP hSPr hSJ hCP hII hAd F₀ T' (F₀.loc T' c e b)
    (fun i => hLO hR E n π S F₀ T' c e b (F₀.C.a i) (F₀.C.le i))

end PositivityTheory.Rg.BcB.F.FX.Bo

end

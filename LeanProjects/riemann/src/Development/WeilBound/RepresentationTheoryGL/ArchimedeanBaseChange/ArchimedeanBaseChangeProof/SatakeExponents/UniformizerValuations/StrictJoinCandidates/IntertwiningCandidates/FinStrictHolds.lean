import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FinIso
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FixedMonoBo

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.Tw.FiniteStrictOrder

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem forall₂_ofFn {α β : Type*} (R : α → β → Prop) {c c' : ℕ} (h : c = c') (f : Fin c → α) (g : Fin c' → β)
    (H : ∀ i, R (f i) (g (Fin.cast h i))) : List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  subst h
  induction c with
  | zero => simp
  | succ c ih =>
    simp only [List.ofFn_succ]
    exact List.Forall₂.cons (by simpa using H 0) (ih _ _ fun i => by simpa using H i.succ)

theorem siso_trans {x y z : Σ M : ℕ, Submodule ℂ (Sm E M)} (hy : IsStable y.2) (hx : SIso x z) (hyz : SIso y z) :
    SIso x y := by
  obtain ⟨M, Vx⟩ := x
  obtain ⟨M', Vy⟩ := y
  obtain ⟨Mz, Vz⟩ := z
  obtain ⟨h1, h1'⟩ := hx
  obtain ⟨h2, h2'⟩ := hyz
  simp only at h1 h2
  subst h1
  subst h2
  exact ⟨rfl, PositivityTheory.Rg.BcB.F.F5.Bo.isoV_trans' h1' (PositivityTheory.Rg.BcB.F.F5.Bo.isoV_symm' hy h2')⟩

theorem c_le {a : ℕ} (P : Pre E a) : P.c ≤ a := by
  calc P.c = ∑ _i : Fin P.c, 1 := by simp
    _ ≤ ∑ i, P.N i := Finset.sum_le_sum fun i _ => P.pos i
    _ = a := P.h

theorem N_le {a : ℕ} (P : Pre E a) (j : Fin P.c) : P.N j ≤ a := by
  calc P.N j ≤ ∑ i, P.N i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ = a := P.h

theorem m_le {a : ℕ} (P : Pre E a) (m₀ : (E →+* ℂ) → Multiset ℂ) (hm : ∀ τ, ∑ j, P.m j τ = m₀ τ) (j : Fin P.c)
    (τ : E →+* ℂ) : P.m j τ ≤ m₀ τ := by
  rw [← hm τ]
  exact Finset.single_le_sum (f := fun j => P.m j τ) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ j)

end PositivityTheory.Rg.BcB.F.FX.Bo.Tw.FiniteStrictOrder

namespace PositivityTheory.Rg.BcB.F.FX.Bo.Tw

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo FiniteStrictOrder

theorem FinStrict_holds : FinStrict := by
  intro E _ _ _ a Θ Ω hΘ hΩ m₀

  have hF := fun (M : ℕ) (K' : Subgroup (GL (Fin M) (Af E))) (W' : Submodule ℂ (Kinf E M → ℂ))
    (m' : (E →+* ℂ) → Multiset ℂ) (hK : IsOpen (K' : Set (GL (Fin M) (Af E)))) (hW : FiniteDimensional ℂ W') =>
    Bo.FinIso_holds E M K' W' m' hK hW
  choose V0 _hV0 hV0 using hF

  let Ms : Set ((E →+* ℂ) → Multiset ℂ) := Set.pi Set.univ fun τ => {s | s ≤ m₀ τ}
  have hMs : Ms.Finite := by
    refine Set.Finite.pi fun τ => ?_
    refine (Multiset.toFinset (Multiset.powerset (m₀ τ))).finite_toSet.subset fun s hs => ?_
    simpa [Multiset.mem_powerset] using hs

  let Reps : Set (Σ M : ℕ, Submodule ℂ (Sm E M)) :=
    ⋃ M ∈ Set.Iic a, ⋃ K' ∈ Θ M, ⋃ W' ∈ Ω M, ⋃ m' ∈ Ms,
      ⋃ (hK : IsOpen (K' : Set (GL (Fin M) (Af E)))), ⋃ (hW : FiniteDimensional ℂ W'),
        (Sigma.mk M) '' (V0 M K' W' m' hK hW : Set (Submodule ℂ (Sm E M)))
  have hReps : Reps.Finite :=
    (Set.finite_Iic a).biUnion fun M _ => (hΘ M).1.biUnion fun K' _ => (hΩ M).1.biUnion fun W' _ =>
      hMs.biUnion fun m' _ => Set.finite_iUnion fun hK => Set.finite_iUnion fun hW => (Finset.finite_toSet _).image _
  have := hReps.to_subtype
  have := hMs.to_subtype
  let Good : Pre E a → Prop := fun P =>
    (∀ j, ∃ K' ∈ Θ (P.N j), ∃ W' ∈ Ω (P.N j), HasType K' W' (P.V j)) ∧ (∀ τ, ∑ j, P.m j τ = m₀ τ)

  have hrep : ∀ P : Pre E a, Good P → ∀ j, ∃ z ∈ Reps, SIso ⟨P.N j, P.V j⟩ z := by
    intro P hP j
    obtain ⟨K', hK', W', hW', ht⟩ := hP.1 j
    have hKo := (hΘ _).2 K' hK'
    have hWf := (hΩ _).2 W' hW'
    obtain ⟨V', hV'm, hiso⟩ := hV0 _ K' W' (P.m j) hKo hWf (P.V j) (P.discrete j) ht (P.inf j)
    refine ⟨⟨P.N j, V'⟩, ?_, rfl, hiso⟩
    simp only [Reps, Set.mem_iUnion, Set.mem_image]
    exact ⟨P.N j, N_le P j, K', hK', W', hW', P.m j, fun τ _ => m_le P m₀ hP.2 j τ, hKo, hWf, V', hV'm, rfl⟩
  have hmem : ∀ P : Pre E a, Good P → ∀ j, P.m j ∈ Ms := fun P hP j τ _ => m_le P m₀ hP.2 j τ

  let part : Pre E a → ℕ → Option (Reps × Ms) := fun P i =>
    if h : i < P.c then
      (if h' : (∃ z ∈ Reps, SIso ⟨P.N ⟨i, h⟩, P.V ⟨i, h⟩⟩ z) ∧ P.m ⟨i, h⟩ ∈ Ms then
        some (⟨Classical.choose h'.1, (Classical.choose_spec h'.1).1⟩, ⟨P.m ⟨i, h⟩, h'.2⟩) else none)
    else none
  let key : Pre E a → Fin (a + 1) × (Fin a → Option (Reps × Ms)) := fun P =>
    (⟨min P.c a, Nat.lt_succ_of_le (min_le_right _ _)⟩, fun i => part P i.1)

  have hkey : ∀ P Q : Pre E a, Good P → Good Q → key P = key Q → Strict P Q := by
    intro P Q hP hQ hPQ
    have hc : P.c = Q.c := by
      have := congrArg (fun x => (x.1 : ℕ)) (congrArg Prod.fst hPQ)
      simpa [key, min_eq_left (c_le P), min_eq_left (c_le Q)] using this
    have hpart : ∀ j : Fin P.c, part P j.1 = part Q j.1 := fun j =>
      congrFun (congrArg Prod.snd hPQ) ⟨j.1, lt_of_lt_of_le j.2 (c_le P)⟩
    have hsome : ∀ (R : Pre E a) (hR : Good R) (j : Fin R.c), ∃ z : Reps, SIso ⟨R.N j, R.V j⟩ z.1 ∧
        part R j.1 = some (z, ⟨R.m j, hmem R hR j⟩) := by
      intro R hR j
      have h' : (∃ z ∈ Reps, SIso ⟨R.N ⟨j.1, j.2⟩, R.V ⟨j.1, j.2⟩⟩ z) ∧ R.m ⟨j.1, j.2⟩ ∈ Ms := ⟨hrep R hR j, hmem R hR j⟩
      refine ⟨⟨Classical.choose h'.1, (Classical.choose_spec h'.1).1⟩, (Classical.choose_spec h'.1).2, ?_⟩
      simp only [part, dif_pos j.2, dif_pos h']
    refine ⟨forall₂_ofFn SIso hc _ _ fun j => ?_, hc, fun j => ?_⟩
    · obtain ⟨z, hz, hPz⟩ := hsome P hP j
      obtain ⟨z', hz', hQz⟩ := hsome Q hQ (Fin.cast hc j)
      have e := (hpart j).trans (hQz : part Q j.1 = _)
      rw [hPz] at e
      simp only [Option.some.injEq, Prod.mk.injEq] at e
      rw [← e.1] at hz'
      exact siso_trans (Q.discrete _).stable hz hz'
    · obtain ⟨z, hz, hPz⟩ := hsome P hP j
      obtain ⟨z', hz', hQz⟩ := hsome Q hQ (Fin.cast hc j)
      have e := (hpart j).trans (hQz : part Q j.1 = _)
      rw [hPz] at e
      simp only [Option.some.injEq, Prod.mk.injEq, Subtype.mk.injEq] at e
      exact e.2

  let Im : Set (Fin (a + 1) × (Fin a → Option (Reps × Ms))) := key '' {P | Good P}
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin Im
  have hpre : ∀ i : Fin k, ∃ P, Good P ∧ key P = (e.symm i).1 := fun i => (e.symm i).2
  choose Pl hPl hkPl using hpre
  refine ⟨k, Pl, fun P h1 h2 => ?_⟩
  have hP : Good P := ⟨h1, h2⟩
  refine ⟨e ⟨key P, P, hP, rfl⟩, hkey P _ hP (hPl _) ?_⟩
  rw [hkPl, Equiv.symm_apply_apply]

end PositivityTheory.Rg.BcB.F.FX.Bo.Tw

end

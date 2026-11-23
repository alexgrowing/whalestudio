import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMonoReline
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsometricVerticalIntersectionEqStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MassFormulaConjugationAction
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.Swap

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem arList_swap_one {P : Ideal (MvPolynomial (Σ k, ι k) ℤ)}
    {I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) (T : LocPair ι ℤ Unit)
    (hT : T.IsVertOff P ∅) {A A' : HermLine ι} (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A')
    (hiso : T.IsIsometric P (fun _ => A) (fun _ => A'))
    (pre post : List (HermLine ι)) (hpre : ∀ b ∈ pre, IsSmoothHerm b)
    (hpost : ∀ b ∈ post, IsSmoothHerm b) (hP : IsArithVar P ((pre ++ post).length + 1)) :
    arList I P (pre ++ A :: post) = arList I P (pre ++ A' :: post) := by
  have hL : ∀ j, IsSmoothHerm ((pre ++ post).get j) := fun j => by
    rcases List.mem_append.1 (List.get_mem _ j) with h | h
    · exact hpre _ h
    · exact hpost _ h
  have hsnoc : ∀ B : HermLine ι, IsSmoothHerm B → arList I P (pre ++ B :: post) =
      I P ((pre ++ post).length + 1) (Fin.snoc (pre ++ post).get B) := by
    intro B hB
    refine arList_eq_of_perm hP hI _ _ ?_ ?_
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa using hB
      · simpa using hL i
    · rw [List.ofFn_succ']
      simp only [Fin.snoc_castSucc, Fin.snoc_last, List.ofFn_get, List.concat_eq_append]
      exact List.perm_middle.trans (List.perm_append_singleton _ _).symm
  rw [hsnoc A hA, hsnoc A' hA']
  have h := GlobalTheory.T.isometric_vertical_intersection_eq K ι P _ hP I hI ∅ T hT A A' hA hA' hiso (pre ++ post).get hL
  simpa [sub_eq_zero] using h

theorem arList_swap_map {J : Type} {P : Ideal (MvPolynomial (Σ k, ι k) ℤ)}
    {I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) (T : LocPair ι ℤ Unit)
    (hT : T.IsVertOff P ∅) {A A' : HermLine ι} (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A')
    (hiso : T.IsIsometric P (fun _ => A) (fun _ => A')) (F G : J → HermLine ι)
    (hF : ∀ j, IsSmoothHerm (F j)) (hG : ∀ j, IsSmoothHerm (G j))
    (hFG : ∀ j, F j = G j ∨ (F j = A ∧ G j = A')) (l : List J) :
    ∀ (pre : List (HermLine ι)), (∀ b ∈ pre, IsSmoothHerm b) →
      IsArithVar P (pre.length + l.length) →
      arList I P (pre ++ l.map F) = arList I P (pre ++ l.map G) := by
  induction l with
  | nil => intro pre _ _; rfl
  | cons j l ih =>
    intro pre hpre hP
    have e1 : pre ++ (j :: l).map F = (pre ++ [F j]) ++ l.map F := by simp
    have e2 : (pre ++ [F j]) ++ l.map G = pre ++ F j :: l.map G := by simp
    have hpre' : ∀ b ∈ pre ++ [F j], IsSmoothHerm b := fun b hb => by
      rcases List.mem_append.1 hb with h | h
      · exact hpre b h
      · rw [List.mem_singleton.1 h]; exact hF j
    have hlen : (pre ++ [F j]).length + l.length = pre.length + (j :: l).length := by
      simp; omega
    rw [e1, ih _ hpre' (hlen ▸ hP), e2, List.map_cons]
    rcases hFG j with h | ⟨h, h'⟩
    · rw [h]
    · rw [h, h']
      refine arList_swap_one hI T hT hA hA' hiso pre _ hpre ?_ ?_
      · intro b hb
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
        exact hG i
      · have : (pre ++ l.map G).length + 1 = pre.length + (j :: l).length := by
          simp; omega
        exact this ▸ hP

theorem ofFn_monoLines {J : Type} (ℓ : J → HermLine ι) (m : J →₀ ℕ) (d : ℕ)
    (hd : (Finsupp.toMultiset m).toList.length = d) :
    List.ofFn (monoLines ℓ m d) = (Finsupp.toMultiset m).toList.map ℓ := by
  subst hd
  apply List.ext_get (by simp)
  intro n h₁ h₂
  simp [monoLines]

end GlobalTheory.CompanionTheory.Ar.Num.Swap

namespace GlobalTheory.CompanionTheory.Ar.Num.Link

open GlobalTheory.CompanionTheory.Ar.Top.Link

theorem arMono_swapA : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) [DecidableEq M.K] (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (A' : HermLine M.ι) (hs : IsSmoothHerm A') (hc : IsConjInvariantH A') (T : LocPair M.ι ℤ Unit), T.IsVertOff M.P ∅ → T.IsIsometric M.P (fun _ => M.A) (fun _ => A') → ∀ (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ), M.arMono II t m = (Link.reline M M.xdeg M.x M.x_deg M.x_smooth M.x_conj A' hs hc).arMono II t m := by
  intro Ψ _ N M _ II hII A' hs hc T hT hiso t m
  set M' := Link.reline M M.xdeg M.x M.x_deg M.x_smooth M.x_conj A' hs hc with hM'
  have hI : IsIntersectionFamily (II M.K M.ι) := hII.1 M.K M.ι
  have hP : IsArithVar M.P (dimFl Ψ N + 1) := M.arith
  have hF : ∀ j, IsSmoothHerm (M.line t j) := fun j => by
    cases j with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  have hG : ∀ j, IsSmoothHerm (M'.line t j) := fun j => by
    cases j with
    | none => exact hs
    | some r => exact M.x_smooth t r
  have hFG : ∀ j, M.line t j = M'.line t j ∨ (M.line t j = M.A ∧ M'.line t j = A') := fun j => by
    cases j with
    | none => exact Or.inr ⟨rfl, rfl⟩
    | some r => exact Or.inl rfl
  show (if m.degree = dimFl Ψ N + 1 then
      II M.K M.ι M.P (dimFl Ψ N + 1) (monoLines (M.line t) m (dimFl Ψ N + 1)) /
        ((M.δ : ℝ) * (M.kA : ℝ) ^ m none) else 0) =
    (if m.degree = dimFl Ψ N + 1 then
      II M.K M.ι M.P (dimFl Ψ N + 1) (monoLines (M'.line t) m (dimFl Ψ N + 1)) /
        ((M.δ : ℝ) * (M.kA : ℝ) ^ m none) else 0)
  split_ifs with hd
  swap
  · rfl
  have hlen : (Finsupp.toMultiset m).toList.length = dimFl Ψ N + 1 := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset, ← hd]
    rfl
  have hmono : ∀ ℓ : Option (Ψ × Fin N) → HermLine M.ι, (∀ j, IsSmoothHerm (ℓ j)) →
      II M.K M.ι M.P (dimFl Ψ N + 1) (monoLines ℓ m (dimFl Ψ N + 1)) =
        arList (II M.K M.ι) M.P ((Finsupp.toMultiset m).toList.map ℓ) := by
    intro ℓ hℓ
    symm
    refine arList_eq_of_perm hP hI _ _ ?_ ?_
    · intro j
      unfold monoLines
      split_ifs with h
      · exact hℓ _
      · exact absurd (by have := j.2; omega) h
    · rw [Swap.ofFn_monoLines ℓ m _ hlen]
  have key : arList (II M.K M.ι) M.P ((Finsupp.toMultiset m).toList.map (M.line t)) =
      arList (II M.K M.ι) M.P ((Finsupp.toMultiset m).toList.map (M'.line t)) :=
    Swap.arList_swap_map hI T hT M.A_smooth hs hiso _ _ hF hG hFG _ [] (by simp) (by simpa [hlen] using hP)
  exact congrArg (· / ((M.δ : ℝ) * (M.kA : ℝ) ^ m none))
    ((hmono _ hF).trans (key.trans (hmono (M'.line t) hG).symm))

end GlobalTheory.CompanionTheory.Ar.Num.Link

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IntersectionSystemDegreeStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionConstantMetricStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionMultilinearAllStatement

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.GeoMix

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem line_ext {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl

def oneLine (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι :=
  HermLine.ofWeight (fun _ => (-1 : ℝ)) (fun _ _ _ => rfl)

theorem smooth_oneLine : IsSmoothHerm (oneLine ι) := by
  show ContDiffOn ℝ _ (fun _ => Real.exp (-(-1 : ℝ))) _
  exact contDiffOn_const

theorem smooth_comb {J : Type} [Fintype J] {ℓ : J → HermLine ι} (hℓ : ∀ j, IsSmoothHerm (ℓ j))
    (n : J → ℤ) : IsSmoothHerm (combLine ℓ n) := by
  refine contDiffOn_prod fun a _ => ?_
  intro z hz
  have h0 : (ℓ a).h z ≠ 0 := ((ℓ a).pos z hz).ne'
  have hf := hℓ a z hz
  have key : ∀ m : ℤ, ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (ℓ a).h z ^ m)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} z := by
    intro m
    cases m with
    | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
    | negSucc k =>
      simp only [zpow_negSucc]
      exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)
  exact key _

def extLine {J : Type} (ℓ : J → HermLine ι) : Option J → HermLine ι
  | none => oneLine ι
  | some j => ℓ j

def extExp {J : Type} (m : J → ℤ) : Option J → ℤ
  | none => 0
  | some j => m j

def lastExp {J : Type} : Option J → ℤ
  | none => 1
  | some _ => 0

theorem comb_extExp {J : Type} [Fintype J] (ℓ : J → HermLine ι) (m : J → ℤ) :
    combLine (extLine ℓ) (extExp m) = combLine ℓ m := by
  apply line_ext
  · simp [combLine, Fintype.sum_option, extLine, extExp]
  · funext z
    simp [combLine, Fintype.prod_option, extLine, extExp]

theorem comb_lastExp {J : Type} [Fintype J] (ℓ : J → HermLine ι) :
    combLine (extLine ℓ) lastExp = oneLine ι := by
  apply line_ext
  · simp [combLine, Fintype.sum_option, extLine, lastExp]
  · funext z
    simp [combLine, Fintype.prod_option, extLine, lastExp]

theorem pts_eq_II (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (P : Ideal (MRing ι))
    {e : ℕ} (L : Fin e → HermLine ι) (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) :
    ptsIntegral P (fun k z => Real.log ((L k).h z)) (fun _ => 1) =
      II K ι P (e + 1) (Fin.snoc L (oneLine ι)) := by
  have h := GlobalTheory.T.arith_intersection_constant_metric II hII.1 K ι P e L (-1) hP hL
  have h' : II K ι P (e + 1) (Fin.snoc L (oneLine ι)) =
      - -1 * ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := h
  rw [h']
  ring

theorem pts_comb (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (P : Ideal (MRing ι))
    {e : ℕ} {J : Type} [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (n : Fin e → J → ℤ)
    (hP : IsArithVar P (e + 1)) (hℓ : ∀ j, IsSmoothHerm (ℓ j)) :
    ptsIntegral P (fun k z => Real.log ((combLine ℓ (n k)).h z)) (fun _ => 1) =
      ∑ w : Fin e → J, (∏ k, (n k (w k) : ℝ)) *
        ptsIntegral P (fun k z => Real.log ((ℓ (w k)).h z)) (fun _ => 1) := by
  have hext : ∀ o, IsSmoothHerm (extLine ℓ o) := by
    intro o
    cases o with
    | none => exact smooth_oneLine
    | some j => exact hℓ j
  let n' : Fin (e + 1) → Option J → ℤ :=
    Fin.snoc (α := fun _ => Option J → ℤ) (fun k => extExp (n k)) lastExp
  have hn'c : ∀ k : Fin e, n' k.castSucc = extExp (n k) := fun k => by simp [n']
  have hn'l : n' (Fin.last e) = lastExp := by simp [n']
  have hcomb : (Fin.snoc (fun k => combLine ℓ (n k)) (oneLine ι) : Fin (e + 1) → HermLine ι) =
      fun k => combLine (extLine ℓ) (n' k) := by
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp [hn'l, comb_lastExp]
    · simp [hn'c, comb_extExp]
  rw [pts_eq_II II hII P _ hP (fun k => smooth_comb hℓ _), hcomb,
    GlobalTheory.T.arith_intersection_multilinear_all II hII K ι P (e + 1) (Option J) (extLine ℓ) n' hP hext]
  symm
  let E : (Fin e → J) → (Fin (e + 1) → Option J) := fun w =>
    Fin.snoc (α := fun _ => Option J) (fun k => some (w k)) none
  have hEc : ∀ (w : Fin e → J) (k : Fin e), E w k.castSucc = some (w k) := fun w k => by simp [E]
  have hEl : ∀ w : Fin e → J, E w (Fin.last e) = none := fun w => by simp [E]
  refine Finset.sum_of_injOn E ?_ ?_ ?_ ?_
  · intro w _ w' _ h
    funext k
    have := congrFun h k.castSucc
    rw [hEc, hEc] at this
    exact Option.some.inj this
  · intro w _
    exact Finset.mem_coe.2 (Finset.mem_univ _)
  · intro v _ hv
    have hzero : ∏ k, (n' k (v k) : ℝ) = 0 := by
      by_cases hl : v (Fin.last e) = none
      · by_cases hs : ∀ k : Fin e, (v k.castSucc).isSome
        · exfalso
          apply hv
          refine ⟨fun k => (v k.castSucc).get (hs k), Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩
          funext k
          refine Fin.lastCases ?_ (fun k => ?_) k
          · rw [hEl, hl]
          · rw [hEc]
            simp
        · push_neg at hs
          obtain ⟨k, hk⟩ := hs
          have hk' : v k.castSucc = none := by simpa using hk
          refine Finset.prod_eq_zero (Finset.mem_univ k.castSucc) ?_
          rw [hk', hn'c]
          simp [extExp]
      · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 hl
        refine Finset.prod_eq_zero (Finset.mem_univ (Fin.last e)) ?_
        rw [hj, hn'l]
        simp [lastExp]
    rw [hzero, zero_mul]
  · intro w _
    have hlines : (fun k => extLine ℓ (E w k)) =
        (Fin.snoc (fun k => ℓ (w k)) (oneLine ι) : Fin (e + 1) → HermLine ι) := by
      funext k
      refine Fin.lastCases ?_ (fun k => ?_) k
      · simp [hEl, extLine]
      · simp [hEc, extLine]
    rw [hlines, ← pts_eq_II II hII P _ hP (fun k => hℓ _), Fin.prod_univ_castSucc]
    simp [hn'c, hn'l, hEc, hEl, extExp, lastExp]

theorem pts_perm (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (P : Ideal (MRing ι))
    {e : ℕ} (L : Fin e → HermLine ι) (σ : Equiv.Perm (Fin e)) (hP : IsArithVar P (e + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) :
    ptsIntegral P (fun k z => Real.log ((L (σ k)).h z)) (fun _ => 1) =
      ptsIntegral P (fun k z => Real.log ((L k).h z)) (fun _ => 1) := by
  let τ : Equiv.Perm (Fin (e + 1)) :=
    (finSuccEquivLast.trans (Equiv.optionCongr σ)).trans finSuccEquivLast.symm
  have hτc : ∀ k : Fin e, τ k.castSucc = (σ k).castSucc := fun k => by simp [τ]
  have hτl : τ (Fin.last e) = Fin.last e := by simp [τ]
  have hcomp : (Fin.snoc (fun k => L (σ k)) (oneLine ι) : Fin (e + 1) → HermLine ι) =
      (Fin.snoc L (oneLine ι) : Fin (e + 1) → HermLine ι) ∘ τ := by
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp [hτl]
    · simp [hτc]
  have hsm : ∀ j, IsSmoothHerm ((Fin.snoc L (oneLine ι) : Fin (e + 1) → HermLine ι) j) := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa using smooth_oneLine
    · simpa using hL k
  rw [pts_eq_II II hII P _ hP (fun k => hL _), pts_eq_II II hII P _ hP hL, hcomp]
  exact (hII.1 K ι).1 P (e + 1) _ τ hP hsm

theorem pts_deg (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (P : Ideal (MRing ι))
    {e : ℕ} (L L' : Fin e → HermLine ι) (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j))
    (hL' : ∀ j, IsSmoothHerm (L' j)) (ha : ∀ k, (L' k).a = (L k).a) :
    ptsIntegral P (fun k z => Real.log ((L' k).h z)) (fun _ => 1) =
      ptsIntegral P (fun k z => Real.log ((L k).h z)) (fun _ => 1) := by
  have hD := GlobalTheory.T.intersection_system_degree II hII.1
  have h1 : ptsIntegral P (fun k z => Real.log ((L k).h z)) (fun _ => 1) = _ :=
    hD K ι P e L 2 hP hL Nat.prime_two
  have h2 : ptsIntegral P (fun k z => Real.log ((L' k).h z)) (fun _ => 1) = _ :=
    hD K ι P e L' 2 hP hL' Nat.prime_two
  have hdeg : (fun j => (L' j).a) = fun j => (L j).a := funext ha
  rw [h1, h2, hdeg]

end GlobalTheory.CompanionTheory.Ar.Top.GeoMix

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem geo_multilin : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (J : Type) [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (n : Fin e → J → ℤ), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (ℓ j)) → (ptsIntegral P (fun k z => Real.log ((combLine ℓ (n k)).h z)) (fun _ => 1) = ∑ w : Fin e → J, (∏ k, (n k (w k) : ℝ)) * ptsIntegral P (fun k z => Real.log ((ℓ (w k)).h z)) (fun _ => 1)) ∧ (∀ (L L' : Fin e → HermLine ι) (σ : Equiv.Perm (Fin e)), (∀ k, IsSmoothHerm (L k)) → (∀ k, IsSmoothHerm (L' k)) → (∀ k, (L' k).a = (L (σ k)).a) → ptsIntegral P (fun k z => Real.log ((L' k).h z)) (fun _ => 1) = ptsIntegral P (fun k z => Real.log ((L k).h z)) (fun _ => 1)) := by
  intro II hII K _ ι _ P e J _ _ ℓ n hP hℓ
  refine ⟨GeoMix.pts_comb II hII P ℓ n hP hℓ, ?_⟩
  intro L L' σ hL hL' ha
  rw [GeoMix.pts_deg II hII P (fun k => L (σ k)) L' hP (fun k => hL _) hL' ha]
  exact GeoMix.pts_perm II hII P L σ hP hL

end GlobalTheory.CompanionTheory.Ar.Top

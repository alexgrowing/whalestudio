import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SerreVanishingCubeTotalComplexExactAtStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExactAtSectionCubeOfMulPullbackStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyEquivOfAffineCovers
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SecCubeExactAtZeroAndOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

namespace GlobalTheory.PolVanishing

variable {X : Scheme.{0}} {L : LB X}

theorem lbIso_pw_tw (hL : L.IsLB) (b N t : ℤ) :
    LBIso (AbLaw.pw L (b + N * t)) (tw (AbLaw.pw L b) (AbLaw.pw L N) t) := by
  refine lbIso_of_chartPull ⟨fun i => (i, i), fun i y hy => ⟨hy, hy⟩, fun y i j hi hj => ?_⟩
    (isLB_tw (isLB_pw hL b) (isLB_pw hL N) t)
  refine Eq.trans ?_ (gm_div (AbLaw.pw (AbLaw.pw L N) (-t)) (AbLaw.pw L b) (𝟙 X) y (i, i) (j, j)
    ⟨⟨hi, hi⟩, hj, hj⟩).symm
  change gm (𝟙 X) y (L.U i ⊓ L.U j) (L.g i j ^ (b + N * t)) =
    gm (𝟙 X) y (L.U i ⊓ L.U j) (L.g i j ^ b) * (gm (𝟙 X) y (L.U i ⊓ L.U j) ((L.g i j ^ N) ^ (-t)))⁻¹
  rw [← map_inv, ← map_mul, zpow_neg, inv_inv, ← zpow_mul, ← zpow_add]

theorem lbIso_pull_pw (μ' : X ⟶ X) (d l : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, μ'] ![d, -1])) (hα : α.IsGen) :
    LBIso ((AbLaw.pw L l).pull μ') (AbLaw.pw L (d * l)) := by
  let A := LB.LinComb L (K := Fin 2) ![𝟙 X, μ'] ![d, -1]
  have le : ∀ p : L.ι × (PUnit → L.ι), L.U p.1 ⊓ ((AbLaw.pw L l).pull μ').U p.2 ≤
      LB.wchart L (K := Fin 2) ![𝟙 X, μ'] ![p.1, p.2 PUnit.unit] := fun p y hy =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [hy.1, mem_pull.1 hy.2]
  refine gen_chartPull (A' := LB.div (AbLaw.pw L (d * l)) ((AbLaw.pw L l).pull μ')) (h := 𝟙 X)
    (A := AbLaw.pw A l) ⟨fun p => ![p.1, p.2 PUnit.unit], le, fun y p q hp hq => ?_⟩
    ⟨fun j => α.s j ^ l⟩ fun i j => ?_
  · refine (gm_div ((AbLaw.pw L l).pull μ') (AbLaw.pw L (d * l)) (𝟙 X) y p q ⟨hp, hq⟩).trans ?_
    rw [gm_pull_g (AbLaw.pw L l) μ' (𝟙 X) y p.2 q.2 hp.2 hq.2]
    refine Eq.trans ?_ ((map_zpow _ _ l).trans (congrArg (· ^ l)
      (gm_linComb L (K := Fin 2) ![𝟙 X, μ'] ![d, -1] (𝟙 X) y _ _ (le p hp) (le q hq)))).symm
    rw [Fin.prod_univ_two]
    change gm (𝟙 X) y (L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1 ^ (d * l)) *
        (gm (𝟙 X ≫ μ') y (L.U (p.2 PUnit.unit) ⊓ L.U (q.2 PUnit.unit))
          (L.g (p.2 PUnit.unit) (q.2 PUnit.unit) ^ l))⁻¹ =
      (gm (𝟙 X) y (L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1) ^ d *
        gm (𝟙 X ≫ μ') y (L.U (p.2 PUnit.unit) ⊓ L.U (q.2 PUnit.unit))
          (L.g (p.2 PUnit.unit) (q.2 PUnit.unit)) ^ (-1 : ℤ)) ^ l
    rw [map_zpow, map_zpow, mul_zpow, zpow_neg_one, inv_zpow, zpow_mul]
  · have h := congrArg (· ^ l) (hα i j)
    simp only [mul_zpow, ← map_zpow] at h
    exact h

variable {R : Type} [CommRing R] {f : X ⟶ Spec (CommRingCat.of R)}

theorem exactAt_of_lbIso {M M' : LB X} (hM : M.IsLB) (hM' : M'.IsLB) (h : LBIso M M')
    {κ : Type} [LinearOrder κ] {D : κ → X.Opens} {p : ℕ}
    (hp : (cubeComplex (secCube f M D)).ExactAt p) : (cubeComplex (secCube f M' D)).ExactAt p := by
  obtain ⟨w, hw⟩ := h
  exact hp.of_iso ((cubeFunctor κ R).mapIso (secCubeCongr f D hM hM' w hw))

theorem exactAt_of_affine_covers [IsSeparated f] {M : LB X} (hM : M.IsLB)
    {κ : Type} [LinearOrder κ] [Fintype κ] {D : κ → X.Opens}
    {κ' : Type} [LinearOrder κ'] [Fintype κ'] {D' : κ' → X.Opens}
    (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (hD' : ∀ i, IsAffineOpen (D' i)) (hc' : ⨆ i, D' i = ⊤) {p : ℕ}
    (hp : (cubeComplex (secCube f M D)).ExactAt p) : (cubeComplex (secCube f M D')).ExactAt p := by
  match p with
  | 0 => exact (secCube_exactAt_zero_and_one R X f M κ' D' hc').1
  | 1 => exact (secCube_exactAt_zero_and_one R X f M κ' D' hc').2
  | p + 2 =>
    rw [← cechComplex_exactAt_succ_iff_cube, HomologicalComplex.exactAt_iff_isZero_homology,
      ModuleCat.isZero_iff_subsingleton] at hp ⊢
    obtain ⟨e⟩ := cechLB_homology_equiv_of_affine_covers R X f M κ D κ' D' hM inferInstance
      hD hc hD' hc' (p + 1)
    exact @Equiv.subsingleton _ _ e.symm.toEquiv hp

theorem exists_forall_le_exactAt [IsNoetherianRing R] (hL : L.IsLB) {N : ℤ} (hN : 0 < N) {m : ℕ}
    {s : Fin (m + 1) → LB.Sec (AbLaw.pw L N)} (hs : VeryAmpleBy f (AbLaw.pw L N) s) :
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ p,
      (cubeComplex (secCube f (AbLaw.pw L n) (fun i => Out.nonzeroLocus (s i)))).ExactAt p := by
  choose t₀ ht₀ using fun b : ℤ =>
    GlobalTheory.T.serre_vanishing_cubeTotalComplex_exactAt R X f (AbLaw.pw L N) m s (AbLaw.pw L b) (isLB_pw hL N) (isLB_pw hL b) hs
  obtain ⟨T, hT⟩ := ((Set.finite_Ico (0 : ℤ) N).image t₀).bddAbove
  refine ⟨T * N, fun n hn p => ?_⟩
  have h₁ : t₀ (n % N) ≤ n / N :=
    (hT ⟨n % N, ⟨Int.emod_nonneg n hN.ne', Int.emod_lt_of_pos n hN⟩, rfl⟩).trans
      (Int.le_ediv_of_mul_le hN hn)
  have h₂ := exactAt_of_lbIso (isLB_tw (isLB_pw hL _) (isLB_pw hL N) _) (isLB_pw hL _)
    (lbIso_pw_tw hL (n % N) N (n / N)).symm (ht₀ (n % N) (n / N) h₁ p)
  rwa [Int.emod_add_mul_ediv] at h₂

theorem exists_le_natCast_ne_zero (K : Type) [Field K] (B : ℕ) : ∃ m : ℕ, B ≤ m ∧ (m : K) ≠ 0 := by
  by_cases h : (B : K) = 0
  · exact ⟨B + 1, Nat.le_succ B, by simp [h]⟩
  · exact ⟨B, le_rfl, h⟩

theorem exactAt_secCube_pw : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (l : ℤ) (I : Type) [LinearOrder I] [Fintype I] (D : I → P.A.left.Opens), 1 ≤ l → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ p, (cubeComplex (secCube P.A.hom (pw P.L l) D)).ExactAt p := by
  intro hLaw K _ _ P l I _ _ D hl hD hc p
  have := P.isAb.proper
  obtain ⟨N, hN, r, s, -, hs⟩ := veryAmpleBy_of_relAmple P.isLB P.ample (𝟙 P.A.left)
    (Category.id_comp _) P.isLB (lbIso_pull_id P.isLB).symm
  obtain ⟨n₀, hn₀⟩ := exists_forall_le_exactAt P.isLB (by exact_mod_cast hN) hs
  obtain ⟨m, hm, hmK⟩ := exists_le_natCast_ne_zero K n₀.toNat
  have hm₁ : 1 ≤ m := Nat.pos_of_ne_zero fun h => hmK (by simp [h])
  have hle : n₀ ≤ (m : ℤ) ^ 2 * l := by
    have h₁ : n₀ ≤ m := by omega
    have h₂ : (1 : ℤ) ≤ m := by exact_mod_cast hm₁
    nlinarith [mul_nonneg (sq_nonneg (m : ℤ)) (sub_nonneg.2 hl)]
  obtain ⟨α, hα⟩ := hLaw.mulPull _ P m
  have := (hLaw.mulN _ P m hm₁).1
  refine GlobalTheory.T.exactAt_sectionCube_of_mul_pullback hLaw K P m _ I D p hmK (isLB_pw P.isLB l) ?_
  refine exactAt_of_lbIso (isLB_pw P.isLB _) (LB.isLB_pull (isLB_pw P.isLB l) _)
    (lbIso_pull_pw _ _ l α hα).symm ?_
  refine exactAt_of_affine_covers (isLB_pw P.isLB _) (fun i => (hs.2 i).1) hs.1
    (fun i => (hD i).preimage _) ?_ (hn₀ _ hle p)
  rw [← Scheme.Hom.preimage_iSup, hc]
  rfl

end GlobalTheory.PolVanishing

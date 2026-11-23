import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FormPolyIsHomogeneousAndEval
import Development.AutomorphicSpectrum.Proofs.MetricProofs.KillNoneFormPoly
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace FlLines

section Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_integralCombination_of_mem_completedLattice {A B D : Type} [Fintype A] [Fintype B] [Fintype D] (ca : A → ℤ) (bb : A → D → ℤ) (P : B → ℤ)
    (G : D → B → ℤ) :
    ∑ k, (∑ a, ca a * bb a k) * ∑ w, P w * G k w = ∑ a, ∑ w, (P w * ca a) * ∑ k, bb a k * G k w := by
  have h1 : ∀ k, (∑ a, ca a * bb a k) * ∑ w, P w * G k w = ∑ a, ∑ w, (ca a * bb a k) * (P w * G k w) :=
    fun k => Finset.sum_mul_sum _ _ _ _
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun k _ => by ring

theorem geoNum_polar {σ : Type} [Fintype σ] (n : ℕ) (V : Ideal (MRing ι)) (c : Fin n → σ → ℤ) (b : σ → K → ℤ) :
    geoNum n V (fun r k => ∑ a, c r a * b a k) =
      ∑ w : Fin n → σ, (∏ r, c r (w r)) * geoNum n V (fun r => b (w r)) := by
  classical
  induction n generalizing V with
  | zero =>
    have h : ∀ a a' : Fin 0 → K → ℤ, geoNum 0 V a = geoNum 0 V a' := fun a a' => by
      rw [Subsingleton.elim a a']
    simp only [Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    exact h _ _
  | succ n ih =>
    by_cases hV : IsRelevant V
    · rw [← (Fin.snocEquiv (fun _ => σ)).sum_comp, Fintype.sum_prod_type]
      simp only [geoNum, dif_pos hV]
      have hin : ∀ (a : σ) (w' : Fin n → σ),
          Fin.init (fun r => b ((Fin.snocEquiv (fun _ => σ)) (a, w') r)) = fun r => b (w' r) := by
        intro a w'
        funext r
        simp [Fin.init, Fin.snocEquiv]
      have hla : ∀ (a : σ) (w' : Fin n → σ), (Fin.snocEquiv (fun _ => σ)) (a, w') (Fin.last n) = a := by
        intro a w'
        simp [Fin.snocEquiv]
      have hca : ∀ (a : σ) (w' : Fin n → σ) (r : Fin n),
          (Fin.snocEquiv (fun _ => σ)) (a, w') r.castSucc = w' r := by
        intro a w' r
        simp [Fin.snocEquiv]
      have hi2 : Fin.init (fun r k => ∑ a, c r a * b a k) =
          fun (r : Fin n) k => ∑ a, c r.castSucc a * b a k := by
        funext r k
        simp [Fin.init]
      simp only [hin, hla, Fin.prod_univ_castSucc, hca, hi2]
      have e : ∀ (k : K) (f : Ideal (MRing ι) → ℤ),
          ∑ᶠ W ∈ divSupp V (X ⟨k, (hV k).choose⟩ : MRing ι), f W =
            ∑ W ∈ (divSupp_finite V (X ⟨k, (hV k).choose⟩ : MRing ι)).toFinset, f W :=
        fun k f => finsum_mem_eq_finite_toFinset_sum f (divSupp_finite _ _)
      simp only [e]
      simp only [ih _ (fun r => c r.castSucc)]
      rw [← exists_integralCombination_of_mem_completedLattice (fun a => c (Fin.last n) a) b (fun w' : Fin n → σ => ∏ r, c r.castSucc (w' r))]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun W _ => ?_
      ring
    · have e : ∀ a, geoNum (n + 1) V a = 0 := fun a => by simp only [geoNum, dif_neg hV]
      simp [e]

theorem degSum_polar {σ : Type} [Fintype σ] (e : ℕ) (S : Set (Ideal (MRing ι))) (hS : S.Finite)
    (m : Ideal (MRing ι) → ℝ) (lam : σ → ℤ) (b : σ → K → ℤ) :
    ∑ w : Fin e → σ, (∏ r, (lam (w r) : ℝ)) * ∑ᶠ V ∈ S, m V * (geoNum e V (fun r => b (w r)) : ℝ) =
      ∑ᶠ V ∈ S, m V * (geoNum e V (fun _ k => ∑ a, lam a * b a k) : ℝ) := by
  have e' : ∀ f : Ideal (MRing ι) → ℝ, ∑ᶠ V ∈ S, f V = ∑ V ∈ hS.toFinset, f V :=
    fun f => finsum_mem_eq_finite_toFinset_sum f hS
  have hp : ∀ V : Ideal (MRing ι), geoNum e V (fun _ k => ∑ a, lam a * b a k) =
      ∑ w : Fin e → σ, (∏ r, lam (w r)) * geoNum e V (fun r => b (w r)) :=
    fun V => geoNum_polar e V (fun _ => lam) b
  simp only [e', hp]
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun V _ => Finset.sum_congr rfl fun w _ => ?_
  ring

end Geo

section Wt

variable {Ψ : Type} {N : ℕ}

def gapZ (lam : Ψ × Fin N → ℤ) (p : Ψ × Fin N) : ℤ :=
  lam p - if h : (p.2 : ℕ) + 1 < N then lam (p.1, ⟨(p.2 : ℕ) + 1, h⟩) else 0

theorem gap_cast (lam : Ψ × Fin N → ℤ) (p : Ψ × Fin N) :
    gap (fun q => (lam q : ℝ)) p = (gapZ lam p : ℝ) := by
  unfold gap gapX gapZ
  split_ifs <;> simp

theorem formPoly_eq_toWt [Fintype Ψ] (n : ℕ) (ax ay : (Fin n → Ψ × Fin N) → ℝ)
    (h : ∀ lam : Ψ × Fin N → ℤ, ∑ w, (∏ r, (lam (w r) : ℝ)) * ax w = ∑ w, (∏ r, (gapZ lam (w r) : ℝ)) * ay w) :
    formPoly n ax = toWt (formPoly n ay) := by
  refine MvPolynomial.funext_set (fun _ => Set.range (fun z : ℤ => (z : ℝ)))
    (fun _ => Set.infinite_range_of_injective Int.cast_injective) ?_
  intro x hx
  choose lam hlam using fun i => hx i (Set.mem_univ i)
  have hxl : x = fun p => (lam p : ℝ) := funext fun p => (hlam p).symm
  rw [hxl, eval_toWt_gap, (formPoly_isHomogeneous_and_eval _ n ax).2, (formPoly_isHomogeneous_and_eval _ n ay).2]
  simp only [gap_cast]
  simpa only [mul_comm] using h lam

end Wt

section Flag

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

def yDeg (p : Ψ × Fin N) : FlBlock Ψ N → ℤ :=
  fun q => if q.1 = p.1 ∧ (q.2 : ℕ) = p.2 then 1 else 0

variable {Ψ N}

theorem deg_abel (lam : Ψ × Fin N → ℤ) (q : FlBlock Ψ N) :
    ∑ p, lam p * xDeg Ψ N p q = ∑ p, gapZ lam p * yDeg Ψ N p q := by
  classical
  obtain ⟨τ, i⟩ := q
  have hi : (i : ℕ) + 1 < N := by have := i.2; omega
  have hi0 : (i : ℕ) < N := by omega
  have hx : ∀ p : Ψ × Fin N, xDeg Ψ N p (τ, i) =
      (if p = (τ, ⟨(i : ℕ), hi0⟩) then 1 else 0) - (if p = (τ, ⟨(i : ℕ) + 1, hi⟩) then 1 else 0) := by
    rintro ⟨τ', a⟩
    by_cases ht : τ = τ'
    · subst ht
      simp [xDeg, Fin.ext_iff, eq_comm]
    · simp [xDeg, ht, Ne.symm ht]
  have hy : ∀ p : Ψ × Fin N, yDeg Ψ N p (τ, i) = if p = (τ, ⟨(i : ℕ), hi0⟩) then 1 else 0 := by
    rintro ⟨τ', a⟩
    by_cases ht : τ = τ'
    · subst ht
      simp [yDeg, Fin.ext_iff, eq_comm]
    · simp [yDeg, ht, Ne.symm ht]
  simp only [hx, hy, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp [gapZ, hi]

theorem deg_abel_smul (lam : Ψ × Fin N → ℤ) :
    ∑ p, lam p • xDeg Ψ N p = ∑ p, gapZ lam p • yDeg Ψ N p := by
  funext q
  simpa [Finset.sum_apply] using deg_abel lam q

end Flag

end FlLines

open FlLines

theorem flLines_polys : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) → hFlPoly Ψ N II = toWt (formPoly (antisymDegree Ψ N + 1) fun w => II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (antisymDegree Ψ N + 1) fun r => yLineFl Ψ N (w r)) ∧ degFlPoly Ψ N = toWt (formPoly (antisymDegree Ψ N) fun w => ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) fun _ => 1) := by
  intro hIn II hII Ψ _ _ _ N _ hP
  have hI := hII.1 (FlBlock Ψ N) (FlIdx Ψ N)
  refine ⟨formPoly_eq_toWt _ _ _ fun lam => ?_, formPoly_eq_toWt _ _ _ fun lam => ?_⟩
  · have h1 := FlagHeightMultilinear.I_fsHerm_sum hI hP (fun _ => lam) (xDeg Ψ N)
    have h2 := FlagHeightMultilinear.I_fsHerm_sum hI hP (fun _ => gapZ lam) (yDeg Ψ N)
    rw [deg_abel_smul lam, h2] at h1
    exact h1.symm
  · set S : Set (Ideal (MRing (FlIdx Ψ N))) := divSupp (PFl Ψ N) (C (((2 : ℕ) : ℤ))) with hSdef
    have hS : S.Finite := divSupp_finite _ _
    set m : Ideal (MRing (FlIdx Ψ N)) → ℝ :=
      fun V => (multAt (PFl Ψ N ⊔ Ideal.span {C (((2 : ℕ) : ℤ))}) V : ℝ) with hm
    have hD : ∀ L : Fin (antisymDegree Ψ N) → HermLine (FlIdx Ψ N), (∀ j, IsSmoothHerm (L j)) →
        ptsIntegral (PFl Ψ N) (pot L) (fun _ => 1) = ∑ᶠ V ∈ S, m V * (geoNum _ V (fun j => (L j).a) : ℝ) :=
      fun L hL => hIn.degree _ _ _ _ L 2 hP hL Nat.prime_two
    have hsm : ∀ a : FlBlock Ψ N → ℤ, IsSmoothHerm (fsHerm (FlIdx Ψ N) a) :=
      FlagHeightMultilinear.isSmoothHerm_fsHerm
    have h1 := degSum_polar (antisymDegree Ψ N) S hS m lam (xDeg Ψ N)
    have h2 := degSum_polar (antisymDegree Ψ N) S hS m (gapZ lam) (yDeg Ψ N)
    have hv : (fun (_ : Fin (antisymDegree Ψ N)) k => ∑ a, lam a * xDeg Ψ N a k) =
        fun _ k => ∑ a, gapZ lam a * yDeg Ψ N a k := by
      funext _ k
      exact deg_abel lam k
    rw [hv, ← h2] at h1
    have ex : ∀ w : Fin (antisymDegree Ψ N) → Ψ × Fin N,
        ptsIntegral (PFl Ψ N) (pot fun r => xLine Ψ N (w r)) (fun _ => 1) =
          ∑ᶠ V ∈ S, m V * (geoNum _ V (fun r => xDeg Ψ N (w r)) : ℝ) :=
      fun w => hD _ fun _ => hsm _
    have ey : ∀ w : Fin (antisymDegree Ψ N) → Ψ × Fin N,
        ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) (fun _ => 1) =
          ∑ᶠ V ∈ S, m V * (geoNum _ V (fun r => yDeg Ψ N (w r)) : ℝ) :=
      fun w => hD _ fun _ => hsm _
    simp only [ex, ey]
    exact h1

end GlobalTheory.CompanionTheory.Ar.PB

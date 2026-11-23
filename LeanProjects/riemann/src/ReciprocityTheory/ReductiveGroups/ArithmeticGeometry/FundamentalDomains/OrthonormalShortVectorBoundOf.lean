import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ReducedLatticeShortBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.GramSchmidtEigenframe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnitaryFixingIsotropicPlane
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnitaryComplementMoveOfIsotropic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FinrankEqTwoMulHalfDegree

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

theorem complexStructure_add (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.Jt x τ (u + v) = X.Jt x τ u + X.Jt x τ v := by
  have hh : ∀ w, hermC τ.1 X.Gm (u + v) w = hermC τ.1 X.Gm u w + hermC τ.1 X.Gm v w := by
    intro w
    simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hp : X.ppos x τ (u + v) = X.ppos x τ u + X.ppos x τ v := by
    simp only [ReciprocityTheory.ChartRestriction.G.FD.Data.ppos, hh, add_mul, Finset.sum_add_distrib, add_smul]
  simp only [ReciprocityTheory.ChartRestriction.G.FD.Data.Jt, hp, smul_add, smul_sub]
  abel

theorem complexStructure_smul (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (u : Fin r → ℂ) :
    X.Jt x τ (c • u) = c • X.Jt x τ u := by
  have hh : ∀ w, hermC τ.1 X.Gm (c • u) w = c * hermC τ.1 X.Gm u w := by
    intro w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hp : X.ppos x τ (c • u) = c • X.ppos x τ u := by
    simp only [ReciprocityTheory.ChartRestriction.G.FD.Data.ppos, hh, Finset.smul_sum, smul_smul, Finset.mul_sum, mul_assoc]
  simp only [ReciprocityTheory.ChartRestriction.G.FD.Data.Jt, hp]
  module

theorem eigenspan_perp_isotropic {z0 : Frame X.Ψ r} {ξ : Fin r → E} {f : X.Ψ → Fin (r - 2) → Fin r → ℂ}
    (hf : X.UBasis z0 ξ f) (τ : X.Ψ) (s : Set (Fin (r - 2))) (σ : ℂ)
    (hs : ∀ k ∈ s, (if (k : ℕ) < X.p0 - 1 then I else -I) = σ) (v : Fin r → ℂ)
    (hv : v ∈ Submodule.span ℂ (f τ '' s)) :
    hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 ∧ hermC τ.1 X.Gm (X.Jt z0 τ v) (emb τ.1 ξ) = 0 ∧
      X.Jt z0 τ v = σ • v := by
  have hadd : ∀ a b w, hermC τ.1 X.Gm (a + b) w = hermC τ.1 X.Gm a w + hermC τ.1 X.Gm b w := by
    intro a b w
    simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hsm : ∀ (c : ℂ) a w, hermC τ.1 X.Gm (c • a) w = c * hermC τ.1 X.Gm a w := by
    intro c a w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hJ0 : X.Jt z0 τ 0 = 0 := by simpa using complexStructure_smul X z0 τ 0 0
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.UBasis at hf
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨k, hk, rfl⟩ := hw
    exact ⟨((hf τ).1 k).1, ((hf τ).1 k).2, by rw [(hf τ).2.1 k, hs k hk]⟩
  | zero => exact ⟨by simp [hermC], by rw [hJ0]; simp [hermC], by rw [hJ0, smul_zero]⟩
  | add a b _ _ ha hb =>
    exact ⟨by rw [hadd, ha.1, hb.1, add_zero], by rw [complexStructure_add, hadd, ha.2.1, hb.2.1, add_zero],
      by rw [complexStructure_add, ha.2.2, hb.2.2, smul_add]⟩
  | smul c a _ ha =>
    exact ⟨by rw [hsm, ha.1, mul_zero], by rw [complexStructure_smul, hsm, ha.2.1, mul_zero],
      by rw [complexStructure_smul, ha.2.2, smul_comm]⟩

end Data

private lemma d4ep0_pos_and_le_one (g d f NA NC c1 w : ℝ) (hg : 0 < g) (hd : 0 < d) (hf : 1 ≤ f) (hNC : 0 < NC)
    (hNA : 0 ≤ NA) (hc1 : 0 < c1) (hw : 1 ≤ w) :
    0 < flowEpsilonBound g d f NA NC c1 w ∧ flowEpsilonBound g d f NA NC c1 w ≤ 1 := by
  unfold flowEpsilonBound
  dsimp only
  refine ⟨lt_min one_pos ?_, min_le_left _ _⟩
  have hH : 0 ≤ NC ^ 2 * (2 + 4 * f ^ 4 * (d ^ (1 / (2 * f))) ^ 2 * NA ^ 2) := by positivity
  have hK : 1 ≤ 1 + g * d ^ 2 * (NC ^ 2 * (2 + 4 * f ^ 4 * (d ^ (1 / (2 * f))) ^ 2 * NA ^ 2)) *
      (2 * c1 + 1) := by
    have : 0 ≤ g * d ^ 2 * (NC ^ 2 * (2 + 4 * f ^ 4 * (d ^ (1 / (2 * f))) ^ 2 * NA ^ 2)) * (2 * c1 + 1) := by
      apply mul_nonneg (mul_nonneg (mul_pos hg (pow_pos hd 2)).le hH)
      linarith
    linarith
  have hL : 0 ≤ Real.log (2 * (1 + g * d ^ 2 * (NC ^ 2 * (2 + 4 * f ^ 4 * (d ^ (1 / (2 * f))) ^ 2 * NA ^ 2)) *
      (2 * c1 + 1)) * (4 * f)) := Real.log_nonneg (by nlinarith)
  have h4 : 0 ≤ 4 * f * Real.log (2 * (1 + g * d ^ 2 * (NC ^ 2 * (2 + 4 * f ^ 4 * (d ^ (1 / (2 * f))) ^ 2 * NA ^ 2)) *
      (2 * c1 + 1)) * (4 * f)) := mul_nonneg (by linarith) hL
  apply div_pos (pow_pos (by linarith) 2)
  apply mul_pos (mul_pos (mul_pos (pow_pos (mul_pos hg (pow_pos hd 2)) 2) (pow_pos hNC 2)) hc1)
  linarith

theorem epsilonZero_pos_le_one {r : ℕ} (X : DataX E r) (c1 w : ℝ) (hc1 : 0 < c1) (hw1 : 1 ≤ w) :
    0 < flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ∧ flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ≤ 1 := by
  have hd : 0 < dE E := by
    unfold dE
    exact abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero E))
  have hf : (1 : ℝ) ≤ (fdeg E : ℝ) := by
    have h1 : Module.finrank ℚ E = 2 * NumberField.InfinitePlace.nrComplexPlaces E :=
      NumberField.IsTotallyComplex.finrank E
    have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
    have h3 : 1 ≤ fdeg E := by
      unfold fdeg
      omega
    exact_mod_cast h3
  exact d4ep0_pos_and_le_one _ _ _ _ _ _ _ (Nat.cast_pos.mpr X.g_pos) hd hf (Nat.cast_pos.mpr X.NC_pos) (Nat.cast_nonneg _) hc1 hw1

theorem orthonormalShortVectorBound_of (hD4 : ShortVectorBound (E := E)) (hD5 : CoveringRadiusStatement) : OrthonormalShortVectorBound (E := E) := by
  intro r X la P ξ ν c1 w z0 hH x0 hx0 hortho hflag
  have hξ : X.IsIso ξ := hH.2.2.1
  have hc1 : 0 < c1 := hH.2.2.2.1
  have hw1 : 1 ≤ w := hH.2.2.2.2.2.2.1
  have hz : z0 ∈ X.dom := hH.2.2.2.2.2.2.2.2.2.1.1
  obtain ⟨hep, hep1⟩ := epsilonZero_pos_le_one X c1 w hc1 hw1
  have hrh : 0 < d6rh c1 w := by unfold d6rh; positivity
  have hrh1 : d6rh c1 w ≤ 1 := by
    unfold d6rh
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hD4' := hD4 r X la P ξ ν c1 w z0 hH
  obtain ⟨f, hf⟩ := exists_unitary_basis_same_flag r X ξ z0 x0 hξ hz hx0 hortho hflag
  obtain ⟨β, S, LB, Q, hβ, hβind, hβspan, hS, hLB, hLat, hSD, hQ, hSQ, hQf⟩ := exists_perp_hermitian_reduction r X ξ z0 f hξ hz hf
  obtain ⟨lam, hl1, hl2, hl3, hl4, hl5, hl6, hYind, hYU, hYorth, hYpos, hYneg, hYgraph⟩ :=
    reducedLattice_short_bound hD5 r X ξ z0 f β S LB Q _ _ hξ hz hf hβ hβind hβspan hS hLB hLat hSD hQ hSQ hQf hep hep1 hrh
      hrh1 hD4'
  obtain ⟨h1, hU, hI, hUz, hmap, hpre⟩ := gramSchmidt_eigenframe r X ξ z0 f (fun τ j => X.ucomp z0 ξ (X.embV (lam j)) τ) hξ hz hf
    hYind hYU hYorth hYpos hYneg
  obtain ⟨Z1, hfl, hZ⟩ := unitary_fixing_isotropic_plane r X ξ z0 x0 f h1 (d6rh c1 w / 120) hξ hz hx0 hortho hflag hf (by positivity) hU hI
    hUz (fun τ v hv c hc => hYgraph τ c (hc ▸ hmap τ v hv))
  obtain ⟨hdom1, haproj, -, hJ⟩ := unitaryComplementMove r X.toData ξ hξ z0 hz h1 hU hI hUz

  have hJsplit : ∀ j : Fin (r - 2),
      X.Jz (X.lmulC h1 z0) (X.ucomp (X.lmulC h1 z0) ξ (X.embV (lam j))) =
        (if (j : ℕ) < X.p0 - 1 then I else -I) • X.ucomp (X.lmulC h1 z0) ξ (X.embV (lam j)) := by
    intro j
    choose u hu hhu using hpre
    have hmem : ∀ τ, X.toData.Jt z0 τ (u τ j) = (if (j : ℕ) < X.p0 - 1 then I else -I) • u τ j ∧
        hermC τ.1 X.Gm (u τ j) (Data.emb τ.1 ξ) = 0 ∧
        hermC τ.1 X.Gm (X.toData.Jt z0 τ (u τ j)) (Data.emb τ.1 ξ) = 0 := by
      intro τ
      have := X.toData.eigenspan_perp_isotropic hf τ _ (if (j : ℕ) < X.p0 - 1 then I else -I) (fun k hk => by
        simp only [Set.mem_setOf_eq] at hk
        by_cases hj : (j : ℕ) < X.p0 - 1
        · rw [if_pos (hk.2 hj), if_pos hj]
        · rw [if_neg (fun h => hj (hk.1 h)), if_neg hj]) (u τ j) (hu τ j)
      exact ⟨this.2.2, this.1, this.2.1⟩
    have huU : (fun τ => u τ j) ∈ X.Uz z0 ξ := ⟨fun τ => (hmem τ).2.1, fun τ => (hmem τ).2.2⟩
    have hIp : X.embV (lam j) ∈ X.Iperp ξ := fun τ => by
      rw [Data.embV, ← emb_herm, (hl1 j).2, map_zero]
    have hY : X.ucomp (X.lmulC h1 z0) ξ (X.embV (lam j)) = X.applyV h1 (fun τ => u τ j) := by
      funext τ
      show (X.embV (lam j) - X.aproj (X.lmulC h1 z0) ξ (X.embV (lam j))) τ = (h1 τ) *ᵥ (u τ j)
      rw [haproj _ hIp, hhu τ j]
      rfl
    rw [hY, hJ _ huU]
    funext τ
    simp only [Data.applyV, Data.Jz, Pi.smul_apply]
    have h2 := (hmem τ).1
    simp only [Data.Jt] at h2
    rw [h2, Matrix.mulVec_smul]
  refine ⟨lam, h1, Z1, hU, hI, hUz, ⟨hl1, hl2, hl3, fun j hj => ⟨hl4 j hj, ?_⟩, fun j hj => ⟨hl5 j hj, ?_⟩, hl6⟩,
    hfl, ?_⟩
  · rw [hJsplit j, if_pos hj]
  · rw [hJsplit j, if_neg (by omega), neg_smul]
  · have : d6rh c1 w / 120 ≤ d6rh c1 w / 100 := by
      apply div_le_div_of_nonneg_left hrh.le (by norm_num) (by norm_num)
    linarith

end

end ReciprocityTheory.ChartRestriction.G.FD

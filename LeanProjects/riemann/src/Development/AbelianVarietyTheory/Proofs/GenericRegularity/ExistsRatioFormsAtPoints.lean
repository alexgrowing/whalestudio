import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
import ReciprocityTheory.SemistableReduction.AlgAll
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

namespace GlobalTheory.ConstRatio

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
  {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

abbrev Deg (wL : WeightFamilies.Wt D j) (m : ℕ) : Submodule B.KO X.Forms :=
  LinearMap.range (X.inc (addL (wt0 D j) wL m))

theorem deg_mul {m n : ℕ} {x y : X.Forms} (hx : x ∈ Deg X wL m) (hy : y ∈ Deg X wL n) :
    x * y ∈ Deg X wL (m + n) := by
  obtain ⟨F, rfl⟩ := hx
  obtain ⟨G, rfl⟩ := hy
  have h : X.inc _ F * X.inc _ G ∈
      LinearMap.range (X.inc (wadd (addL (wt0 D j) wL m) (addL (wt0 D j) wL n))) := by
    obtain ⟨H, hH⟩ := X.inc_mul _ _ F G
    exact ⟨H, hH.symm⟩
  rwa [wadd_addL_addL, zero_weight_add] at h

theorem deg_one (F : B.Cusp j wL) : X.inc wL F ∈ Deg X wL 1 := by
  have h : X.inc wL F ∈ LinearMap.range (X.inc wL) := ⟨F, rfl⟩
  unfold Deg
  rwa [add_zero_weight_one_eq]

theorem deg_wsmul (k : ℕ) (g : B.Cusp j (wsmul k wL)) : X.inc (wsmul k wL) g ∈ Deg X wL k := by
  have h : X.inc _ g ∈ LinearMap.range (X.inc (wsmul k wL)) := ⟨g, rfl⟩
  unfold Deg
  rwa [addL, zero_weight_add]

theorem deg_mul_pow {m : ℕ} {y x : X.Forms} (hy : y ∈ Deg X wL m) (hx : x ∈ Deg X wL 1) (e : ℕ) :
    y * x ^ e ∈ Deg X wL (m + e) := by
  induction e with
  | zero => simpa using hy
  | succ e ih =>
    rw [pow_succ, ← mul_assoc, ← add_assoc]
    exact deg_mul X ih hx

theorem deg_mul_prod (d : Fin N →₀ ℕ) {m : ℕ} {y : X.Forms} (hy : y ∈ Deg X wL m) (s : Finset (Fin N)) :
    y * ∏ i ∈ s, X.inc wL (w i) ^ d i ∈ Deg X wL (m + ∑ i ∈ s, d i) := by
  classical
  refine Finset.induction_on s (by simpa using hy) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  have e1 : y * (X.inc wL (w a) ^ d a * ∏ i ∈ s, X.inc wL (w i) ^ d i) =
      (y * ∏ i ∈ s, X.inc wL (w i) ^ d i) * X.inc wL (w a) ^ d a := by ring
  have e2 : m + (d a + ∑ i ∈ s, d i) = m + ∑ i ∈ s, d i + d a := by ring
  rw [e1, e2]
  exact deg_mul_pow X ih (deg_one X (w a)) (d a)

theorem deg_mul_aeval {k : ℕ} (Pw : MvPolynomial (Fin N) B.KO) (hPw : Pw.IsHomogeneous k) {m : ℕ} {y : X.Forms}
    (hy : y ∈ Deg X wL m) :
    y * MvPolynomial.aeval (fun i => X.inc wL (w i)) Pw ∈ Deg X wL (m + k) := by
  classical
  rw [Pw.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, mul_left_comm, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hdeg : ∑ i ∈ d.support, d i = k := by
    have := hPw (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have h := deg_mul_prod X w d hy d.support
  rw [hdeg] at h
  exact h

theorem ratio_large {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (hB : CurveLoc.BirAt X N w gF) (k0 : Fin N) (hk0 : gF (X.inc wL (w k0)) ≠ 0) (a : Ω) :
    ∃ k : ℕ, ∀ m, k < m → ∃ n d : B.Cusp j (addL (wt0 D j) wL m),
      gF (X.inc _ d) ≠ 0 ∧ gF (X.inc _ n) = a * gF (X.inc _ d) := by
  obtain ⟨k, g, Pw, hPw, hne, he⟩ := hB a
  refine ⟨k, fun m hm => ?_⟩
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hm
  have h1 : X.inc wL (w k0) * X.inc wL (w k0) ^ e ∈ Deg X wL (1 + e) :=
    deg_mul_pow X (deg_one X (w k0)) (deg_one X (w k0)) e
  have hd := deg_mul_aeval X w Pw hPw h1
  have hn := deg_mul X h1 (deg_wsmul X k g)
  have e1 : 1 + e + k = k + e + 1 := by ring
  rw [e1] at hd hn
  obtain ⟨d, hd⟩ := hd
  obtain ⟨n, hn⟩ := hn
  have hPv : gF (MvPolynomial.aeval (fun i => X.inc wL (w i)) Pw) =
      MvPolynomial.aeval (fun i => gF (X.inc wL (w i))) Pw :=
    MvPolynomial.comp_aeval_apply (fun i => X.inc wL (w i)) gF Pw
  refine ⟨n, d, ?_, ?_⟩
  · rw [hd, map_mul, map_mul, map_pow, hPv]
    exact mul_ne_zero (mul_ne_zero hk0 (pow_ne_zero _ hk0)) hne
  · rw [hd, hn, map_mul, map_mul gF _ (MvPolynomial.aeval _ Pw), hPv, ← he]
    ring

end GlobalTheory.ConstRatio

namespace GlobalTheory

open ConstRatio in

theorem exists_ratio_forms_at_points : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (Pt : Type) [Finite Pt] (U : Pt → Type) [∀ ζ, Field (U ζ)] (ev : ∀ ζ, Rp X la N →+* U ζ) (ι : Type) (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z) (Zc : Pt → ι) (jz : ∀ ζ, Ω (Zc ζ) →+* U ζ), (∀ ζ, ∃ k, ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc wL (w k))) ≠ 0) → (∀ ζ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), gF (Zc ζ) (X.inc u F) = 0 → ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F)) = 0) → (∀ ζ (u : WeightFamilies.Wt D j) (F F' : B.Cusp j u), jz ζ (gF (Zc ζ) (X.inc u F)) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F')) = jz ζ (gF (Zc ζ) (X.inc u F')) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F))) → (∀ Z, CurveLoc.BirAt X N w (gF Z)) → (∀ Z (u : WeightFamilies.Wt D j) (F : B.Cusp j u), ∃ F' : B.Cusp j u, gF Z (X.inc u F') = gF Z (X.inc u F) ∧ ∀ Z', Z' ≠ Z → gF Z' (X.inc u F') = 0) → ∀ a : ∀ Z, Ω Z, ∃ (k : ℕ) (F F' : B.Cusp j (addL (wt0 D j) wL k)), ∀ ζ, ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F')) ≠ 0 ∧ ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F)) = jz ζ (a (Zc ζ)) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F')) := by
  intro D B P j X la N wL w Pt _ U _ ev ι Ω _ _ gF Zc jz h1 h2 h3 hB hs a
  classical
  haveI := Fintype.ofFinite Pt
  choose k0 hk0 using h1
  have hg0 : ∀ ζ, gF (Zc ζ) (X.inc wL (w (k0 ζ))) ≠ 0 := fun ζ h => hk0 ζ (h2 ζ wL _ h)
  choose K hK using fun ζ => ratio_large X w (gF (Zc ζ)) (hB _) (k0 ζ) (hg0 ζ) (a _)
  set M : ℕ := Finset.univ.sup K with hM
  have hlt : ∀ ζ, K ζ < 1 + M := fun ζ => by
    have : K ζ ≤ M := Finset.le_sup (f := K) (Finset.mem_univ ζ)
    omega
  have key : ∀ Z, ∃ n d : B.Cusp j (addL (wt0 D j) wL (1 + M)),
      (∀ Z', Z' ≠ Z → gF Z' (X.inc _ n) = 0 ∧ gF Z' (X.inc _ d) = 0) ∧
      (Z ∈ Set.range Zc → gF Z (X.inc _ d) ≠ 0 ∧ gF Z (X.inc _ n) = a Z * gF Z (X.inc _ d)) := by
    intro Z
    by_cases hZ : Z ∈ Set.range Zc
    · obtain ⟨ζ, rfl⟩ := hZ
      obtain ⟨n, d, hd, hn⟩ := hK ζ _ (hlt ζ)
      obtain ⟨n', hn1, hn2⟩ := hs (Zc ζ) _ n
      obtain ⟨d', hd1, hd2⟩ := hs (Zc ζ) _ d
      refine ⟨n', d', fun Z' h => ⟨hn2 Z' h, hd2 Z' h⟩, fun _ => ?_⟩
      rw [hn1, hd1]
      exact ⟨hd, hn⟩
    · exact ⟨0, 0, fun Z' _ => by simp, fun h => absurd h hZ⟩
  choose n d hoff hon using key
  have hsum : ∀ (f : ι → B.Cusp j (addL (wt0 D j) wL (1 + M))),
      (∀ Z Z', Z' ≠ Z → gF Z' (X.inc _ (f Z)) = 0) → ∀ ζ,
      gF (Zc ζ) (X.inc _ (∑ Z ∈ Finset.univ.image Zc, f Z)) = gF (Zc ζ) (X.inc _ (f (Zc ζ))) := by
    intro f hf ζ
    rw [map_sum, map_sum]
    exact Finset.sum_eq_single_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ ζ))
      fun Z _ h => hf Z _ h.symm
  refine ⟨1 + M, ∑ Z ∈ Finset.univ.image Zc, n Z, ∑ Z ∈ Finset.univ.image Zc, d Z, fun ζ => ?_⟩
  have hn := hsum n (fun Z Z' h => (hoff Z Z' h).1) ζ
  have hd := hsum d (fun Z Z' h => (hoff Z Z' h).2) ζ
  obtain ⟨o1, o2⟩ := hon (Zc ζ) ⟨ζ, rfl⟩
  rw [← hd] at o1
  rw [← hd, ← hn] at o2
  generalize (∑ Z ∈ Finset.univ.image Zc, n Z) = F at o2 ⊢
  generalize (∑ Z ∈ Finset.univ.image Zc, d Z) = F' at o1 o2 ⊢
  have hj : jz ζ (gF (Zc ζ) (X.inc _ F')) ≠ 0 := (map_ne_zero _).2 o1
  constructor
  · obtain ⟨G, hG⟩ := deg_mul_pow X (deg_one X (w (k0 ζ))) (deg_one X (w (k0 ζ))) M
    have hev : ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ G)) ≠ 0 := by
      rw [hG, map_mul, map_mul, map_pow, map_pow]
      exact mul_ne_zero (hk0 ζ) (pow_ne_zero _ (hk0 ζ))
    intro h0
    have h := h3 ζ _ F' G
    rw [h0, mul_zero] at h
    exact mul_ne_zero hj hev h
  · have h := h3 ζ _ F F'
    rw [o2, map_mul] at h
    apply mul_left_cancel₀ hj
    rw [← h]
    ring

end GlobalTheory

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDerivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionIsLieActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactTypeInCompactStableSubmoduleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VoganNormSqHolomorphicLowestKTypeSubRootLtStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.Lowering

open Formalism.REAL

variable {n : ℕ}

lemma sum_root_mul (a b : Fin n) (N : Fin n → ℝ) : ∑ i, root a b i * N i = N a - N b := by
  simp [root, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]

lemma sum_cone_mul (co : Fin n → Fin n → ℕ) (N : Fin n → ℝ) :
    ∑ k, (∑ i, ∑ j, (co i j : ℝ) • root i j) k * N k = ∑ i, ∑ j, (co i j : ℝ) * (N i - N j) := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← sum_root_mul i j N, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => by ring

lemma cone_nonneg (ε : Fin n → Bool) (co : Fin n → Fin n → ℕ) (hco : ∀ a b, co a b ≠ 0 → a < b ∧ ε a = ε b)
    (N : Fin n → ℝ) (hN : ∀ i j, i < j → ε i = ε j → N j ≤ N i) :
    0 ≤ ∑ k, (∑ i, ∑ j, (co i j : ℝ) • root i j) k * N k := by
  rw [sum_cone_mul]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  by_cases h : co i j = 0
  · simp [h]
  · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 (hN i j (hco i j h).1 (hco i j h).2))

lemma rhoC_anti (ε : Fin n → Bool) (i j : Fin n) (hij : i < j) (h : ε i = ε j) : rhoC ε j ≤ rhoC ε i := by
  unfold rhoC
  have h1 : (Finset.univ.filter fun b => j < b ∧ ε b = ε j).card ≤
      (Finset.univ.filter fun b => i < b ∧ ε b = ε i).card :=
    Finset.card_le_card fun b hb => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact ⟨hij.trans hb.1, hb.2.trans h.symm⟩
  have h2 : (Finset.univ.filter fun b => b < i ∧ ε b = ε i).card ≤
      (Finset.univ.filter fun b => b < j ∧ ε b = ε j).card :=
    Finset.card_le_card fun b hb => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact ⟨hb.1.trans hij, hb.2.trans h⟩
  have h1' : ((Finset.univ.filter fun b => j < b ∧ ε b = ε j).card : ℝ) ≤
      (Finset.univ.filter fun b => i < b ∧ ε b = ε i).card := by exact_mod_cast h1
  have h2' : ((Finset.univ.filter fun b => b < i ∧ ε b = ε i).card : ℝ) ≤
      (Finset.univ.filter fun b => b < j ∧ ε b = ε j).card := by exact_mod_cast h2
  linarith

lemma vNormSq_lt (p : ℕ) (ε : Fin n → Bool) (hε : ∀ a, ε a = decide ((a : ℕ) < p)) (Λ μ : Fin n → ℝ)
    (hΛ : ∀ i j, i < j → ε i = ε j → Λ j ≤ Λ i) (hμ : ∀ i j, i < j → ε i = ε j → μ j ≤ μ i)
    (hV : ∀ a c : Fin n, ε a = true → ε c = false → vNormSq ε (Λ - root a c) < vNormSq ε Λ)
    (a c : Fin n) (ha : ε a = true) (hc : ε c = false) (hd : CDom ε (μ + root a c) Λ) :
    vNormSq ε μ < vNormSq ε Λ := by
  obtain ⟨co, hco, hd⟩ := hd
  have hap : (a : ℕ) < p := by simpa [hε a] using ha
  have hcp : p ≤ (c : ℕ) := by simpa [hε c] using hc
  let a0 : Fin n := ⟨p - 1, by have := c.2; omega⟩
  let c0 : Fin n := ⟨p, by have := c.2; omega⟩
  have ha0v : (a0 : ℕ) = p - 1 := rfl
  have hc0v : (c0 : ℕ) = p := rfl
  have ha0 : ε a0 = true := by rw [hε]; simp only [decide_eq_true_eq]; omega
  have hc0 : ε c0 = false := by rw [hε]; simp only [decide_eq_false_iff_not]; omega
  set L : Fin n → ℝ := Λ + (2 : ℝ) • rhoC ε with hL
  set M : Fin n → ℝ := μ + (2 : ℝ) • rhoC ε with hM
  set γ : Fin n → ℝ := ∑ i, ∑ j, (co i j : ℝ) • root i j with hγ
  have hδ : ∀ k, L k - M k = root a c k + γ k := by
    intro k
    have := congrFun hd k
    simp only [hL, hM, Pi.add_apply, Pi.sub_apply] at this ⊢
    linarith
  have hN : ∀ i j, i < j → ε i = ε j → (L + M) j ≤ (L + M) i := by
    intro i j hij h
    have := hΛ i j hij h
    have := hμ i j hij h
    have := rhoC_anti ε i j hij h
    simp only [hL, hM, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hgap : 1 < L a0 - L c0 := by
    have h1 := hV a0 c0 ha0 hc0
    have hne : a0 ≠ c0 := fun h => by rw [h, hc0] at ha0; exact absurd ha0 (by simp)
    have h2 : vNormSq ε (Λ - root a0 c0) = vNormSq ε Λ - 2 * ∑ i, root a0 c0 i * L i
        + ∑ i, root a0 c0 i * root a0 c0 i := by
      simp only [vNormSq, nsq, dot, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hL, Pi.add_apply, Pi.sub_apply]
      ring
    rw [sum_root_mul, sum_root_mul] at h2
    have h3 : root a0 c0 a0 - root a0 c0 c0 = 2 := by
      simp [root, Pi.single_apply, hne, hne.symm]; norm_num
    linarith
  have h1 : vNormSq ε Λ - vNormSq ε μ = ∑ k, root a c k * (L + M) k + ∑ k, γ k * (L + M) k := by
    simp only [vNormSq, nsq, dot, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hL, ← hM, ← add_mul, ← hδ, Pi.add_apply]
    ring
  rw [sum_root_mul] at h1
  have h2 := cone_nonneg ε co hco _ hN
  have h3 : (L + M) a0 ≤ (L + M) a := by
    rcases eq_or_lt_of_le (show a ≤ a0 by rw [Fin.le_def]; omega) with h | h
    · rw [h]
    · exact hN _ _ h (ha.trans ha0.symm)
  have h4 : (L + M) c ≤ (L + M) c0 := by
    rcases eq_or_lt_of_le (show c0 ≤ c by rw [Fin.le_def]; omega) with h | h
    · rw [h]
    · exact hN _ _ h (hc0.trans hc.symm)
  have h5 : γ c0 - γ a0 ≥ 0 := by
    have := cone_nonneg ε co hco (fun k => root c0 a0 k) (by
      intro i j hij h
      have hi : i ≠ a0 := by
        rintro rfl
        have : ε j = true := h.symm.trans ha0
        rw [hε] at this
        simp only [decide_eq_true_eq] at this
        rw [Fin.lt_def] at hij
        omega
      have hj : j ≠ c0 := by
        rintro rfl
        have : ε i = false := h.trans hc0
        rw [hε] at this
        simp only [decide_eq_false_iff_not] at this
        rw [Fin.lt_def] at hij
        omega
      simp only [root, Pi.sub_apply, Pi.single_apply, if_neg hi, if_neg hj]
      split_ifs <;> norm_num)
    simp only [mul_comm _ (root c0 a0 _)] at this
    rw [sum_root_mul] at this
    exact this
  have h6 : root a c a0 ≤ 1 := by
    simp only [root, Pi.sub_apply, Pi.single_apply]; split_ifs <;> norm_num
  have h7 : -1 ≤ root a c c0 := by
    simp only [root, Pi.sub_apply, Pi.single_apply]; split_ifs <;> norm_num
  have h8 := hδ a0
  have h9 := hδ c0
  simp only [Pi.add_apply] at h1 h2 h3 h4 ⊢
  linarith

section Rep

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool} {σ : Mt n → (H →L[ℂ] H)}

noncomputable abbrev tor (θ : Fin n → ℝ) : Mt n := Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

lemma kset_sub {g : Mt n} (hg : g ∈ Kset ε) : g ∈ UJset ε := by
  obtain ⟨h1, h2⟩ := hg
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← h2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.1 h1, Matrix.one_mul]

lemma kset_star {g : Mt n} (hg : g ∈ Kset ε) : star g ∈ Kset ε := by
  obtain ⟨h1, h2⟩ := hg
  refine ⟨Unitary.star_mem h1, ?_⟩
  have := congrArg Matrix.conjTranspose h2
  simp only [Matrix.conjTranspose_mul, Jm_conjTranspose] at this
  exact this.symm

lemma kset_inv {g : Mt n} (hg : g ∈ Kset ε) : g⁻¹ = star g :=
  Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hg.1)

lemma tor_mem (ε : Fin n → Bool) (θ : Fin n → ℝ) : tor θ ∈ Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply, RCLike.star_def]
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp
  · simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]

lemma inner_kset (hσ : IsURepOn (UJset ε) σ) {g : Mt n} (hg : g ∈ Kset ε) (x y : H) :
    ⟪x, σ g y⟫_ℂ = ⟪σ (star g) x, y⟫_ℂ := by
  have h1 : σ g (σ (star g) x) = x := by
    have := hσ.1.2 g (kset_sub hg) _ (kset_sub (kset_star hg))
    rw [Matrix.mem_unitaryGroup_iff.1 hg.1, hσ.1.1] at this
    have h2 := congrArg (fun T : H →L[ℂ] H => T x) this
    simpa using h2.symm
  let T : H →ₗᵢ[ℂ] H := { (σ g : H →ₗ[ℂ] H) with norm_map' := hσ.2.1 g (kset_sub hg) }
  have h2 : ⟪σ g (σ (star g) x), σ g y⟫_ℂ = ⟪σ (star g) x, y⟫_ℂ := T.inner_map_map _ _
  rwa [h1] at h2

lemma exists_wt_of_inner_ne (hσ : IsURepOn (UJset ε) σ) {S : Submodule ℂ H} [FiniteDimensional ℂ S]
    (hS : IsKStableOn ε σ S) {ν : Fin n → ℝ} {y : H} (hy : IsWtOn (Kset ε) σ ν y) {w : H} (hw : w ∈ S)
    (hwy : ⟪w, y⟫_ℂ ≠ 0) : ∃ y' ∈ S, y' ≠ 0 ∧ IsWtOn (Kset ε) σ ν y' := by
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S
  have key : ∀ s ∈ S, ⟪s, S.starProjection y⟫_ℂ = ⟪s, y⟫_ℂ := by
    intro s hs
    rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 hs]
  have hm : S.starProjection y ∈ S := Submodule.starProjection_apply_mem S y
  refine ⟨S.starProjection y, hm, fun h => hwy ?_, fun θ hθ => ?_⟩
  · rw [← key w hw, h, inner_zero_right]
  · rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ)]
    set s := σ (tor θ) (S.starProjection y) -
      Complex.exp (((∑ a, ν a * θ a : ℝ) : ℂ) * Complex.I) • S.starProjection y with hs
    have hsS : s ∈ S := S.sub_mem (hS _ hθ _ hm) (S.smul_mem _ hm)
    calc ⟪s, s⟫_ℂ = ⟪s, σ (tor θ) (S.starProjection y) -
      Complex.exp (((∑ a, ν a * θ a : ℝ) : ℂ) * Complex.I) • S.starProjection y⟫_ℂ := by rw [← hs]
      _ = 0 := by
        rw [inner_sub_right, inner_smul_right, key s hsS, inner_kset hσ hθ,
          key _ (hS _ (kset_star hθ) _ hsS), ← inner_kset hσ hθ, hy θ hθ, inner_smul_right, sub_self]

lemma dominant_of_isKTypeOf (hσ : IsURepOn (UJset ε) σ) {μ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : IsKTypeOf ε σ μ S) (i j : Fin n) (hij : i < j) (h : ε i = ε j) : μ j ≤ μ i := by
  obtain ⟨_, hK, -, ⟨u, huS, hu0, hu⟩, hd⟩ := hS
  let s : Equiv.Perm (Fin n) := Equiv.swap i j
  let g : Mt n := (1 : Mt n).submatrix s id
  have hgd : ∀ d : Fin n → ℂ, Matrix.diagonal d * g = g * Matrix.diagonal (d ∘ s) := by
    intro d
    ext a b
    simp only [g, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.submatrix_apply, id, Matrix.one_apply,
      Function.comp]
    split_ifs with hab
    · rw [← hab]; simp [s]
    · simp
  have hεs : ∀ a, ε (s a) = ε a := by
    intro a
    simp only [s, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, h]
    · rw [h2, h]
    · rfl
  have hg : g ∈ Kset ε := by
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      ext a b
      simp [g, Matrix.mul_apply, Matrix.one_apply, eq_comm]
    · unfold Formalism.REAL.Jm
      rw [hgd]
      congr 2
      funext a
      simp [hεs]
  have hw : IsWtOn (Kset ε) σ (μ ∘ s) (σ g u) := by
    intro θ hθ
    have h1 := hσ.1.2 _ (kset_sub hθ) _ (kset_sub hg)
    have h2 := hσ.1.2 _ (kset_sub hg) _ (kset_sub (tor_mem ε (θ ∘ s)))
    rw [hgd] at h1
    have h3 : (σ (tor θ)).comp (σ g) = (σ g).comp (σ (tor (θ ∘ s))) := h1.symm.trans h2
    have h4 := congrArg (fun T : H →L[ℂ] H => T u) h3
    simp only [ContinuousLinearMap.comp_apply] at h4
    rw [h4, hu (θ ∘ s) (tor_mem ε _), map_smul]
    congr 4
    rw [← Equiv.sum_comp s]
    simp [s]
  have hne : σ g u ≠ 0 := by
    intro h0
    have := hσ.2.1 g (kset_sub hg) u
    rw [h0, norm_zero] at this
    exact hu0 (norm_eq_zero.1 this.symm)
  obtain ⟨co, hco, hc⟩ := hd _ _ (hK g hg u huS) hne hw
  have h1 := cone_nonneg ε co hco (fun k => -((k : ℕ) : ℝ)) (by
    intro a b hab _
    have : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab.le
    linarith)
  have h2 : μ - μ ∘ s = (μ i - μ j) • root i j := by
    funext k
    simp only [s, root, Pi.sub_apply, Function.comp, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Equiv.swap_apply_def]
    have := hij.ne
    split_ifs with h1 h2 h3
    · exact absurd (h1.symm.trans h2) this
    · rw [h1]; ring
    · rw [h3]; ring
    · ring
  rw [← hc, h2] at h1
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum] at h1
  rw [sum_root_mul i j (fun k => -((k : ℕ) : ℝ))] at h1
  have h3 : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
  by_contra hlt
  push Not at hlt
  nlinarith

lemma exists_fin_stable (lam : Fin n → ℝ) {v : H} (hv : v ∈ lowKSub ε lam σ) :
    ∃ W : Submodule ℂ H, FiniteDimensional ℂ W ∧ IsKStableOn ε σ W ∧ W ≤ lowKSub ε lam σ ∧ v ∈ W := by
  unfold lowKSub at hv
  rw [sSup_eq_iSup'] at hv
  refine Submodule.iSup_induction (motive := fun v => ∃ W : Submodule ℂ H, FiniteDimensional ℂ W ∧
    IsKStableOn ε σ W ∧ W ≤ lowKSub ε lam σ ∧ v ∈ W) _ hv ?_ ?_ ?_
  · rintro ⟨S, hS⟩ x hx
    exact ⟨S, hS.1, hS.2.1, le_sSup hS, hx⟩
  · refine ⟨⊥, inferInstance, fun g _ w hw => ?_, bot_le, Submodule.zero_mem _⟩
    rw [(Submodule.mem_bot ℂ).1 hw, map_zero]
    exact Submodule.zero_mem _
  · rintro x y ⟨W, h1, h2, h3, h4⟩ ⟨W', h1', h2', h3', h4'⟩
    refine ⟨W ⊔ W', inferInstance, fun g hg w hw => ?_, sup_le h3 h3', Submodule.add_mem_sup h4 h4'⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add]
    exact Submodule.add_mem_sup (h2 g hg a ha) (h2' g hg b hb)

lemma cdom_of_inner_ne (hσ : IsURepOn (UJset ε) σ) (lam : Fin n → ℝ) {ν : Fin n → ℝ} {y : H}
    (hy : IsWtOn (Kset ε) σ ν y) {w : H} (hw : w ∈ lowKSub ε lam σ) (hwy : ⟪w, y⟫_ℂ ≠ 0) :
    CDom ε ν (Formalism.QuantumDeterminants.lowK ε lam) := by
  by_contra hn
  have h : lowKSub ε lam σ ≤ (ℂ ∙ y)ᗮ := by
    refine sSup_le fun S hS x hx => ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    by_contra hx0
    haveI := hS.1
    obtain ⟨y', h1, h2, h3⟩ := exists_wt_of_inner_ne hσ hS.2.1 hy hx hx0
    exact hn (hS.2.2.2.2 ν y' h1 h2 h3)
  exact hwy (Submodule.mem_orthogonal_singleton_iff_inner_left.1 (h hw))

lemma tor_conj (θ : Fin n → ℝ) (a c : Fin n) :
    tor θ * Matrix.single a c (1 : ℂ) * (tor θ)⁻¹ =
      Complex.exp (((θ a - θ c : ℝ) : ℂ) * Complex.I) • Matrix.single a c (1 : ℂ) := by
  rw [kset_inv (tor_mem (fun _ => true) θ), Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, Matrix.single_apply, Pi.star_apply,
    RCLike.star_def, smul_eq_mul]
  split_ifs with h
  · rw [← h.1, ← h.2, ← Complex.exp_conj, mul_one, mul_one, ← Complex.exp_add]
    congr 1
    simp
    ring
  · simp

lemma conjH_single (a c : Fin n) (ha : ε a = true) (hc : ε c = false) :
    conjH (Formalism.REAL.Jm ε) (Matrix.single c a (1 : ℂ)) = Matrix.single a c 1 := by
  unfold conjH
  rw [Matrix.inv_eq_left_inv (Jm_mul_self ε)]
  ext i j
  simp only [Formalism.REAL.Jm, Matrix.neg_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    Matrix.single_apply]
  by_cases h : a = i ∧ c = j
  · obtain ⟨rfl, rfl⟩ := h
    simp [ha, hc]
  · have h' : ¬(c = j ∧ a = i) := fun h' => h ⟨h'.2, h'.1⟩
    simp [h, h']

end Rep

theorem lowK_killed : ∀ (n p : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mt n → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → (∀ a, ε a = decide ((a : ℕ) < p)) → IsDS ε lam σ → ∀ v ∈ lowKSub ε lam σ, SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v → ∀ a c : Fin n, ε a = true → ε c = false → dRepC (Formalism.REAL.Jm ε) σ (Matrix.single c a 1) v = 0 := by
  intro n p ε lam H _ _ σ hlam hε hDS v hv hsm a c ha hc
  obtain ⟨hcomp, -, hσ, -, -, ⟨S₀, hS₀⟩, hmin⟩ := hDS
  have hH : (Formalism.REAL.Jm ε).IsHermitian := Jm_conjTranspose ε
  have hdet : (Formalism.REAL.Jm ε).det ≠ 0 := (Matrix.isUnit_det_of_left_inverse (Jm_mul_self ε)).ne_zero
  have hU : IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε)) σ := hσ
  obtain ⟨hspan, hsmv⟩ := GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv n _ H σ hH hdet hU
  have hlie := GlobalTheory.T.complexifiedDerivedAction_isLieAction n _ H σ hH hdet hU
  obtain ⟨W, hWf, hWK, hWle, hvW⟩ := exists_fin_stable lam hv
  set J := Formalism.REAL.Jm ε with hJ
  let V : Submodule ℂ H := W ⊓ Submodule.span ℂ {w | SmoothVec (lieH J) σ w}
  have hVs : ∀ w ∈ V, SmoothVec (lieH J) σ w := fun w hw => hspan w hw.2
  haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le inf_le_left
  have hVK : ∀ g ∈ Kset ε, ∀ w ∈ V, σ g w ∈ V := fun g hg w hw =>
    ⟨hWK g hg w hw.1, Submodule.subset_span ((hsmv w (hVs w hw)).1 g (kset_sub hg))⟩
  have hs0 : SmoothVec (lieH J) σ 0 := hspan 0 (Submodule.zero_mem _)
  have hz1 : ∀ w, SmoothVec (lieH J) σ w → dRepC J σ 0 w = 0 := by
    intro w hw
    have := ((hlie w w hw hw).1 1 0 0).1
    simpa using this
  have hz2 : ∀ Z, dRepC J σ Z 0 = 0 := by
    intro Z
    have := ((hlie 0 0 hs0 hs0).1 1 Z Z).2.1
    simpa using this
  have hsm1 : ∀ w, SmoothVec (lieH J) σ w → ∀ (t : ℂ) Z, dRepC J σ (t • Z) w = t • dRepC J σ Z w := by
    intro w hw t Z
    have := ((hlie w w hw hw).1 t Z 0).1
    rwa [add_zero, hz1 w hw, add_zero] at this
  let B : Mt n →ₗ[ℂ] V →ₗ[ℂ] H := LinearMap.mk₂ ℂ (fun Z w => dRepC J σ Z w)
    (fun Z Z' w => by simpa using ((hlie w w (hVs _ w.2) (hVs _ w.2)).1 1 Z Z').1)
    (fun t Z w => hsm1 w (hVs _ w.2) t Z)
    (fun Z w w' => by simpa using ((hlie w w' (hVs _ w.2) (hVs _ w'.2)).1 1 Z Z).2.1)
    (fun t Z w => by
      have := ((hlie w 0 (hVs _ w.2) hs0).1 t Z Z).2.1
      rwa [add_zero, hz2, add_zero] at this)
  let G : Set H := {x | ∃ Z : Mt n, (Z * J = Z ∧ J * Z = -Z) ∧ ∃ w ∈ V, x = dRepC J σ Z w}
  let S : Submodule ℂ H := Submodule.span ℂ G
  have hSf : FiniteDimensional ℂ S := by
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (TensorProduct.lift B)) ?_
    refine Submodule.span_le.2 ?_
    rintro x ⟨Z, -, w, hw, rfl⟩
    exact ⟨Z ⊗ₜ ⟨w, hw⟩, rfl⟩
  have hSK : IsKStableOn ε σ S := by
    intro g hg
    have : S ≤ S.comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨Z, ⟨hZ1, hZ2⟩, w, hw, rfl⟩
      refine Submodule.subset_span ⟨g * Z * g⁻¹, ⟨?_, ?_⟩, σ g w, hVK g hg w hw,
        (hlie w w (hVs w hw) (hVs w hw)).2.2.1 g (kset_sub hg) Z⟩
      · rw [kset_inv hg, Matrix.mul_assoc, (kset_star hg).2, ← Matrix.mul_assoc, Matrix.mul_assoc g Z, hZ1]
      · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hg.2, Matrix.mul_assoc g _ Z, hZ2]
        simp
    exact fun x hx => this hx
  have hSs : ∀ x ∈ S, SmoothVec (lieH J) σ x := by
    intro x hx
    refine hspan x (Submodule.span_mono ?_ hx)
    rintro x ⟨Z, -, w, hw, rfl⟩
    exact (hsmv w (hVs w hw)).2.2.1 Z
  by_contra hne
  have hS0 : S ≠ ⊥ := by
    intro h0
    refine hne ((Submodule.mem_bot ℂ).1 (h0 ▸ Submodule.subset_span
      ⟨Matrix.single c a 1, ⟨?_, ?_⟩, v, ⟨hvW, Submodule.subset_span hsm⟩, rfl⟩))
    · ext i j
      simp only [hJ, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.single_apply]
      by_cases h : c = i ∧ a = j
      · obtain ⟨rfl, rfl⟩ := h
        simp [ha]
      · simp [h]
    · ext i j
      simp only [hJ, Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.neg_apply, Matrix.single_apply]
      by_cases h : c = i ∧ a = j
      · obtain ⟨rfl, rfl⟩ := h
        simp [hc]
      · simp [h]
  obtain ⟨μ, S', hS'le, hS'⟩ := GlobalTheory.T.exists_compactType_in_compactStable_submodule n ε H σ hσ S hSf hSK hS0
  obtain ⟨u, huS', hu0, hu⟩ := hS'.2.2.2.1
  have huS := hS'le huS'
  have hus := hSs u huS
  have hex : ∃ a' c' : Fin n, ε a' = true ∧ ε c' = false ∧ ∃ w ∈ V,
      ⟪dRepC J σ (Matrix.single c' a' 1) w, u⟫_ℂ ≠ 0 := by
    by_contra hn
    push Not at hn
    have h : S ≤ (ℂ ∙ u)ᗮ := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨Z, ⟨hZ1, hZ2⟩, w, hw, rfl⟩
      have h1 : dRepC J σ Z w = ∑ i, ∑ j, Z i j • dRepC J σ (Matrix.single i j 1) w := by
        have : B Z ⟨w, hw⟩ = ∑ i, ∑ j, Z i j • B (Matrix.single i j 1) ⟨w, hw⟩ := by
          conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
          simp only [map_sum, LinearMap.sum_apply]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [← LinearMap.smul_apply, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
        exact this
      rw [SetLike.mem_coe, h1]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      by_cases hij : Z i j = 0
      · rw [hij, zero_smul]
        exact Submodule.zero_mem _
      · refine Submodule.smul_mem _ _ (Submodule.mem_orthogonal_singleton_iff_inner_left.2 (hn j i ?_ ?_ w hw))
        · have := congrFun (congrFun hZ1 i) j
          simp only [hJ, Formalism.REAL.Jm, Matrix.mul_diagonal] at this
          by_contra hj
          rw [if_neg hj] at this
          exact hij (by linear_combination (-1 / 2 : ℂ) * this)
        · have := congrFun (congrFun hZ2 i) j
          simp only [hJ, Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.neg_apply] at this
          by_contra hi
          rw [if_pos (by simpa using hi)] at this
          exact hij (by linear_combination (1 / 2 : ℂ) * this)
    exact hu0 (inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_left.1 (h huS)))
  obtain ⟨a', c', ha', hc', w, hw, hwu⟩ := hex
  rw [(hlie w u (hVs w hw) hus).2.2.2, neg_ne_zero, hJ, conjH_single a' c' ha' hc', ← hJ] at hwu
  have hy : IsWtOn (Kset ε) σ (μ + root a' c') (dRepC J σ (Matrix.single a' c' 1) u) := by
    intro θ hθ
    have h1 := (hlie u u hus hus).2.2.1 _ (kset_sub hθ) (Matrix.single a' c' 1)
    have h2 := ((hlie u 0 hus hs0).1 (Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I))
      (Matrix.single a' c' 1) 0).2.1
    rw [add_zero, hz2, add_zero] at h2
    rw [h1, tor_conj, hsm1 _ ((hsmv u hus).1 _ (kset_sub hθ)), hu θ hθ, h2, smul_smul, ← Complex.exp_add]
    congr 2
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, sum_root_mul]
    push_cast
    ring
  have hd := cdom_of_inner_ne hσ lam hy (hWle hw.1) hwu
  exact absurd (hmin μ S' hS') (not_le.2 (vNormSq_lt p ε hε _ μ (dominant_of_isKTypeOf hσ hS₀)
    (dominant_of_isKTypeOf hσ hS') (GlobalTheory.T.voganNormSq_holomorphicLowestKType_sub_root_lt n p ε lam hlam hε) a' c' ha' hc' hd))

end GlobalTheory.HolDict.Lowering

import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianFormsSameSignatureSameSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SignatureHermitianModelOfDatum

open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HermModel
open scoped nonZeroDivisors

namespace GlobalTheory.LatSplitPrime

theorem sum_orth {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M] {σ : O →+* O}
    (h : M →ₗ[O] M →ₛₗ[σ] O) [Fintype ι] (c : ι → O) (w : ι → M) (ho : ∀ i j, i ≠ j → h (w i) (w j) = 0) :
    h (∑ i, c i • w i) (∑ i, c i • w i) = ∑ i, c i * σ (c i) * h (w i) (w i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  rw [Finset.sum_eq_single j (fun i _ hi => by rw [ho i j hi, mul_zero]) (by simp)]
  ring

section Real

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem denseRange_places : DenseRange fun (x : E) (w : InfinitePlace E) => w.embedding x := by
  have h1 := NumberField.InfiniteAdeleRing.denseRange_algebraMap E
  have hs : Function.Surjective
      (Pi.map fun w : InfinitePlace E => InfinitePlace.Completion.extensionEmbedding w) := by
    intro y
    choose x hx using fun w : InfinitePlace E =>
      InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex (IsTotallyComplex.isComplex w) (y w)
    exact ⟨x, funext hx⟩
  have hc : Continuous (Pi.map fun w : InfinitePlace E => InfinitePlace.Completion.extensionEmbedding w) :=
    continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have := hs.denseRange.comp h1 hc
  convert this using 1
  funext x w
  change w.embedding x = InfinitePlace.Completion.extensionEmbedding w (algebraMap E (InfiniteAdeleRing E) x w)
  rw [InfiniteAdeleRing.algebraMap_apply]
  have := InfinitePlace.Completion.extensionEmbedding_coe (v := w) ((WithAbs.equiv w.1).symm x)
  simp only [RingEquiv.apply_symm_apply] at this
  rw [← this]
  rfl

theorem map_herm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    τ (FD.herm G x y) = FD.hermC τ G (τ ∘ x) (τ ∘ y) := by
  simp [FD.herm, FD.hermC, FD.cc, IsCMField.complexEmbedding_complexConj]

noncomputable def sesqC (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) :
    (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₛₗ[starRingEnd ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (FD.hermC τ G)
    (fun x y z => by simp [FD.hermC, add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [FD.hermC, Finset.mul_sum, mul_assoc])
    (fun x y z => by simp [FD.hermC, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [FD.hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)

omit [NumberField E] [IsCMField E] in
theorem re_comb (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {Q : Matrix (Fin r) (Fin r) ℂ} {p : ℕ}
    (hQ : FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p (a : ℕ) : ℝ) : ℂ)) (c : Fin r → ℂ) :
    (FD.hermC τ G (Q *ᵥ c) (Q *ᵥ c)).re = ∑ a, Complex.normSq (c a) * FD.sgn p (a : ℕ) := by
  have h1 : ∀ a b, sesqC τ G (FD.col Q a) (FD.col Q b) =
      Matrix.diagonal (fun a : Fin r => ((FD.sgn p (a : ℕ) : ℝ) : ℂ)) a b := fun a b => congrFun (congrFun hQ a) b
  have h2 : Q *ᵥ c = ∑ a, c a • FD.col Q a := by
    ext k
    simp [Matrix.mulVec, dotProduct, FD.col, mul_comm]
  have h3 := sum_orth (sesqC τ G) c (FD.col Q) fun a b hab => by rw [h1, Matrix.diagonal_apply_ne _ hab]
  rw [← h2] at h3
  refine (congrArg Complex.re h3).trans ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [h1, Matrix.diagonal_apply_eq, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem exists_ker {a b : ℕ} (hab : b < a) (f : (Fin a → ℂ) →ₗ[ℂ] (Fin b → ℂ)) : ∃ c, c ≠ 0 ∧ f c = 0 := by
  have := LinearMap.ker_ne_bot_of_finrank_lt (f := f) (by simpa using hab)
  obtain ⟨c, hc, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
  exact ⟨c, h0, hc⟩

theorem exists_pos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p k : ℕ) (G : Matrix (Fin r) (Fin r) E), k < p → p ≤ r → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p (a : ℕ) : ℝ) : ℂ)) → ∀ (v : Fin k → Fin r → E) (m : Fin k → E), ∃ x : Fin r → E, ∀ τ : E →+* ℂ, 0 < (τ (FD.herm G x x - ∑ i, m i * (FD.herm G x (v i) * FD.herm G (v i) x))).re := by
  intro E _ _ _ r p k G hk hp hsig v m
  have key : ∀ τ : E →+* ℂ, ∃ u : Fin r → ℂ, (∀ i, FD.hermC τ G u (τ ∘ v i) = 0) ∧ 0 < (FD.hermC τ G u u).re := by
    intro τ
    obtain ⟨Q, -, hQ⟩ := hsig τ
    let ext : (Fin p → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
      LinearMap.pi fun a => if h : (a : ℕ) < p then LinearMap.proj (⟨a, h⟩ : Fin p) else 0
    obtain ⟨c, hc, h0⟩ := exists_ker hk
      ((LinearMap.pi fun i => (sesqC τ G).flip (τ ∘ v i)) ∘ₗ Matrix.mulVecLin Q ∘ₗ ext)
    refine ⟨Q *ᵥ ext c, fun i => congrFun h0 i, ?_⟩
    rw [re_comb τ G hQ]
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hc
    refine Finset.sum_pos' (fun a _ => ?_) ⟨Fin.castLE hp j, Finset.mem_univ _, ?_⟩
    · by_cases h : (a : ℕ) < p
      · simp [FD.sgn, h, Complex.normSq_nonneg]
      · simp [ext, h]
    · have hj' : c j ≠ 0 := hj
      simpa [ext, FD.sgn] using hj'
  choose u hu0 hu using key
  let F : (w : InfinitePlace E) → (Fin r → InfinitePlace E → ℂ) → ℝ := fun w z =>
    (FD.hermC w.embedding G (fun a => z a w) (fun a => z a w) - ∑ i, w.embedding (m i) *
      (FD.hermC w.embedding G (fun a => z a w) (w.embedding ∘ v i) *
        FD.hermC w.embedding G (w.embedding ∘ v i) (fun a => z a w))).re
  have hF : ∀ w, Continuous (F w) := fun w => by
    simp only [F, FD.hermC]
    fun_prop
  have hd : DenseRange (Pi.map fun (_ : Fin r) (x : E) (w : InfinitePlace E) => w.embedding x) :=
    DenseRange.piMap fun _ => denseRange_places
  have hne : ∀ w, 0 < F w fun a w => u w.embedding a := fun w => by
    have e : F w (fun a w => u w.embedding a) = (FD.hermC w.embedding G (u w.embedding) (u w.embedding)).re := by
      simp only [F, hu0, zero_mul, mul_zero, Finset.sum_const_zero, sub_zero]
    rw [e]
    exact hu _
  have hU : IsOpen (⋂ w, {z | 0 < F w z}) := isOpen_iInter_of_finite fun w => isOpen_lt continuous_const (hF w)
  obtain ⟨x, hx⟩ := hd.exists_mem_open hU ⟨fun a w => u w.embedding a, Set.mem_iInter.2 hne⟩
  refine ⟨x, fun τ => ?_⟩
  have h1 : 0 < F (InfinitePlace.mk τ) (fun a w => w.embedding (x a)) := Set.mem_iInter.1 hx (InfinitePlace.mk τ)
  have h2 : 0 < ((InfinitePlace.mk τ).embedding
      (FD.herm G x x - ∑ i, m i * (FD.herm G x (v i) * FD.herm G (v i) x))).re := by
    simp only [map_sub, map_sum, map_mul, map_herm]
    exact h1
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rwa [h] at h2
  · rwa [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re] at h2

theorem not_forall_pos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p : ℕ) (G : Matrix (Fin r) (Fin r) E) (τ : E →+* ℂ) (Q : Matrix (Fin r) (Fin r) ℂ), Q.det ≠ 0 → (FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p (a : ℕ) : ℝ) : ℂ)) → ∀ v : Fin (p + 1) → Fin r → E, (∀ i j, i ≠ j → FD.herm G (v i) (v j) = 0) → ¬ ∀ i, 0 < (τ (FD.herm G (v i) (v i))).re := by
  intro E _ _ _ r p G τ Q hdet hQ v ho hpos
  let res : (Fin r → ℂ) →ₗ[ℂ] (Fin p → ℂ) :=
    LinearMap.pi fun a => if h : (a : ℕ) < r then LinearMap.proj (⟨a, h⟩ : Fin r) else 0
  obtain ⟨c, hc, h0⟩ := exists_ker (Nat.lt_succ_self p)
    (res ∘ₗ Matrix.mulVecLin Q⁻¹ ∘ₗ Fintype.linearCombination ℂ fun i => τ ∘ v i)
  have h1 := sum_orth (sesqC τ G) c (fun i => τ ∘ v i) fun i j hij =>
    (map_herm τ G _ _).symm.trans (by rw [ho i j hij, map_zero])
  change res (Q⁻¹ *ᵥ ∑ i, c i • (τ ∘ v i)) = 0 at h0
  generalize ∑ i, c i • (τ ∘ v i) = x at h0 h1
  have h2 := re_comb τ G hQ (Q⁻¹ *ᵥ x)
  rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), one_mulVec] at h2
  have h3 : (FD.hermC τ G x x).re ≤ 0 := by
    rw [h2]
    refine Finset.sum_nonpos fun a _ => ?_
    by_cases h : (a : ℕ) < p
    · have := congrFun h0 ⟨a, h⟩
      simp only [res, LinearMap.pi_apply, a.2, dif_pos, LinearMap.proj_apply, Pi.zero_apply] at this
      rw [this]
      simp
    · simp [FD.sgn, h, Complex.normSq_nonneg]
  have h4 : 0 < (sesqC τ G x x).re := by
    rw [h1, Complex.re_sum]
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hc
    have e : ∀ i, (c i * starRingEnd ℂ (c i) * sesqC τ G (τ ∘ v i) (τ ∘ v i)).re =
        Complex.normSq (c i) * (τ (FD.herm G (v i) (v i))).re := fun i => by
      rw [Complex.mul_conj, Complex.re_ofReal_mul, map_herm]
      rfl
    refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
    · rw [e]
      exact mul_nonneg (Complex.normSq_nonneg _) (hpos i).le
    · rw [e]
      exact mul_pos (Complex.normSq_pos.2 hj) (hpos j)
  exact absurd h4 (not_lt.2 h3)

end Real

theorem exists_notMem : ∀ (O M : Type) [CommRing O] [IsDedekindDomain O] [AddCommGroup M] [Module O M] [Module.Finite O M] (σ : O →+* O) (h : M →ₗ[O] M →ₛₗ[σ] O) (q ρ n : O) (W : Submodule O M) (π : M →ₗ[O] M) (P : Ideal O), (∀ (a : O) (x : M), a • x = 0 → a = 0 ∨ x = 0) → P.IsMaximal → q ∈ P → q ≠ 0 → σ ρ = -ρ → 2 * ρ ∉ P → n ∉ P → W ≠ ⊥ → (∀ x, (∀ y, q ∣ h x y) → ∃ z, x = q • z) → (∀ x, π x ∈ W) → (∀ x ∈ W, π x = n • x) → (∀ x ∈ W, ∀ y, h x (π y) = n * h x y) → ∃ f ∈ W, h f f ∉ P := by
  intro O M _ _ _ _ _ σ h q ρ n W π P htf hP hqP hq hρ h2ρ hn hW hperf π1 π2 π3
  by_contra hcon
  push Not at hcon
  have h1 : ∀ x ∈ W, ∀ y ∈ W, h x y ∈ P := fun x hx y hy => by
    have a1 := P.sub_mem (P.sub_mem (hcon _ (W.add_mem hx hy)) (hcon x hx)) (hcon y hy)
    have a2 := P.sub_mem (P.sub_mem (hcon _ (W.add_mem (W.smul_mem ρ hx) hy)) (hcon _ (W.smul_mem ρ hx))) (hcon y hy)
    have a3 := P.add_mem (P.mul_mem_left ρ a1) a2
    have e : ρ * (h (x + y) (x + y) - h x x - h y y) +
        (h (ρ • x + y) (ρ • x + y) - h (ρ • x) (ρ • x) - h y y) = 2 * ρ * h x y := by
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hρ, RingHom.id_apply]
      ring
    rw [e] at a3
    exact (hP.isPrime.mem_or_mem a3).resolve_left h2ρ
  have h2 : ∀ x ∈ W, ∀ y, h x y ∈ P := fun x hx y => by
    have := h1 x hx _ (π1 y)
    rw [π3 x hx] at this
    exact (hP.isPrime.mem_or_mem this).resolve_left hn
  obtain ⟨I, hI⟩ : ∃ I : Ideal O, Ideal.span {q} = P * I :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hqP)
  obtain ⟨b, c, hc, hbc⟩ := hP.exists_inv hn
  have h3 : I • W ≤ P • I • W := by
    refine Submodule.smul_le.2 fun a ha x hx => ?_
    obtain ⟨z, hz⟩ := hperf (a • x) fun y => by
      rw [← Ideal.mem_span_singleton, hI, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm a]
      exact Ideal.mul_mem_mul (h2 x hx y) ha
    have e : a • x = b • q • π z + c • a • x := by
      rw [← map_smul, ← hz, π2 _ (W.smul_mem a hx), smul_smul b, ← add_smul, hbc, one_smul]
    rw [e]
    refine add_mem (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem_smul hc (Submodule.smul_mem_smul ha hx))
    rw [← Submodule.mul_smul, ← hI]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self q) (π1 z)
  obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul P (I • W)
    (IsNoetherian.noetherian _) h3
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hqI : q ∈ I := Ideal.le_of_dvd ⟨P, by rw [hI, mul_comm]⟩ (Ideal.mem_span_singleton_self q)
  have h4 : q • x ∈ I • W := Submodule.smul_mem_smul hqI hx
  rcases htf s (q • x) (hs _ h4) with h0 | h0
  · rw [h0, zero_sub] at hs1
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (P.neg_mem_iff.1 hs1))
  · exact (htf _ _ h0).elim hq hx0

theorem exists_isCoprime : ∀ (O M : Type) [CommRing O] [IsDedekindDomain O] [AddCommGroup M] [Module O M] (σ : O →+* O) (h : M →ₗ[O] M →ₛₗ[σ] O) (q : O) (W : Submodule O M), q ≠ 0 → (∀ a, σ (σ a) = a) → (∀ x, σ (h x x) = h x x) → (∀ P : Ideal O, P.IsMaximal → q ∈ P → ∃ f ∈ W, h f f ∉ P) → ∃ f ∈ W, IsCoprime (h f f) q := by
  intro O M _ _ _ _ σ h q W hq hσ hs hloc
  classical
  have key : ∀ S : Finset (Ideal O), (∀ P ∈ S, P.IsMaximal ∧ q ∈ P) → ∃ f ∈ W, ∀ P ∈ S, h f f ∉ P := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun _ => ⟨0, W.zero_mem, by simp⟩
    | insert P₀ S _ ih =>
      intro hS
      obtain ⟨f, hf, hfS⟩ := ih fun P hP => hS P (Finset.mem_insert_of_mem hP)
      obtain ⟨hP₀, hq₀⟩ := hS P₀ (Finset.mem_insert_self _ _)
      by_cases hc : h f f ∈ P₀
      swap
      · exact ⟨f, hf, fun P hP => (Finset.mem_insert.1 hP).elim (fun e => e ▸ hc) (hfS P)⟩
      obtain ⟨g, hg, hg₀⟩ := hloc P₀ hP₀ hq₀
      obtain ⟨a, ha⟩ : ∃ a, ∀ P ∈ S, 1 - a * h f f ∈ P := by
        have h1 : IsCoprime (Ideal.span {h f f}) (∏ P ∈ S, P) := IsCoprime.prod_right fun P hP => by
          obtain ⟨b, c, hc, hbc⟩ := (hS P (Finset.mem_insert_of_mem hP)).1.exists_inv (hfS P hP)
          exact Ideal.isCoprime_iff_exists.2 ⟨_, Ideal.mem_span_singleton'.2 ⟨b, rfl⟩, c, hc, hbc⟩
        obtain ⟨i, hi, j, hj, e⟩ := Ideal.isCoprime_iff_exists.1 h1
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hi
        refine ⟨a, fun P hP => ?_⟩
        rw [← e, add_sub_cancel_left]
        exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hP) hj
      set c := h f f with hcdef
      have hσc : σ c = c := hs f
      set b := (1 - a * c) * (1 - σ a * c) with hb
      have hσb : σ b = b := by
        rw [hb]
        simp only [map_mul, map_sub, map_one, hσ, hσc]
        ring
      have e : h (c • f + b • g) (c • f + b • g) = c * c * c + b * (c * (h f g + h g f)) + b * b * h g g := by
        simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hσc, hσb,
          RingHom.id_apply, ← hcdef]
        ring
      refine ⟨c • f + b • g, W.add_mem (W.smul_mem _ hf) (W.smul_mem _ hg), fun P hP hmem => ?_⟩
      rw [e] at hmem
      rcases Finset.mem_insert.1 hP with rfl | hP
      · refine hg₀ ?_
        have e2 : h g g = (c * c * c + b * (c * (h f g + h g f)) + b * b * h g g) -
            c * (c * c + b * (h f g + h g f) + (a * σ a * c - a - σ a) * (b + 1) * h g g) := by
          rw [hb]
          ring
        rw [e2]
        exact P.sub_mem hmem (P.mul_mem_right _ hc)
      · have hbP : b ∈ P := P.mul_mem_right _ (ha P hP)
        have hp := (hS P (Finset.mem_insert_of_mem hP)).1.isPrime
        have h3 : c * c * c ∈ P := by
          have := P.sub_mem hmem (P.mul_mem_right (c * (h f g + h g f) + b * h g g) hbP)
          convert this using 1
          ring
        exact hfS P hP ((hp.mem_or_mem h3).elim (fun h4 => (hp.mem_or_mem h4).elim id id) id)
  have hfin : {P : Ideal O | P ∣ Ideal.span {q}}.Finite := by
    haveI := UniqueFactorizationMonoid.fintypeSubtypeDvd (Ideal.span {q})
      (by simpa [Ideal.span_singleton_eq_bot] using hq)
    exact Set.finite_coe_iff.1 (inferInstanceAs (Finite {P : Ideal O // P ∣ Ideal.span {q}}))
  obtain ⟨f, hf, hfS⟩ := key (hfin.toFinset.filter Ideal.IsMaximal) fun P hP => by
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hP
    exact ⟨hP.2, Ideal.dvd_span_singleton.1 hP.1⟩
  refine ⟨f, hf, ?_⟩
  rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  refine hfS P ?_ (hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)))
  rw [Finset.mem_filter, Set.Finite.mem_toFinset]
  exact ⟨Ideal.dvd_iff_le.2 (le_sup_right.trans hle), hP⟩

section Abstract

variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {σ : O →+* O} (h : M →ₗ[O] M →ₛₗ[σ] O)

def perp {k : ℕ} (v : Fin k → M) : Submodule O M where
  carrier := {x | ∀ i, h x (v i) = 0}
  zero_mem' := fun i => by simp
  add_mem' := fun {a b} ha hb i => by simp [ha i, hb i]
  smul_mem' := fun c x hx i => by simp [hx i]

theorem exists_proj {k : ℕ} (v : Fin k → M) (m : Fin k → O) (n : O) (hn : σ n = n)
    (ho : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hm : ∀ i, m i * h (v i) (v i) = n) :
    ∃ π : M →ₗ[O] M, (∀ x, π x = n • x - ∑ i, (m i * h x (v i)) • v i) ∧ (∀ x, π x ∈ perp h v) ∧
      (∀ x ∈ perp h v, π x = n • x) ∧ ∀ x ∈ perp h v, ∀ y, h x (π y) = n * h x y := by
  let π : M →ₗ[O] M := n • LinearMap.id - ∑ i, (m i • h.flip (v i)).smulRight (v i)
  have e : ∀ x, π x = n • x - ∑ i, (m i * h x (v i)) • v i := fun x => by
    simp [π, LinearMap.sum_apply]
  refine ⟨π, e, fun x j => ?_, fun x hx => ?_, fun x hx y => ?_⟩
  · rw [e]
    simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
    rw [Finset.sum_eq_single j (fun i _ hi => by rw [ho i j hi, mul_zero]) (by simp), ← hm j]
    ring
  · rw [e, Finset.sum_eq_zero fun i _ => by rw [hx i, mul_zero, zero_smul], sub_zero]
  · rw [e, map_sub, map_sum, Finset.sum_eq_zero fun i _ => by rw [map_smulₛₗ, hx i, smul_zero], sub_zero,
      map_smulₛₗ, hn, smul_eq_mul]

end Abstract

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_mul {q : ℕ} (hq : q.Prime) {k : ℕ} (c : Fin k → 𝓞 E) (h0 : ∀ i, c i ≠ 0)
    (hc : ∀ i, IsCoprime (c i) (q : 𝓞 E)) : ∃ (N : ℕ) (m : Fin k → 𝓞 E), ¬ q ∣ N ∧ ∀ i, m i * c i = N := by
  have h1 : ∀ i, ∃ N : ℕ, ¬ q ∣ N ∧ c i ∣ (N : 𝓞 E) := fun i => by
    have h2 : Ideal.absNorm (Ideal.span {c i}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact h0 i
    have h3 := Ideal.mem_span_singleton.1 (Ideal.absNorm_mem (Ideal.span {c i}))
    obtain ⟨j, N, hN, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd h2 q hq.ne_one
    rw [e, Nat.cast_mul, Nat.cast_pow] at h3
    exact ⟨N, hN, (hc i).pow_right.dvd_of_dvd_mul_left h3⟩
  choose N hN hd using h1
  have h4 : ∀ i, ∃ m, m * c i = ((∏ j, N j : ℕ) : 𝓞 E) := fun i => by
    obtain ⟨m, hm⟩ := (hd i).trans (Nat.cast_dvd_cast (Finset.dvd_prod_of_mem N (Finset.mem_univ i)))
    exact ⟨m, by rw [hm, mul_comm]⟩
  choose m hm using h4
  refine ⟨_, m, fun hh => ?_, hm⟩
  obtain ⟨i, -, hi⟩ := (hq.prime.dvd_finset_prod_iff _).1 hh
  exact hN i hi

theorem eventually_pos (A B C : ℝ) (hC : 0 < C) {q : ℕ} (hq : 0 < q) :
    ∀ᶠ t : ℕ in Filter.atTop, 0 < A + ((q * t : ℕ) : ℝ) * B + ((q * t : ℕ) : ℝ) ^ 2 * C := by
  obtain ⟨T, hT⟩ := exists_nat_gt ((|A| + |B|) / C)
  rw [div_lt_iff₀ hC] at hT
  filter_upwards [Filter.eventually_ge_atTop (T + 1)] with t ht
  have h1 : ((T + 1 : ℕ) : ℝ) ≤ ((q * t : ℕ) : ℝ) := by
    exact_mod_cast ht.trans (Nat.le_mul_of_pos_left t hq)
  generalize ((q * t : ℕ) : ℝ) = s at h1
  push_cast at h1
  have h2 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have h3 : |A| + |B| < s * C := by nlinarith
  have h4 := neg_abs_le A
  have h5 := neg_abs_le B
  have h6 := abs_nonneg A
  have h7 : s * (|A| + |B|) < s * (s * C) := mul_lt_mul_of_pos_left h3 (by linarith)
  nlinarith

variable [IsCMField E] {M : Type} [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M]
  {σ : 𝓞 E →+* 𝓞 E} {r : ℕ}

theorem exists_family (h : M →ₗ[𝓞 E] M →ₛₗ[σ] 𝓞 E) (G : Matrix (Fin r) (Fin r) E)
    (φ : M →ₗ[𝓞 E] (Fin r → E)) (hinj : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (hh : ∀ x y, (h x y : E) = FD.herm G (φ x) (φ y)) (hσ : ∀ a, σ (σ a) = a) (hs : ∀ x y, σ (h x y) = h y x)
    {q : ℕ} (hq : q.Prime) (ρ : 𝓞 E) (hρ : σ ρ = -ρ) (hρq : IsCoprime (2 * ρ) (q : 𝓞 E))
    (hperf : ∀ x, (∀ y, (q : 𝓞 E) ∣ h x y) → ∃ z, x = (q : 𝓞 E) • z) {p : ℕ} (hp : p ≤ r)
    (hsig : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p (a : ℕ) : ℝ) : ℂ)) (k : ℕ) (hk : k ≤ p) :
    ∃ v : Fin k → M, (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ (∀ i (τ : E →+* ℂ), 0 < (τ (h (v i) (v i) : E)).re) ∧
      ∀ i, IsCoprime (h (v i) (v i)) (q : 𝓞 E) := by
  induction k with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
  obtain ⟨v, ho, hpos, hc⟩ := ih (by omega)
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨N, m, hN, hm⟩ := exists_nat_mul hq (fun i => h (v i) (v i))
    (fun i h0 => by have := hpos i τ₀; rw [h0] at this; simp at this) hc
  have hN0 : N ≠ 0 := by rintro rfl; exact hN (dvd_zero q)
  have hNE : (N : E) ≠ 0 := by exact_mod_cast hN0
  obtain ⟨π, e, π1, π2, π3⟩ := exists_proj h v m N (map_natCast σ N) ho hm
  obtain ⟨x, hx⟩ := exists_pos E r p k G (by omega) hp hsig (fun i => φ (v i)) fun i => (m i : E) / N
  have hv : x ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ x hv
  rw [← LinearMap.coe_range, Submodule.span_eq] at ht
  obtain ⟨y, hy⟩ := ht
  have hy' : φ y = ((t : 𝓞 E) : E) • x := hy
  have ht0 : ((t : 𝓞 E) : E) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero t.2
  have hu : ∀ τ : E →+* ℂ, 0 < (τ (h (π y) (π y) : E)).re := fun τ => by
    have e1 : h (π y) (π y) = N * (N * h y y - ∑ i, m i * (h y (v i) * h (v i) y)) := by
      rw [π3 _ (π1 y), e]
      simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, mul_assoc]
    have e2 : (h (π y) (π y) : E) = (N : E) ^ 2 * (((t : 𝓞 E) : E) * FD.cc ((t : 𝓞 E) : E)) *
        (FD.herm G x x - ∑ i, (m i : E) / N * (FD.herm G x (φ (v i)) * FD.herm G (φ (v i)) x)) := by
      rw [e1]
      change algebraMap (𝓞 E) E _ = _
      simp only [map_mul, map_sub, map_sum, map_natCast, hh, hy', herm_smul_left, herm_smul_right]
      rw [mul_sub, mul_sub, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        field_simp
    rw [e2, map_mul, map_mul, map_mul, GlobalTheory.OneSpace.emb_cc, Complex.mul_conj, map_pow, map_natCast]
    have h1 : 0 < Complex.normSq (τ ((t : 𝓞 E) : E)) := Complex.normSq_pos.2 ((_root_.map_ne_zero τ).2 ht0)
    have h2 : (0 : ℝ) < (N : ℝ) ^ 2 * Complex.normSq (τ ((t : 𝓞 E) : E)) := by positivity
    have h3 := mul_pos h2 (hx τ)
    rw [← Complex.re_ofReal_mul] at h3
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast] using h3
  have hq0 : (q : 𝓞 E) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hnot : ∀ (P : Ideal (𝓞 E)) (c : 𝓞 E), P.IsMaximal → (q : 𝓞 E) ∈ P → IsCoprime c (q : 𝓞 E) → c ∉ P := by
    rintro P c hP h1 ⟨a, b, hab⟩ h2
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (hab ▸ P.add_mem (P.mul_mem_left a h2) (P.mul_mem_left b h1)))
  obtain ⟨f, hf, hfq⟩ := exists_isCoprime (𝓞 E) M σ h q (perp h v) hq0 hσ (fun x => hs x x) fun P hP hqP =>
    exists_notMem (𝓞 E) M σ h q ρ N (perp h v) π P
      (fun a z hz => by
        have h1 : (a : E) • φ z = 0 := by
          change a • φ z = 0
          rw [← map_smul, hz, map_zero]
        rcases smul_eq_zero.1 h1 with h2 | h2
        · exact Or.inl (by exact_mod_cast h2)
        · exact Or.inr (hinj (h2.trans (map_zero φ).symm)))
      hP hqP hq0 hρ (hnot P _ hP hqP hρq)
      (hnot P _ hP hqP (Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hq).2 hN).symm))
      (fun h0 => by
        have h1 := π1 y
        have h2 := hu τ₀
        rw [h0, Submodule.mem_bot] at h1
        rw [h1] at h2
        simp at h2)
      hperf π1 π2 π3
  obtain ⟨s, hsτ⟩ := (Filter.eventually_all.2 fun τ : E →+* ℂ => eventually_pos (τ (h f f : E)).re
    (τ ((h f (π y) + h (π y) f : 𝓞 E) : E)).re _ (hu τ) hq.pos).exists
  set w : M := f + ((q * s : ℕ) : 𝓞 E) • π y with hw
  have hwW : w ∈ perp h v := add_mem hf (Submodule.smul_mem _ _ (π1 y))
  have eww : h w w = h f f + ((q * s : ℕ) : 𝓞 E) * (h f (π y) + h (π y) f) +
      ((q * s : ℕ) : 𝓞 E) ^ 2 * h (π y) (π y) := by
    rw [hw]
    simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_natCast]
    ring
  refine ⟨Fin.cons w v, fun i j hij => ?_, fun i τ => ?_, fun i => ?_⟩
  · induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j => exact hwW j
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (hs w (v i)).symm.trans (by rw [hwW i, map_zero])
      | succ j => exact ho i j fun hh => hij (by rw [hh])
  · induction i using Fin.cases with
    | zero =>
      have := hsτ τ
      have e3 : τ (algebraMap (𝓞 E) E (h w w)) = τ (algebraMap (𝓞 E) E (h f f)) +
          (((q * s : ℕ) : ℝ) : ℂ) * τ (algebraMap (𝓞 E) E (h f (π y) + h (π y) f)) +
          ((((q * s : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) * τ (algebraMap (𝓞 E) E (h (π y) (π y))) := by
        rw [eww]
        simp only [map_add, map_mul, map_pow, map_natCast, Complex.ofReal_pow, Complex.ofReal_natCast]
      change 0 < (τ (algebraMap (𝓞 E) E (h w w))).re
      rw [e3, Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      exact this
    | succ i => exact hpos i τ
  · induction i using Fin.cases with
    | zero =>
      change IsCoprime (h w w) _
      have : h w w = h f f + (q : 𝓞 E) * (s * (h f (π y) + h (π y) f) + q * s ^ 2 * h (π y) (π y)) := by
        rw [eww]
        push_cast
        ring
      rw [this]
      exact hfq.add_mul_left_left _
    | succ i => exact hc i

omit [IsCMField E] in
theorem trace_eq_sum_re (z : E) : ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ : E →ₐ[ℚ] ℂ, ((τ : E →+* ℂ) z).re := by
  have := congrArg Complex.re (trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := z))
  rw [Complex.re_sum] at this
  simpa using this

theorem exists_split_prime_to : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (q : ℕ), q.Prime → ¬ q ∣ 2 * H.d * (discr E).natAbs → ∃ (Lp Lm : Submodule (𝓞 E) D.La) (N : ℕ), ¬ q ∣ N ∧ (∀ v : D.La, N • v ∈ Lp ⊔ Lm) ∧ (∀ a ∈ Lp, ∀ b ∈ Lm, D.EF a b = 0) ∧ (∀ a ∈ Lp, 0 ≤ H.rt0.im * D.EF (H.w0 • a) a) ∧ ∀ a ∈ Lm, H.rt0.im * D.EF (H.w0 • a) a ≤ 0 := by
  intro E _ _ _ H D q hq hqd
  have := D.fin
  have hd0 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hdE : (H.d : E) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  have hΔ : discr E ≠ 0 := discr_ne_zero E
  have hΔE : (discr E : E) ≠ 0 := by exact_mod_cast hΔ
  have hrt := GlobalTheory.OneSpace.rt_sq' H
  have hcc := GlobalTheory.OneSpace.cc_rt H
  have him : H.rt0.im ≠ 0 := fun h0 => by
    have := congrArg Complex.re H.sqrt_neg_disc_sq
    simp [pow_two, h0] at this
    nlinarith [mul_self_nonneg H.rt0.re]
  obtain ⟨ε, hε, hεi⟩ : ∃ ε : ℤ, ε * ε = 1 ∧ (ε : ℝ) * H.rt0.im < 0 := by
    rcases lt_or_gt_of_ne him with h | h
    · exact ⟨1, rfl, by simpa using h⟩
    · exact ⟨-1, rfl, by simpa using h⟩
  have hεE : (ε : E) * ε = 1 := by exact_mod_cast hε
  have hε0 : (ε : E) ≠ 0 := left_ne_zero_of_mul_eq_one hεE
  set ξ : E := ε * (H.rt : E) / ((discr E : E) ^ 2 * H.d) with hξdef
  have hξ : FD.cc ξ = -ξ := by
    have h1 : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := hcc
    simp only [hξdef, FD.cc, map_div₀, map_mul, map_pow, map_intCast, map_natCast, h1]
    ring
  have hξ0 : ξ ≠ 0 :=
    div_ne_zero (mul_ne_zero hε0 (GlobalTheory.OneSpace.rt_ne H)) (mul_ne_zero (pow_ne_zero _ hΔE) hdE)
  obtain ⟨G, φ, hM⟩ := GlobalTheory.exists_herm_coord_of_datum E H D ξ hξ hξ0 _ rfl
  obtain ⟨-, -, hint, hdual⟩ := rank_integral_selfDual E H D _ ξ G φ hξ hM
  have hsig : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ, Q.det ≠ 0 ∧
      FD.gram τ G Q = Matrix.diagonal fun a : Fin (D.p + D.q) => ((FD.sgn D.p (a : ℕ) : ℝ) : ℂ) := by
    have key : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → _ := fun τ hτ =>
      (GlobalTheory.HermSign.signature_of_model E H D _ ξ G φ hξ hM τ hτ).2 (by
        have e : τ ξ = ((ε / ((discr E : ℝ) ^ 2 * H.d) : ℝ) : ℂ) * H.rt0 := by
          simp only [hξdef, map_div₀, map_mul, map_pow, map_intCast, map_natCast, hτ]
          push_cast
          ring
        have hΔR : (discr E : ℝ) ≠ 0 := by exact_mod_cast hΔ
        rw [e, Complex.im_ofReal_mul, div_mul_eq_mul_div]
        exact div_neg_of_neg_of_pos hεi (by positivity))
    intro τ
    have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by rw [GlobalTheory.OneSpace.emb_rt_sq, H.sqrt_neg_disc_sq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact key τ h
    · exact GlobalTheory.OneSpace.gram_conj τ G _ (key (ComplexEmbedding.conjugate τ) (by
        rw [ComplexEmbedding.conjugate_coe_eq,
          GlobalTheory.OneSpace.conj_of_sq H.d_prime.pos (GlobalTheory.OneSpace.emb_rt_sq H τ), h, neg_neg]))
  obtain ⟨hinj, hspan, hG, -, hEF⟩ := hM
  have hsm : ∀ (a : 𝓞 E) (x : D.La), φ (a • x) = (a : E) • φ x := fun a x => by
    rw [map_smul]; rfl
  have hI : ∀ x y, ∃ c : 𝓞 E, (c : E) = FD.herm G (φ x) (φ y) := fun x y => by
    obtain ⟨c, hc⟩ : ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = (discr E : E) * (ξ * FD.herm G (φ x) (φ y)) :=
      ⟨⟨_, hint x y⟩, rfl⟩
    refine ⟨-(ε * discr E * H.rt) * c, ?_⟩
    change algebraMap (𝓞 E) E _ = _
    rw [map_mul, map_neg, map_mul, map_mul, map_intCast, map_intCast, hc]
    change -((ε : E) * discr E * (H.rt : E)) * ((discr E : E) * (ξ * FD.herm G (φ x) (φ y))) = _
    rw [hξdef]
    field_simp
    linear_combination (-(FD.herm G (φ x) (φ y)) * (H.rt : E) ^ 2) * hεE - FD.herm G (φ x) (φ y) * hrt
  choose h₀ hh₀ using hI
  have hbar : ∀ a : 𝓞 E, ((H.bar a : 𝓞 E) : E) = FD.cc (a : E) := H.bar_eq
  let σ : 𝓞 E →+* 𝓞 E := H.bar
  let h : D.La →ₗ[𝓞 E] D.La →ₛₗ[σ] 𝓞 E := LinearMap.mk₂'ₛₗ (RingHom.id _) σ h₀
    (fun x y z => RingOfIntegers.ext (by
      rw [RingOfIntegers.coe_eq_algebraMap (_ + _), map_add]
      simp [hh₀, FD.herm, add_mul, Finset.sum_add_distrib]))
    (fun c x y => RingOfIntegers.ext (by
      rw [hh₀, hsm, herm_smul_left, ← hh₀]
      rfl))
    (fun x y z => RingOfIntegers.ext (by
      rw [hh₀, map_add, herm_add_right, ← hh₀, ← hh₀]
      rfl))
    (fun c x y => RingOfIntegers.ext (by
      rw [hh₀, hsm, herm_smul_right, ← hh₀, ← hbar, mul_comm]
      rfl))
  have hh : ∀ x y, (h x y : E) = FD.herm G (φ x) (φ y) := hh₀
  have hσ : ∀ a, σ (σ a) = a := fun a => RingOfIntegers.ext (by
    change ((H.bar (H.bar a) : 𝓞 E) : E) = a
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply])
  have hs : ∀ x y, σ (h x y) = h y x := fun x y => RingOfIntegers.ext (by
    change ((H.bar (h x y) : 𝓞 E) : E) = _
    rw [hbar, hh, hh, FD.herm, FD.herm, Finset.sum_comm]
    have hG' : ∀ a b, IsCMField.complexConj E (G a b) = G b a := hG
    simp only [FD.cc, map_sum, map_mul, hG', IsCMField.complexConj_apply_apply]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)
  have hρ : σ H.rt = -H.rt := RingOfIntegers.ext (by
    change ((H.bar H.rt : 𝓞 E) : E) = _
    rw [hbar, hcc]
    rfl)
  have hco : (2 * H.d * (discr E).natAbs).Coprime q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hqd).symm
  have hρq : IsCoprime (2 * H.rt) (q : 𝓞 E) := by
    have h1 : IsCoprime ((2 * H.d : ℕ) : 𝓞 E) (q : 𝓞 E) := Nat.Coprime.cast (Nat.Coprime.coprime_mul_right hco)
    refine h1.of_isCoprime_of_dvd_left ⟨-H.rt, ?_⟩
    push_cast
    linear_combination 2 * H.rt_sq
  have hD0 : IsCoprime (q : ℤ) (discr E ^ 2 * H.d) := by
    have h1 : IsCoprime (discr E) (q : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]
      exact Nat.Coprime.coprime_mul_left hco
    have h2 : IsCoprime (H.d : ℤ) (q : ℤ) :=
      Nat.Coprime.cast (Nat.Coprime.coprime_mul_left (Nat.Coprime.coprime_mul_right hco))
    exact (h1.pow_left.mul_left h2).symm
  have hqE : (q : E) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hperf : ∀ x, (∀ y, (q : 𝓞 E) ∣ h x y) → ∃ z, x = (q : 𝓞 E) • z := fun x hx => by
    obtain ⟨z, hz⟩ := (hdual ((q : E)⁻¹ • φ x)).1 fun y => by
      obtain ⟨c, hc⟩ := hx y
      have e1 : (discr E ^ 2 * H.d : ℤ) * D.EF x y = q * Algebra.trace ℤ (𝓞 E) (ε * H.rt * c) := by
        have : (((discr E ^ 2 * H.d : ℤ) * D.EF x y : ℤ) : ℚ) =
            ((q * Algebra.trace ℤ (𝓞 E) (ε * H.rt * c) : ℤ) : ℚ) := by
          have ht : ∀ (n : ℤ) (z : E), (n : ℚ) * Algebra.trace ℚ E z = Algebra.trace ℚ E (n * z) := fun n z => by
            rw [← zsmul_eq_mul, ← zsmul_eq_mul, map_zsmul]
          rw [Int.cast_mul, Int.cast_mul (q : ℤ), hEF, Algebra.coe_trace_int, ← hh, hc, ht, ht, hξdef]
          congr 1
          simp only [map_intCast, map_mul, map_natCast, RingOfIntegers.coe_eq_algebraMap]
          push_cast
          field_simp
        exact_mod_cast this
      obtain ⟨n, hn⟩ := hD0.dvd_of_dvd_mul_left ⟨_, e1⟩
      refine ⟨n, ?_⟩
      have e2 : ξ * FD.herm G ((q : E)⁻¹ • φ x) (φ y) = (q : ℚ)⁻¹ • (ξ * FD.herm G (φ x) (φ y)) := by
        rw [herm_smul_left, Algebra.smul_def, map_inv₀, map_natCast]
        ring
      have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
      rw [e2, map_smul, ← hEF, hn, smul_eq_mul]
      push_cast
      field_simp
    refine ⟨z, hinj ?_⟩
    rw [hsm, hz]
    change _ = algebraMap (𝓞 E) E q • _
    rw [map_natCast, smul_inv_smul₀ hqE]
  obtain ⟨v, ho, hpos, hc⟩ := exists_family h G φ hinj hspan hh hσ hs hq H.rt hρ hρq hperf (Nat.le_add_right _ _)
    hsig D.p le_rfl
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨N, m, hN, hm⟩ := exists_nat_mul hq (fun i => h (v i) (v i))
    (fun i h0 => by have := hpos i τ₀; rw [h0] at this; simp at this) hc
  obtain ⟨π, e, π1, -, -⟩ := exists_proj h v m N (map_natCast σ N) ho hm
  have hval : ∀ a, ∃ c : ℝ, 0 < c ∧ H.rt0.im * D.EF (H.w0 • a) a =
      c * ∑ τ : E →ₐ[ℚ] ℂ, ((τ : E →+* ℂ) (h a a : E)).re := fun a => by
    have hΔR : (discr E : ℝ) ≠ 0 := by exact_mod_cast hΔ
    have hΔQ : (discr E : ℚ) ≠ 0 := by exact_mod_cast hΔ
    have h1 : D.EF ((2 * H.w0) • a) a = D.EF ((1 + H.rt) • a) a := by rw [H.two_weight_eq_one_add_root]
    rw [two_mul, add_smul, add_smul, one_smul, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      D.alt, zero_add] at h1
    have h2 := hEF (H.rt • a) a
    have h3 : ξ * FD.herm G (φ (H.rt • a)) (φ a) = (-(ε : ℚ) / (discr E : ℚ) ^ 2) • (h a a : E) := by
      have h5 : ξ * (H.rt : E) = -(ε : E) / (discr E : E) ^ 2 := by
        rw [hξdef, div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hΔE) hdE) (pow_ne_zero _ hΔE)]
        linear_combination (ε * (discr E : E) ^ 2) * hrt
      rw [hsm, herm_smul_left, hh, Algebra.smul_def, ← mul_assoc, h5]
      simp only [map_div₀, map_neg, map_pow, map_intCast]
    rw [h3, ← h1, map_smul (Algebra.trace ℚ E), smul_eq_mul] at h2
    have h4 := congrArg (Rat.cast : ℚ → ℝ) h2
    push_cast at h4
    rw [trace_eq_sum_re] at h4
    refine ⟨-(ε * H.rt0.im) / (2 * (discr E : ℝ) ^ 2), div_pos (by linarith) (by positivity), ?_⟩
    linear_combination (H.rt0.im / 2) * h4
  refine ⟨Submodule.span _ (Set.range v), perp h v, N, hN, fun x => ?_, fun a ha b hb => ?_, fun a ha => ?_,
    fun a ha => ?_⟩
  · have : N • x = ∑ i, (m i * h x (v i)) • v i + π x := by
      rw [e, Nat.cast_smul_eq_nsmul]
      abel
    rw [this]
    exact Submodule.add_mem_sup (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) (π1 x)
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 ha
    have h1 : h (∑ i, c i • v i) b = 0 := by
      rw [← hs, map_sum, Finset.sum_eq_zero fun i _ => by rw [map_smulₛₗ, hb i, smul_zero], map_zero]
    have h2 := hEF (∑ i, c i • v i) b
    rw [← hh, h1] at h2
    generalize ∑ i, c i • v i = z at h2 ⊢
    simpa using h2
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 ha
    obtain ⟨t, ht, e1⟩ := hval (∑ i, c i • v i)
    rw [e1]
    refine mul_nonneg ht.le (Finset.sum_nonneg fun τ _ => ?_)
    rw [sum_orth h c v ho, RingOfIntegers.coe_eq_algebraMap, map_sum, map_sum, Complex.re_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have e2 : algebraMap (𝓞 E) E (σ (c i)) = FD.cc (algebraMap (𝓞 E) E (c i)) := hbar (c i)
    rw [map_mul, map_mul, map_mul, map_mul, e2, GlobalTheory.OneSpace.emb_cc, Complex.mul_conj, Complex.re_ofReal_mul]
    exact mul_nonneg (Complex.normSq_nonneg _) (hpos i _).le
  · obtain ⟨t, ht, e1⟩ := hval a
    rw [e1]
    refine mul_nonpos_of_nonneg_of_nonpos ht.le (Finset.sum_nonpos fun τ _ => not_lt.1 fun hlt => ?_)
    obtain ⟨Q, hQ, hQ'⟩ := hsig τ
    refine not_forall_pos E _ _ G τ Q hQ hQ' (fun i => φ (Fin.cons (α := fun _ => D.La) a v i)) (fun i j hij => ?_)
      fun i => ?_
    · rw [← hh]
      have : h (Fin.cons (α := fun _ => D.La) a v i) (Fin.cons (α := fun _ => D.La) a v j) = 0 := by
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => exact absurd rfl hij
          | succ j => exact ha j
        | succ i =>
          induction j using Fin.cases with
          | zero => exact (hs a (v i)).symm.trans (by rw [ha i, map_zero])
          | succ j => exact ho i j fun hh => hij (by rw [hh])
      rw [this]
      rfl
    · rw [← hh]
      induction i using Fin.cases with
      | zero => exact hlt
      | succ i => exact hpos i _

end GlobalTheory.LatSplitPrime

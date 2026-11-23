import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLinear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace LinearPrimeSection

variable {T : Type} [Fintype T] {k : Type} [Field k]

def ellForm {m : ℕ} (M : T → Fin m → k) (c : T) : MvPolynomial (Option (Fin m)) k :=
  ∑ j, C (M c j) * X (some j)

theorem linPointMap_graphSecond {m : ℕ} (α : T → k) (M : T → Fin m → k) (t : T) :
    linPointMap α M (graphSecond t) = ellForm M t :=
  LinPrimeExample.linPointMap_second α M t

def cutForms {n : ℕ} (M : T → Fin (n + 2) → k) (c : T) (j₀ : Fin (n + 2)) : T → Fin (n + 1) → k :=
  fun t j => M t (j₀.succAbove j) - M t j₀ * (M c (j₀.succAbove j) / M c j₀)

def subst {n : ℕ} (M : T → Fin (n + 2) → k) (c : T) (j₀ : Fin (n + 2)) :
    MvPolynomial (Option (Fin (n + 2))) k →ₐ[k] MvPolynomial (Option (Fin (n + 1))) k :=
  aeval fun o => o.elim (X none) fun j =>
    Fin.insertNth (α := fun _ => MvPolynomial (Option (Fin (n + 1))) k) j₀
      (-∑ j', C (M c (j₀.succAbove j') / M c j₀) * X (some j')) (fun j' => X (some j')) j

def liftBack {n : ℕ} (j₀ : Fin (n + 2)) :
    MvPolynomial (Option (Fin (n + 1))) k →ₐ[k] MvPolynomial (Option (Fin (n + 2))) k :=
  rename (Option.map j₀.succAbove)

theorem ringHom_int_ext {A : Type*} [CommRing A] {T : Type} (f g : MRing (stackedBlocks T) →+* A)
    (h : ∀ i, f (X i) = g (X i)) : f = g := by
  apply MvPolynomial.ringHom_ext _ h
  intro r
  rw [← RingHom.comp_apply, ← RingHom.comp_apply, eq_intCast, eq_intCast]

theorem subst_comp {n : ℕ} (α : T → k) (M : T → Fin (n + 2) → k) (c : T) (j₀ : Fin (n + 2)) :
    (subst M c j₀).toRingHom.comp (linPointMap α M) = linPointMap α (cutForms M c j₀) := by
  apply ringHom_int_ext
  rintro ⟨⟨⟨⟩⟩ | ⟨⟨⟩⟩, t⟩
  · simp [linPointMap, subst]
  · simp only [linPointMap, RingHom.comp_apply, coe_eval₂Hom, eval₂_X, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, map_sum, map_mul, subst, aeval_X, aeval_C, algebraMap_eq, Option.elim]
    rw [Fin.sum_univ_succAbove _ j₀]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, cutForms, map_sub, map_mul,
      sub_mul, Finset.sum_sub_distrib, mul_neg, Finset.mul_sum, mul_assoc]
    ring

omit [Fintype T] in
theorem subst_ellForm {n : ℕ} (M : T → Fin (n + 2) → k) (c : T) (j₀ : Fin (n + 2)) (h : M c j₀ ≠ 0) :
    ∀ f, f - liftBack j₀ (subst M c j₀ f) ∈ Ideal.span {ellForm M c} := by
  set I := Ideal.span {ellForm M c}
  have key : (Ideal.Quotient.mkₐ k I).comp ((liftBack j₀).comp (subst M c j₀)) = Ideal.Quotient.mkₐ k I := by
    apply MvPolynomial.algHom_ext
    rintro (_ | j)
    · simp [subst, liftBack]
    · by_cases hj : j = j₀
      · subst hj
        simp only [AlgHom.comp_apply, subst, aeval_X, Option.elim, Fin.insertNth_apply_same]
        rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton']
        simp only [liftBack, map_neg, map_sum, map_mul, rename_C, rename_X, Option.map_some]
        refine ⟨-C (M c j)⁻¹, ?_⟩
        have e : ∀ j' : Fin (n + 1), C (M c (j.succAbove j') / M c j) * X (some (j.succAbove j')) =
            C (M c j)⁻¹ * (C (M c (j.succAbove j')) * X (some (j.succAbove j'))) := by
          intro j'
          rw [div_eq_mul_inv, C_mul]
          ring
        have hx : C (M c j)⁻¹ * C (M c j) = (1 : MvPolynomial (Option (Fin (n + 2))) k) := by
          rw [← C_mul, inv_mul_cancel₀ h, C_1]
        rw [ellForm, Fin.sum_univ_succAbove _ j]
        simp only [e, ← Finset.mul_sum]
        linear_combination (-X (some j)) * hx
      · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
        simp [subst, liftBack]
  intro f
  rw [← Ideal.Quotient.eq]
  have := congrArg (fun φ => φ f) key
  simpa using this.symm

omit [Fintype T] in
theorem ker_subst_le {n : ℕ} (M : T → Fin (n + 2) → k) (c : T) (j₀ : Fin (n + 2)) (h : M c j₀ ≠ 0)
    (f : MvPolynomial (Option (Fin (n + 2))) k) (hf : subst M c j₀ f = 0) : f ∈ Ideal.span {ellForm M c} := by
  simpa [hf] using subst_ellForm M c j₀ h f

theorem C_mul_u_mem {m : ℕ} (α : T → k) (M : T → Fin m → k) (hα : Submodule.span ℤ (Set.range α) = ⊤) (x : k) :
    C x * X none ∈ (linPointMap α M).range := by
  have hx : x ∈ Submodule.span ℤ (Set.range α) := hα ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨t, rfl⟩ := hy
    exact ⟨graphFirst t, LinPrimeExample.linPointMap_first α M t⟩
  | zero => simp only [map_zero, zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add, add_mul]; exact add_mem hy hz
  | smul a y _ hy => rw [map_zsmul, smul_mul_assoc]; exact zsmul_mem hy a

theorem X_some_eq {m : ℕ} (M : T → Fin m → k) (hM : LinFormsIndep M) (j : Fin m) :
    ∃ c : T → k, (X (some j) : MvPolynomial (Option (Fin m)) k) = ∑ t, C (c t) * ellForm M t := by
  classical
  let L := Matrix.mulVecLin (Matrix.of M)
  have hL : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    apply hM
    intro t
    have := congrFun hw t
    simpa [L, Matrix.mulVec, dotProduct] using this
  obtain ⟨g, hg⟩ := L.exists_leftInverse_of_injective hL
  refine ⟨fun t => g (fun t' => if t = t' then 1 else 0) j, ?_⟩
  have hcoef : ∀ j', ∑ t, g (fun t' => if t = t' then 1 else 0) j * M t j' = if j' = j then 1 else 0 := by
    intro j'
    have h1 := congrArg (fun f => f (Pi.single j' 1) j) hg
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [LinearMap.pi_apply_eq_sum_univ g] at h1
    simp only [L, Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h1
    rw [Pi.single_apply] at h1
    have hs : (if j' = j then (1 : k) else 0) = if j = j' then 1 else 0 := by
      rcases eq_or_ne j' j with rfl | hjj
      · simp
      · simp [hjj, hjj.symm]
    rw [hs, ← h1]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [Matrix.col, mul_comm]
  calc (X (some j) : MvPolynomial (Option (Fin m)) k)
      = ∑ j', C (if j' = j then (1 : k) else 0) * X (some j') := by
        simp [apply_ite C]
    _ = ∑ j', C (∑ t, g (fun t' => if t = t' then 1 else 0) j * M t j') * X (some j') := by
        simp_rw [hcoef]
    _ = ∑ t, C (g (fun t' => if t = t' then 1 else 0) j) * ellForm M t := by
        simp only [ellForm, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm

theorem mul_mem_range {m : ℕ} (α : T → k) (M : T → Fin m → k) (hα : Submodule.span ℤ (Set.range α) = ⊤)
    (hM : LinFormsIndep M) (q : MvPolynomial (Option (Fin m)) k) :
    ∃ N : ℕ, ∀ x : k, C x * X none ^ (N + 1) * q ∈ (linPointMap α M).range := by
  set R := (linPointMap α M).range
  have hu : (X none : MvPolynomial (Option (Fin m)) k) ∈ R := by
    have := C_mul_u_mem α M hα 1
    rwa [map_one, one_mul] at this
  have mono : ∀ (q : MvPolynomial (Option (Fin m)) k) (N : ℕ), (∀ x : k, C x * X none ^ (N + 1) * q ∈ R) →
      ∀ d, ∀ x : k, C x * X none ^ (N + d + 1) * q ∈ R := by
    intro q N hN d
    induction d with
    | zero => simpa using hN
    | succ d ih =>
      intro x
      have := R.mul_mem hu (ih x)
      convert this using 1
      ring
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, fun x => ?_⟩
    convert C_mul_u_mem α M hα (x * a) using 1
    rw [C_mul]
    ring
  | add p q hp hq =>
    obtain ⟨N₁, h₁⟩ := hp
    obtain ⟨N₂, h₂⟩ := hq
    refine ⟨N₁ + N₂, fun x => ?_⟩
    rw [mul_add]
    refine R.add_mem (mono p N₁ h₁ N₂ x) ?_
    have := mono q N₂ h₂ N₁ x
    rwa [add_comm N₂ N₁] at this
  | mul_X p v hp =>
    obtain ⟨N, hN⟩ := hp
    refine ⟨N, fun x => ?_⟩
    cases v with
    | none =>
      have := R.mul_mem (hN x) hu
      convert this using 1
      ring
    | some j =>
      obtain ⟨c, hc⟩ := X_some_eq M hM j
      have : C x * X none ^ (N + 1) * (p * X (some j)) =
          ∑ t, (C (x * c t) * X none ^ (N + 1) * p) * linPointMap α M (graphSecond t) := by
        rw [hc, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [linPointMap_graphSecond, C_mul]
        ring
      rw [this]
      exact sum_mem fun t _ => R.mul_mem (hN _) (RingHom.mem_range_self _ _)

theorem key {n : ℕ} (α : T → k) (M : T → Fin (n + 2) → k) (hα : Submodule.span ℤ (Set.range α) = ⊤)
    (hM : LinFormsIndep M) (c : T) (j₀ : Fin (n + 2)) (h : M c j₀ ≠ 0) (s : T)
    (g : MRing (stackedBlocks T)) (hg : g ∈ linPrime α (cutForms M c j₀)) :
    ∃ (N : ℕ) (h' : MRing (stackedBlocks T)), graphFirst s ^ N * g - graphSecond c * h' ∈ linPrime α M := by
  have h1 : subst M c j₀ (linPointMap α M g) = 0 := by
    rw [linPrime, RingHom.mem_ker, ← subst_comp] at hg
    exact hg
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (ker_subst_le M c j₀ h _ h1)
  obtain ⟨N, hN⟩ := mul_mem_range α M hα hM a
  obtain ⟨h', hh'⟩ := hN (α s ^ (N + 1))
  refine ⟨N + 1, h', ?_⟩
  rw [linPrime, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow, LinPrimeExample.linPointMap_first,
    linPointMap_graphSecond, hh', ← ha, map_pow]
  ring

omit [Fintype T] in

theorem cutForms_indep {n : ℕ} (M : T → Fin (n + 2) → k) (hM : LinFormsIndep M) (c : T) (j₀ : Fin (n + 2)) :
    LinFormsIndep (cutForms M c j₀) := by
  intro w hw
  set v : Fin (n + 2) → k := Fin.insertNth j₀ (-∑ j', M c (j₀.succAbove j') / M c j₀ * w j') w with hv
  have hv0 : v = 0 := by
    apply hM
    intro t
    rw [Fin.sum_univ_succAbove _ j₀]
    simp only [hv, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    have := hw t
    simp only [cutForms] at this
    rw [← this]
    simp only [sub_mul, Finset.sum_sub_distrib, mul_neg, Finset.mul_sum, mul_assoc]
    ring
  funext j'
  have := congrFun hv0 (j₀.succAbove j')
  simpa [hv] using this

theorem main {n : ℕ} (α : T → k) (M : T → Fin (n + 2) → k) (hα : Submodule.span ℤ (Set.range α) = ⊤)
    (hM : LinFormsIndep M) (c : T) (hc : graphSecond c ∉ linPrime α M) :
    ∃ M' : T → Fin (n + 1) → k, LinFormsIndep M' ∧
      divSupp (linPrime α M) (graphSecond c) = {linPrime α M'} ∧
      multAt (linPrime α M ⊔ Ideal.span {graphSecond c}) (linPrime α M') = 1 := by
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, M c j₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hc
    rw [linPrime, RingHom.mem_ker, linPointMap_graphSecond, ellForm]
    simp [hall]
  have hInd := cutForms_indep M hM c j₀
  set M' := cutForms M c j₀ with hM'
  set V := linPrime α M with hV
  set W := linPrime α M' with hW
  set J := V ⊔ Ideal.span {graphSecond c} with hJ
  have hcomp : ∀ g, linPointMap α M' g = subst M c j₀ (linPointMap α M g) := by
    intro g
    rw [hM', ← subst_comp]
    rfl
  have hWprime : W.IsPrime := RingHom.ker_isPrime _
  have hVW : V ≤ W := by
    intro g hg
    rw [hV, linPrime, RingHom.mem_ker] at hg
    rw [hW, linPrime, RingHom.mem_ker, hcomp, hg, map_zero]
  have hYc : graphSecond c ∈ W := by
    rw [hW, linPrime, RingHom.mem_ker, linPointMap_graphSecond, ellForm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : M' c j = 0 := by
      simp only [hM', cutForms]
      field_simp
      ring
    rw [this, C_0, zero_mul]
  have hJW : J ≤ W := sup_le hVW ((Ideal.span_singleton_le_iff_mem _).mpr hYc)
  obtain ⟨s₀, hs₀⟩ : ∃ s, α s ≠ 0 := by
    by_contra hall
    push Not at hall
    have hb : Submodule.span ℤ (Set.range α) = ⊥ :=
      Submodule.span_eq_bot.mpr (by rintro _ ⟨t, rfl⟩; exact hall t)
    rw [hb] at hα
    exact bot_ne_top hα
  have hX : ∀ s, α s ≠ 0 → graphFirst s ∉ W := by
    intro s hs hmem
    rw [hW, linPrime, RingHom.mem_ker, LinPrimeExample.linPointMap_first] at hmem
    simp [hs] at hmem
  have hJmem : ∀ s g, g ∈ W → ∃ N, graphFirst s ^ N * g ∈ J := by
    intro s g hg
    obtain ⟨N, h', hmem⟩ := key α M hα hM c j₀ hj₀ s g hg
    refine ⟨N, ?_⟩
    have := J.add_mem (Ideal.mem_sup_left hmem)
      (Ideal.mem_sup_right (Ideal.mul_mem_right h' _ (Ideal.mem_span_singleton_self (graphSecond c))))
    simpa using this
  have absorb : ∀ P : Ideal (MRing (stackedBlocks T)), P.IsPrime → J ≤ P → ∀ s, graphFirst s ∉ P → W ≤ P := by
    intro P hP hJP s hs g hg
    obtain ⟨N, hN⟩ := hJmem s g hg
    rcases hP.mem_or_mem (hJP hN) with h4 | h4
    · exact absurd (hP.mem_of_pow_mem N h4) hs
    · exact h4
  have hMin : W ∈ J.minimalPrimes :=
    ⟨⟨hWprime, hJW⟩, fun Q hQ hQW => absorb Q hQ.1 hQ.2 s₀ fun h => hX s₀ hs₀ (hQW h)⟩
  have hRel : IsRelevant W := by
    rintro (⟨⟩ | ⟨⟩)
    · exact ⟨s₀, hX s₀ hs₀⟩
    · by_contra hall
      push Not at hall
      have hw := hInd (Pi.single 0 1) fun t => by
        have h1 := hall t
        rw [hW, linPrime, RingHom.mem_ker] at h1
        have h2 := congrArg (MvPolynomial.eval fun o : Option (Fin (n + 1)) =>
          o.elim (0 : k) (Pi.single (0 : Fin (n + 1)) (1 : k))) h1
        simpa [linPointMap] using h2
      simpa using congrFun hw 0
  refine ⟨M', hInd, ?_, ?_⟩
  · ext P
    rw [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hPmin, hPrel⟩
      obtain ⟨i, hi⟩ := hPrel (Sum.inl ())
      have hWP : W ≤ P := absorb P hPmin.1.1 hPmin.1.2 i hi
      exact le_antisymm (hPmin.2 ⟨hWprime, hJW⟩ hWP) hWP
    · rintro rfl
      exact ⟨hMin, hRel⟩
  · unfold multAt
    rw [dif_pos hWprime]
    have := hWprime
    have hsimple : IsSimpleModule (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRing (stackedBlocks T) ⧸ J)) := by
      rw [isSimpleModule_iff_toSpanSingleton_surjective]
      refine ⟨⟨⟨LocalizedModule.mk 1 1, 0, fun h0 => ?_⟩⟩, ?_⟩
      · rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h0
        obtain ⟨u, hu⟩ := h0
        simp only [one_smul, smul_zero, Submonoid.smul_def, Algebra.smul_def, mul_one,
          Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hu
        exact u.2 (hJW hu)
      · intro x hx y
        induction x using LocalizedModule.induction_on with
        | h m s =>
        induction y using LocalizedModule.induction_on with
        | h m' s' =>
        obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective m
        obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective m'
        have hg : g ∉ W := by
          intro hgW
          apply hx
          obtain ⟨N, hN⟩ := hJmem s₀ g hgW
          rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
          refine ⟨⟨graphFirst s₀ ^ N, fun h => hX s₀ hs₀ (hWprime.mem_of_pow_mem N h)⟩, ?_⟩
          simp only [smul_zero, Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
            Ideal.Quotient.eq_zero_iff_mem]
          have := J.mul_mem_left (s : MRing (stackedBlocks T)) hN
          convert this using 1
          ring
        refine ⟨Localization.mk (g' * s) ⟨g * s', W.primeCompl.mul_mem hg s'.2⟩, ?_⟩
        rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
        refine ⟨1, ?_⟩
        simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def,
          Ideal.Quotient.algebraMap_eq, ← map_mul]
        congr 1
        ring
    rw [Module.length_eq_one]
    rfl

end LinearPrimeSection

theorem LinPrimeCut.proof : LinPrimeCut.Statement :=
  fun _ _ _ _ _ α M hα hM c hc => LinearPrimeSection.main α M hα hM c hc

end

end GroundTheory.Heights₂.Heights

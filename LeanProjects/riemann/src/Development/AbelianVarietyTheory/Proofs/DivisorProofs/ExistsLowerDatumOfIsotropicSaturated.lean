import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIntEqFinrankRingOfIntegersMul
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.PEqQOfNeg

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.LowDat.Quot

theorem exists_induced {V P V' : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup P] [Module ℝ P]
    [AddCommGroup V'] [Module ℝ V'] [FiniteDimensional ℝ V] [FiniteDimensional ℝ V']
    (B : LinearMap.BilinForm ℝ V) (B' : LinearMap.BilinForm ℝ V') (J : V →ₗ[ℝ] V)
    (skew : ∀ x y, B x y = -B y x) (hJ : ∀ x, J (J x) = -x) (hB : ∀ x y, B (J x) (J y) = B x y)
    (pos : ∀ x, x ≠ 0 → 0 < B (J x) x) (i : P →ₗ[ℝ] V) (π : P →ₗ[ℝ] V') (hi : Function.Injective i)
    (hπ : Function.Surjective π) (hBB : ∀ x y, B' (π x) (π y) = B (i x) (i y))
    (hr : ∀ y, (∀ x, π x = 0 → B y (i x) = 0) → ∃ x, i x = y) :
    ∃ J' : V' →ₗ[ℝ] V', (∀ x, J' (J' x) = -x) ∧ (∀ x y, B' (J' x) (J' y) = B' x y) ∧
      (∀ x, x ≠ 0 → 0 < B' (J' x) x) ∧
      ∀ (A : V →ₗ[ℝ] V) (AP : P →ₗ[ℝ] P) (A' : V' →ₗ[ℝ] V'), (∀ x, i (AP x) = A (i x)) → (∀ x, π (AP x) = A' (π x)) →
        J ∘ₗ A = A ∘ₗ J → J' ∘ₗ A' = A' ∘ₗ J' ∧ LinearMap.trace ℝ _ (J' ∘ₗ A') = LinearMap.trace ℝ _ (J ∘ₗ A) := by
  let U : Submodule ℝ V := (LinearMap.ker π).map i
  have hU : ∀ u, u ∈ U ↔ ∃ x, π x = 0 ∧ i x = u := fun u => Iff.rfl
  have hiU : ∀ x, ∀ u ∈ U, B (i x) u = 0 := by
    rintro x _ ⟨y, hy, rfl⟩
    rw [← hBB, LinearMap.mem_ker.1 hy, map_zero]
  have hUU : ∀ v ∈ U, ∀ u ∈ U, B v u = 0 := by
    rintro _ ⟨y, -, rfl⟩
    exact hiU y
  have hr' : ∀ y, (∀ u ∈ U, B y u = 0) → ∃ x, i x = y := fun y h => hr y fun x hx => h _ ⟨x, hx, rfl⟩
  have hsym : ∀ x y, B (J x) y = B (J y) x := fun x y => by
    rw [← hB, hJ, skew (J y) x]; simp
  have hdef : ∀ x, B (J x) x = 0 → x = 0 := fun x h => by
    by_contra h0
    exact (pos x h0).ne' h
  let g : LinearMap.BilinForm ℝ V := B ∘ₗ J
  have hc : IsCompl U (g.orthogonal U) := by
    rw [LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint (fun x y h => (hsym y x).trans h), Submodule.disjoint_def]
    exact fun x hx hx' => hdef x (hx' x hx)
  let p : V →ₗ[ℝ] V := U.projection _ hc
  have pU : ∀ x, p x ∈ U := fun x => Submodule.projection_apply_mem hc x
  have pid : ∀ u ∈ U, p u = u := fun u hu => Submodule.projection_apply_of_mem_left hc hu
  have p0 : ∀ x, p x = 0 ↔ ∀ u ∈ U, B (J x) u = 0 := fun x => by
    rw [Submodule.projection_apply_eq_zero_iff]
    exact forall₂_congr fun u _ => by rw [hsym]; rfl
  have pB : ∀ x, ∀ u ∈ U, B (J (p x)) u = B (J x) u := fun x u hu => by
    have := (p0 (x - p x)).1 (by rw [map_sub, pid _ (pU x), sub_self]) u hu
    simp only [map_sub, LinearMap.sub_apply] at this
    linarith
  have pJ : ∀ y, (∀ u ∈ U, B y u = 0) → p (J y) = 0 := fun y h => (p0 _).2 fun u hu => by
    rw [hJ, map_neg, LinearMap.neg_apply, h u hu, neg_zero]
  let Q : V →ₗ[ℝ] V := LinearMap.id - p + J ∘ₗ p ∘ₗ J
  have hQ : ∀ x, Q x = x - p x + J (p (J x)) := fun x => rfl
  have QB : ∀ x, ∀ u ∈ U, B (Q x) u = 0 := fun x u hu => by
    rw [hQ]
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    rw [pB _ u hu, hJ, hUU _ (pU x) u hu]
    simp
  have QJ : ∀ x, Q (J x) = J (Q x) := fun x => by
    simp only [hQ, hJ, map_neg, map_add, map_sub]; abel
  have Qi : ∀ x, Q (i x) = i x - p (i x) := fun x => by rw [hQ, pJ _ (hiU x), map_zero, add_zero]
  have QU : ∀ u ∈ U, Q u = 0 := fun u hu => by rw [hQ, pJ _ (hUU u hu), pid u hu]; simp
  have QW : ∀ w, (∀ u ∈ U, B w u = 0) → (∀ u ∈ U, B (J w) u = 0) → Q w = w := fun w h h' => by
    rw [hQ, pJ _ h, (p0 w).2 h']; simp
  have QQ : ∀ x, Q (Q x) = Q x := fun x => QW _ (QB x) (by rw [← QJ]; exact QB _)
  obtain ⟨l, hl⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  have hl' : ∀ x, l (i x) = x := fun x => LinearMap.congr_fun hl x
  have il : ∀ x, i (l (Q x)) = Q x := fun x => by
    obtain ⟨y, hy⟩ := hr' _ (QB x)
    rw [← hy, hl']
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hπ)
  have hs' : ∀ x, π (s x) = x := fun x => LinearMap.congr_fun hs x
  let σ : V' →ₗ[ℝ] V := Q ∘ₗ i ∘ₗ s
  let ρ : V →ₗ[ℝ] V' := π ∘ₗ l ∘ₗ Q
  have σπ : ∀ x, σ (π x) = Q (i x) := fun x => by
    have := QU (i (s (π x) - x)) ⟨_, by simp [hs'], rfl⟩
    rw [map_sub, map_sub, sub_eq_zero] at this
    exact this
  have σρ : ∀ x, σ (ρ x) = Q x := fun x => (σπ (l (Q x))).trans (by rw [il, QQ])
  have Qσ : ∀ v, Q (σ v) = σ v := fun v => QQ _
  have ρσ : ∀ v, ρ (σ v) = v := fun v => by
    obtain ⟨x, rfl⟩ := hπ v
    obtain ⟨z, hz, hz'⟩ := pU (i x)
    change π (l (Q (σ (π x)))) = _
    rw [Qσ, σπ, Qi, ← hz', ← map_sub, hl', map_sub, LinearMap.mem_ker.1 hz, sub_zero]
  have σinj : Function.Injective σ := Function.LeftInverse.injective ρσ
  have Bσ : ∀ v w, B (σ v) (σ w) = B' v w := fun v w => by
    obtain ⟨x, rfl⟩ := hπ v
    obtain ⟨y, rfl⟩ := hπ w
    rw [σπ, σπ, hBB, Qi y, map_sub, QB _ _ (pU _), Qi, map_sub, LinearMap.sub_apply, skew (p _), hiU _ _ (pU _)]
    simp
  let J' : V' →ₗ[ℝ] V' := ρ ∘ₗ J ∘ₗ σ
  have σJ : ∀ v, σ (J' v) = J (σ v) := fun v => (σρ (J (σ v))).trans (by rw [QJ, Qσ])
  refine ⟨J', fun x => σinj ?_, fun x y => ?_, fun x hx => ?_, fun A AP A' h1 h2 h3 => ?_⟩
  · rw [σJ, σJ, hJ, map_neg]
  · rw [← Bσ, σJ, σJ, hB, Bσ]
  · rw [← Bσ, σJ]
    exact pos _ fun h => hx (σinj (by rw [h, map_zero]))
  have c : ∀ x, J (A x) = A (J x) := fun x => LinearMap.congr_fun h3 x
  have AU : ∀ u ∈ U, A u ∈ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨AP y, by rw [SetLike.mem_coe, LinearMap.mem_ker, h2, LinearMap.mem_ker.1 hy, map_zero], h1 y⟩
  have AQ : ∀ x, ∀ u ∈ U, B (A (Q x)) u = 0 := fun x => by
    rw [← il, ← h1]; exact hiU _
  have QA : ∀ x, Q (A (Q x)) = A (Q x) := fun x => QW _ (AQ x) (by rw [c, ← QJ]; exact AQ _)
  have σA : ∀ v, σ (A' v) = A (σ v) := fun v => by
    obtain ⟨x, rfl⟩ := hπ v
    rw [← h2, σπ, σπ, ← QA, h1, Qi x, map_sub, map_sub, QU _ (AU _ (pU _)), sub_zero]
  refine ⟨LinearMap.ext fun x => σinj ?_, ?_⟩
  · simp only [LinearMap.comp_apply, σJ, σA, c]
  have e1 : J' ∘ₗ A' = ρ ∘ₗ (J ∘ₗ A ∘ₗ σ) := LinearMap.ext fun x => by
    change ρ (J (σ (A' x))) = _
    rw [σA]; rfl
  have e2 : (J ∘ₗ A ∘ₗ σ) ∘ₗ ρ = J ∘ₗ A - (J ∘ₗ A) ∘ₗ p + ((J ∘ₗ A) ∘ₗ J ∘ₗ p) ∘ₗ J := LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, σρ, hQ, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  have e3 : LinearMap.trace ℝ V ((J ∘ₗ A) ∘ₗ p) = 0 := by
    have a1 : (J ∘ₗ A) ∘ₗ p = ((J ∘ₗ A) ∘ₗ p) ∘ₗ p := LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, pid _ (pU x)]
    have a2 : p ∘ₗ ((J ∘ₗ A) ∘ₗ p) = 0 := LinearMap.ext fun x => pJ _ (hUU _ (AU _ (pU x)))
    rw [a1, LinearMap.trace_comp_comm', a2, map_zero]
  have e4 : J ∘ₗ ((J ∘ₗ A) ∘ₗ J ∘ₗ p) = -((J ∘ₗ A) ∘ₗ p) := LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, hJ, c, map_neg]
  rw [e1, LinearMap.trace_comp_comm', e2, map_add, map_sub, e3, LinearMap.trace_comp_comm' J, e4, map_neg, e3]
  simp

theorem free_of_nsmul {M : Type} [AddCommGroup M] [Module.Finite ℤ M]
    (h : ∀ (n : ℕ) (x : M), n ≠ 0 → n • x = 0 → x = 0) : Module.Free ℤ M := by
  have : Module.IsTorsionFree ℤ M := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun a z hz => or_iff_not_imp_left.2 fun ha => ?_
    refine h a.natAbs z (by simpa using ha) ?_
    rw [← natCast_zsmul]
    rcases Int.natAbs_eq a with e | e
    · rwa [← e]
    · rw [e, neg_smul] at hz; exact neg_eq_zero.1 hz
  infer_instance

theorem free_quot {L : Type} [AddCommGroup L] [Module.Finite ℤ L] (N : Submodule ℤ L)
    (h : ∀ (n : ℕ) (x : L), n ≠ 0 → n • x ∈ N → x ∈ N) : Module.Free ℤ (L ⧸ N) := by
  refine free_of_nsmul fun n z hn hz => ?_
  obtain ⟨x, rfl⟩ := N.mkQ_surjective z
  rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact h n x hn hz

theorem exists_extend {L P : Type} [AddCommGroup L] [AddCommGroup P] [Module.Finite ℤ L] (i : P →ₗ[ℤ] L)
    (hi : Function.Injective i) (h : ∀ (n : ℕ) (x : L), n ≠ 0 → (∃ y, i y = n • x) → ∃ y, i y = x) (φ : P →ₗ[ℤ] ℤ) :
    ∃ ψ : L →ₗ[ℤ] ℤ, ∀ x, ψ (i x) = φ x := by
  let N := LinearMap.range i
  have := free_quot N h
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hs' : ∀ x, N.mkQ (s x) = x := fun x => LinearMap.congr_fun hs x
  let r : L →ₗ[ℤ] N := LinearMap.codRestrict N (LinearMap.id - s ∘ₗ N.mkQ) fun x => by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, LinearMap.sub_apply, map_sub, LinearMap.comp_apply, hs']
    exact sub_self _
  refine ⟨φ ∘ₗ (LinearEquiv.ofInjective i hi).symm.toLinearMap ∘ₗ r, fun x => ?_⟩
  have : r (i x) = LinearEquiv.ofInjective i hi x := Subtype.ext (by
    have h0 : N.mkQ (i x) = 0 := (Submodule.Quotient.mk_eq_zero N).2 ⟨x, rfl⟩
    change i x - s (N.mkQ (i x)) = i x
    rw [h0, map_zero, sub_zero])
  simp [this]

theorem finrank_exact {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module.Finite ℤ B]
    (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C) (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : ∀ y, g y = 0 ↔ ∃ x, f x = y) : Module.finrank ℤ B = Module.finrank ℤ A + Module.finrank ℤ C := by
  have e : LinearMap.range f = LinearMap.ker g := Submodule.ext fun y => (h y).symm
  rw [← (LinearMap.ker g).finrank_quotient_add_finrank, (g.quotKerEquivOfSurjective hg).finrank_eq, ← e,
    (LinearEquiv.ofInjective f hf).finrank_eq, add_comm]

theorem trace_act {E : Type} [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M]
    [Module.Finite ℤ M] [Module.Free ℤ M] (a : 𝓞 E) (A : ℝ ⊗[ℤ] M →ₗ[ℝ] ℝ ⊗[ℤ] M)
    (hA : ∀ x : M, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) :
    LinearMap.trace ℝ _ A = Module.finrank (𝓞 E) M * (Algebra.trace ℤ (𝓞 E) a : ℤ) := by
  classical
  have : Module.Finite (𝓞 E) M := Module.Finite.of_restrictScalars_finite ℤ _ _
  set n := Module.finrank (𝓞 E) M with hn
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hn.le
  let φ : (Fin n → 𝓞 E) →ₗ[𝓞 E] M := Fintype.linearCombination (𝓞 E) v
  have hφ : Function.Injective φ := linearIndependent_iff_injective_fintypeLinearCombination.1 hv
  let f : ℝ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℝ] ℝ ⊗[ℤ] M := (φ.restrictScalars ℤ).baseChange ℝ
  have hf : Function.Injective f := Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) (φ.restrictScalars ℤ) hφ
  have hd : Module.finrank ℝ (ℝ ⊗[ℤ] (Fin n → 𝓞 E)) = Module.finrank ℝ (ℝ ⊗[ℤ] M) := by
    rw [Module.finrank_baseChange, Module.finrank_baseChange, finrank_int_eq_finrank_ringOfIntegers_mul E M,
      finrank_int_eq_finrank_ringOfIntegers_mul E]
    simp [hn]
  let e := LinearMap.linearEquivOfInjective f hf hd
  let m : (Fin n → 𝓞 E) →ₗ[ℤ] (Fin n → 𝓞 E) := (LinearMap.lsmul (𝓞 E) _ a).restrictScalars ℤ
  have hAe : A = e.conj (m.baseChange ℝ) := by
    have : A ∘ₗ f = f ∘ₗ m.baseChange ℝ := by
      ext x
      simp [f, m, hA]
    refine LinearMap.ext fun x => ?_
    obtain ⟨x, rfl⟩ := e.surjective x
    rw [LinearEquiv.conj_apply_apply, e.symm_apply_apply]
    exact LinearMap.congr_fun this x
  have hm : m = ∑ k : Fin n, LinearMap.single ℤ (fun _ : Fin n => 𝓞 E) k ∘ₗ (LinearMap.mulLeft ℤ a ∘ₗ LinearMap.proj k) := by
    refine LinearMap.ext fun x => funext fun j => ?_
    simp [m, Pi.single_apply]
  have ht : LinearMap.trace ℤ _ m = n * Algebra.trace ℤ (𝓞 E) a := by
    rw [hm, map_sum, Finset.sum_congr rfl (g := fun _ => Algebra.trace ℤ (𝓞 E) a)]
    · simp
    · intro k _
      rw [LinearMap.trace_comp_comm']
      have : (LinearMap.mulLeft ℤ a ∘ₗ LinearMap.proj k) ∘ₗ LinearMap.single ℤ (fun _ : Fin n => 𝓞 E) k =
          LinearMap.mulLeft ℤ a := by ext; simp
      rw [this]; rfl
  rw [hAe, LinearMap.trace_conj', LinearMap.trace_baseChange, ht]
  simp

theorem mem_range_of_orth {L P : Type} [AddCommGroup L] [AddCommGroup P] (B : LinearMap.BilinForm ℤ L) {ι : Type} [Fintype ι]
    (z : ι → L) (i : P →ₗ[ℤ] L) (hi : ∀ y, (∀ j, B y (z j) = 0) ↔ ∃ x, i x = y) (y : ℝ ⊗[ℤ] L)
    (hy : ∀ j, B.baseChange ℝ y (1 ⊗ₜ z j) = 0) : ∃ x, i.baseChange ℝ x = y := by
  classical
  let g : L →ₗ[ℤ] (ι → ℤ) := LinearMap.pi fun j => B.flip (z j)
  have hex : Function.Exact i g := fun y => by
    rw [Set.mem_range, ← hi, funext_iff]; rfl
  have h2 := Module.Flat.lTensor_exact ℝ hex y
  refine h2.1 ((TensorProduct.piScalarRight ℤ ℝ ℝ ι).injective ?_)
  rw [map_zero]
  funext j
  rw [Pi.zero_apply, ← hy j]
  clear hy h2
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, Pi.add_apply, LinearMap.add_apply, ha, hb]
  | tmul r x => simp [g]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem two_re (H : Host E) (p q : ℕ) (a : 𝓞 E) :
    2 * (∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
      ((p : ℂ) * τ (a : E) + (q : ℂ) * starRingEnd ℂ (τ (a : E)))).re =
      ((p + q : ℕ) : ℝ) * (Algebra.trace ℤ (𝓞 E) a : ℤ) := by
  have h := congrArg Complex.re (HostModel.sum_add_conj_eq_trace H a)
  rw [Complex.intCast_re] at h
  rw [← h, Complex.re_sum, Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp; ring

theorem im_eq (H : Host E) (p q : ℕ) (a : 𝓞 E) :
    (∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
      ((p : ℂ) * τ (a : E) + (q : ℂ) * starRingEnd ℂ (τ (a : E)))).im =
      ((p : ℝ) - q) * ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0), (τ (a : E)).im := by
  rw [Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp; ring

theorem baseChange_form {L M N : Type} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    (B : LinearMap.BilinForm ℤ M) (C : LinearMap.BilinForm ℤ N) (f : L →ₗ[ℤ] M) (g : L →ₗ[ℤ] N)
    (h : ∀ x y, B (f x) (f y) = C (g x) (g y)) (x y : ℝ ⊗[ℤ] L) :
    B.baseChange ℝ (f.baseChange ℝ x) (f.baseChange ℝ y) = C.baseChange ℝ (g.baseChange ℝ x) (g.baseChange ℝ y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul r u =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul s v => simp [h]

theorem baseChange_skew {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (h : ∀ x y, B x y = -B y x)
    (x y : ℝ ⊗[ℤ] L) : B.baseChange ℝ x y = -B.baseChange ℝ y x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]; ring
  | tmul r u =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]; ring
    | tmul s v => simp [h u v, mul_comm]

def act (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (a : 𝓞 E) : ℝ ⊗[ℤ] M →ₗ[ℝ] ℝ ⊗[ℤ] M :=
  ((DistribSMul.toAddMonoidHom M a).toIntLinearMap).baseChange ℝ

omit [NumberField E] [IsCMField E] in
theorem act_tmul (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (a : 𝓞 E) (r : ℝ) (x : M) :
    act M a (r ⊗ₜ x) = r ⊗ₜ (a • x) := rfl

omit [NumberField E] [IsCMField E] in
theorem eq_act {M : Type} [AddCommGroup M] [Module (𝓞 E) M] (a : 𝓞 E) (A : ℝ ⊗[ℤ] M →ₗ[ℝ] ℝ ⊗[ℤ] M)
    (h : ∀ x : M, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) : A = act M a := by
  ext x
  simp [h, act_tmul]

omit [NumberField E] [IsCMField E] in
theorem act_comm {M N : Type} [AddCommGroup M] [Module (𝓞 E) M] [AddCommGroup N] [Module (𝓞 E) N] (a : 𝓞 E)
    (f : M →ₗ[ℤ] N) (h : ∀ x, f (a • x) = a • f x) (x : ℝ ⊗[ℤ] M) :
    f.baseChange ℝ (act M a x) = act N a (f.baseChange ℝ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul r u => simp [act_tmul, h]

theorem act_rt (H : Host E) (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (x : ℝ ⊗[ℤ] M) :
    act M H.rt (act M H.rt x) = -((H.d : ℝ) • x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]; module
  | tmul r x =>
    rw [act_tmul, act_tmul, smul_smul, ← sq, H.rt_sq, neg_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul,
      TensorProduct.tmul_neg, TensorProduct.tmul_smul]

theorem exists_datum (D : Datum H) (Z P L' : Type) [AddCommGroup Z] [Module (𝓞 E) Z] [AddCommGroup P] [Module (𝓞 E) P]
    [AddCommGroup L'] [Module (𝓞 E) L'] (k : Z →ₗ[ℤ] P) (i : P →ₗ[ℤ] D.La) (f : P →ₗ[ℤ] L')
    (ia : ∀ (a : 𝓞 E) x, i (a • x) = a • i x) (fa : ∀ (a : 𝓞 E) x, f (a • x) = a • f x)
    (hk : Function.Injective k) (hi : Function.Injective i) (hf : Function.Surjective f)
    (hkf : ∀ y, f y = 0 ↔ ∃ x, k x = y) (hP : ∀ y, (∀ z, D.EF y (i (k z)) = 0) ↔ ∃ x, i x = y)
    (sat : ∀ (n : ℕ) (x : D.La), n ≠ 0 → (∃ y, i (k y) = n • x) → ∃ y, i (k y) = x) :
    ∃ (D' : Datum H) (e : L' ≃ₗ[𝓞 E] D'.La), (∀ x y, D'.EF (e (f x)) (e (f y)) = D.EF (i x) (i y)) ∧
      D'.p = D.p - Module.finrank (𝓞 E) Z ∧ D'.q = D.q - Module.finrank (𝓞 E) Z := by
  classical
  have := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.Finite ℤ P := Module.Finite.of_injective i hi
  have : Module.Finite ℤ Z := Module.Finite.of_injective k hk
  have : Module.Finite ℤ L' := Module.Finite.of_surjective f hf
  have skew : ∀ x y, D.EF x y = -D.EF y x := fun x y => (LinearMap.IsAlt.neg D.alt y x).symm
  have tfL : ∀ (n : ℕ) (x : D.La), n ≠ 0 → n • x = 0 → x = 0 := fun n x hn hx => D.unimod.1 (by
    refine LinearMap.ext fun y => ?_
    have := congrArg (fun v => D.EF v y) hx
    simpa [hn] using this)
  have : Module.Free ℤ D.La := free_of_nsmul tfL
  have : Module.Free ℤ Z := free_of_nsmul fun n x hn hx => hk (hi (by
    rw [map_zero, map_zero]; exact tfL n _ hn (by rw [← map_nsmul, ← map_nsmul, hx, map_zero, map_zero])))
  have tfL' : ∀ (n : ℕ) (x : L'), n ≠ 0 → n • x = 0 → x = 0 := fun n x hn hx => by
    obtain ⟨x, rfl⟩ := hf x
    rw [← map_nsmul, hkf] at hx
    obtain ⟨z, hz⟩ := hx
    obtain ⟨w, hw⟩ := sat n (i x) hn ⟨z, by rw [hz, map_nsmul]⟩
    exact (hkf x).2 ⟨w, hi hw⟩
  have : Module.Free ℤ L' := free_of_nsmul tfL'
  have hPZ : ∀ x z, D.EF (i x) (i (k z)) = 0 := fun x => (hP _).2 ⟨x, rfl⟩
  have satP : ∀ (n : ℕ) (x : D.La), n ≠ 0 → (∃ y, i y = n • x) → ∃ y, i y = x := fun n x hn h =>
    (hP x).1 fun z => by simpa [hn] using (hP _).2 h z

  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hs' : ∀ x, f (s x) = x := fun x => LinearMap.congr_fun hs x
  let B' : LinearMap.BilinForm ℤ L' := D.EF.compl₁₂ (i ∘ₗ s) (i ∘ₗ s)
  have hsf : ∀ x, ∃ z, s (f x) = x + k z := fun x => by
    obtain ⟨z, hz⟩ := (hkf (s (f x) - x)).1 (by rw [map_sub, hs', sub_self])
    exact ⟨z, by rw [hz]; abel⟩
  have hB' : ∀ x y, B' (f x) (f y) = D.EF (i x) (i y) := fun x y => by
    obtain ⟨z, hz⟩ := hsf x
    obtain ⟨w, hw⟩ := hsf y
    change D.EF (i (s (f x))) (i (s (f y))) = _
    rw [hw, map_add, map_add, hPZ, hz, map_add, map_add, LinearMap.add_apply, skew (i (k z)), hPZ]
    simp
  have uni : Function.Bijective B' := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro v hv
      obtain ⟨x, rfl⟩ := hf v
      let N := LinearMap.range (i ∘ₗ k)
      have := free_quot N sat
      have h0 : N.mkQ (i x) = 0 := (Module.forall_dual_apply_eq_zero_iff ℤ _).1 fun φ => by
        obtain ⟨y, hy⟩ := D.unimod.2 (φ ∘ₗ N.mkQ)
        obtain ⟨u, rfl⟩ := (hP y).1 fun z => by
          have h1 : N.mkQ (i (k z)) = 0 := (Submodule.Quotient.mk_eq_zero N).2 ⟨z, rfl⟩
          rw [hy, LinearMap.comp_apply, h1, map_zero]
        have h2 : D.EF (i u) (i x) = φ (N.mkQ (i x)) := LinearMap.congr_fun hy _
        rw [← h2, skew, ← hB', hv]
        simp
      obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero N).1 h0
      exact (hkf x).2 ⟨z, hi hz⟩
    · intro ψ
      obtain ⟨χ, hχ⟩ := exists_extend i hi satP (ψ ∘ₗ f)
      obtain ⟨y, rfl⟩ := D.unimod.2 χ
      obtain ⟨x, rfl⟩ := (hP y).1 fun z => by
        rw [hχ, LinearMap.comp_apply, (hkf _).2 ⟨z, rfl⟩, map_zero]
      refine ⟨f x, LinearMap.ext fun v => ?_⟩
      obtain ⟨u, rfl⟩ := hf v
      rw [hB', hχ]; rfl

  have fin' : Module.Finite (𝓞 E) L' := Module.Finite.of_restrictScalars_finite ℤ _ _
  have : Module.IsTorsionFree (𝓞 E) L' := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun a z h => or_iff_not_imp_left.2 fun ha => ?_
    obtain ⟨b, n, hn, h1⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul ℤ (1 : 𝓞 E) ha
    have h2 : (n : 𝓞 E) = b * a := by rw [mul_comm, ← h1]; simp
    have h3 : n • z = 0 := by
      rw [← Int.cast_smul_eq_zsmul (𝓞 E), h2, mul_smul, h, smul_zero]
    exact (smul_eq_zero.1 h3).resolve_left hn
  have : Module.FinitePresentation (𝓞 E) L' := Module.finitePresentation_of_finite _ _
  have proj' : Module.Projective (𝓞 E) L' := Module.Flat.projective_of_finitePresentation

  set r := Module.finrank (𝓞 E) Z with hr
  set m := Module.finrank (𝓞 E) L' with hm
  have hE : 0 < Module.finrank ℚ E := Module.finrank_pos
  have rk : D.p + D.q = m + 2 * r := by
    have h1 := finrank_exact k f hk hf hkf
    have h2 := finrank_exact i ((i ∘ₗ k).dualMap ∘ₗ D.EF) hi (fun φ => by
      obtain ⟨χ, hχ⟩ := exists_extend (i ∘ₗ k) (hi.comp hk) sat φ
      obtain ⟨y, rfl⟩ := D.unimod.2 χ
      exact ⟨y, LinearMap.ext hχ⟩) (fun y => by rw [← hP, LinearMap.ext_iff]; rfl)
    rw [Module.finrank_linearMap_self, h1, finrank_int_eq_finrank_ringOfIntegers_mul E D.La,
      finrank_int_eq_finrank_ringOfIntegers_mul E Z, finrank_int_eq_finrank_ringOfIntegers_mul E L', D.rank] at h2
    apply Nat.eq_of_mul_eq_mul_right hE
    rw [h2]; ring

  obtain ⟨J, hJ1, hJ2, hJ3, hJ4⟩ := D.dom
  obtain ⟨J', k1, k2, k3, k4⟩ := exists_induced (D.EF.baseChange ℝ) (B'.baseChange ℝ) J (baseChange_skew _ skew)
    hJ1 hJ2 hJ3 (i.baseChange ℝ) (f.baseChange ℝ) (Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) i hi)
    (LinearMap.lTensor_surjective ℝ hf) (baseChange_form _ _ _ _ hB') (fun y hy => by
      let b := Module.Free.chooseBasis ℤ Z
      refine mem_range_of_orth D.EF (fun j => i (k (b j))) i (fun y => ?_) y fun j => ?_
      · rw [← hP]
        refine ⟨fun h => ?_, fun h j => h _⟩
        have : D.EF y ∘ₗ i ∘ₗ k = 0 := b.ext h
        exact fun z => LinearMap.congr_fun this z
      · exact hy (1 ⊗ₜ k (b j)) (by rw [LinearMap.baseChange_tmul, (hkf _).2 ⟨_, rfl⟩, TensorProduct.tmul_zero]))
  have k5 : ∀ a : 𝓞 E, J' ∘ₗ act L' a = act L' a ∘ₗ J' ∧ LinearMap.trace ℝ _ (J' ∘ₗ act L' a) =
      -2 * (((D.p : ℝ) - D.q) *
        ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0), (τ (a : E)).im) := fun a => by
    obtain ⟨c1, -, c3⟩ := hJ4 a (act D.La a) _ (fun x => rfl) rfl
    rw [← im_eq, ← c3]
    exact k4 _ (act P a) _ (act_comm a i (ia a)) (act_comm a f (fa a)) c1
  have hle : r ≤ D.p ∧ r ≤ D.q := by
    obtain ⟨c1, c2⟩ := k5 H.rt
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have hs := Real.sqrt_pos.2 hd
    have hss : Real.sqrt H.d * Real.sqrt H.d = H.d := Real.mul_self_sqrt hd.le
    have ht := DatumSign.trace_eq (J' ∘ₗ act L' H.rt) _ hs (fun x => by
      have c : J' (act L' H.rt (J' (act L' H.rt x))) = act L' H.rt (J' (J' (act L' H.rt x))) :=
        LinearMap.congr_fun c1 _
      simp only [LinearMap.comp_apply]
      rw [c, k1, map_neg, act_rt, neg_neg, hss])
    have hb := Submodule.finrank_le (LinearMap.ker (J' ∘ₗ act L' H.rt - Real.sqrt H.d • LinearMap.id))
    generalize Module.finrank ℝ (LinearMap.ker (J' ∘ₗ act L' H.rt - Real.sqrt H.d • LinearMap.id)) = w at ht hb
    set S := Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0) with hS
    have hcard : 2 * (S.card : ℝ) = Module.finrank ℚ E := by
      have := two_re H 1 0 1
      rw [← hS, ← map_one (algebraMap ℤ (𝓞 E)), Algebra.trace_algebraMap, RingOfIntegers.rank] at this
      simpa using this
    rw [Module.finrank_baseChange, finrank_int_eq_finrank_ringOfIntegers_mul E L', ← hm] at ht hb
    rw [c2, Finset.sum_congr rfl (g := fun _ => H.rt0.im) (fun τ hτ => by rw [(Finset.mem_filter.1 hτ).2]),
      Finset.sum_const, nsmul_eq_mul] at ht
    have him : H.rt0.im = Real.sqrt H.d ∨ H.rt0.im = -Real.sqrt H.d := by
      have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
      have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
      simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
        Complex.natCast_im, neg_zero] at h1 h2
      have him : H.rt0.im ≠ 0 := fun h => by rw [h] at h1; nlinarith [mul_self_nonneg H.rt0.re]
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      rw [(mul_eq_zero.1 this).resolve_right him] at h1
      exact mul_self_eq_mul_self_iff.1 (by linarith)
    have hb' : (w : ℝ) ≤ m * Module.finrank ℚ E := by exact_mod_cast hb
    have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg w
    have hE' : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast hE
    have rk' : (D.p : ℝ) + D.q = m + 2 * r := by exact_mod_cast rk
    push_cast at ht
    generalize (Module.finrank ℚ E : ℝ) = g at *
    have key : ((D.p : ℝ) - D.q) * g = 2 * w - m * g ∨ ((D.q : ℝ) - D.p) * g = 2 * w - m * g := by
      rcases him with h | h <;> rw [h] at ht
      · right; apply mul_left_cancel₀ hs.ne'; rw [← ht, ← hcard]; ring
      · left; apply mul_left_cancel₀ hs.ne'; rw [← ht, ← hcard]; ring
    have h1 : (r : ℝ) * g ≤ D.p * g ∧ (r : ℝ) * g ≤ D.q * g := by
      have : ((D.p : ℝ) + D.q) * g = (m + 2 * r) * g := by rw [rk']
      rcases key with h | h <;> constructor <;> linarith
    exact ⟨by exact_mod_cast le_of_mul_le_mul_right h1.1 hE', by exact_mod_cast le_of_mul_le_mul_right h1.2 hE'⟩
  have rk2 : m = D.p - r + (D.q - r) := by omega
  refine ⟨{ La := L', fin := fin', proj := proj', EF := B', alt := fun x => D.alt _, unimod := uni
            adj := fun a x y => ?_, p := D.p - r, q := D.q - r, rank := rk2
            dom := ⟨J', k1, k2, k3, fun a A t hA ht => ?_⟩ }, LinearEquiv.refl _ _, hB', rfl, rfl⟩
  · obtain ⟨x, rfl⟩ := hf x
    obtain ⟨y, rfl⟩ := hf y
    rw [← fa, ← fa, hB', hB', ia, ia, D.adj]
  · refine ⟨?_, ?_, ?_⟩
    · rw [eq_act a A hA]; exact (k5 a).1
    · rw [ht, two_re, trace_act L' a A hA, ← rk2]
    · rw [eq_act a A hA, (k5 a).2, ht, im_eq, Nat.cast_sub hle.1, Nat.cast_sub hle.2]; ring

end GlobalTheory.LowDat.Quot

namespace GlobalTheory.LowDat

theorem exists_lowerDatum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (Z : Submodule (𝓞 E) Dw.La),
  GlobalTheory.LowDat.IsIsoSat Dw Z → ∃ (D' : Datum H) (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La), GlobalTheory.LowDat.IsLower Dw D' Z f ∧
    D'.p = Dw.p - Module.finrank (𝓞 E) Z ∧ D'.q = Dw.q - Module.finrank (𝓞 E) Z := by
  intro E _ _ _ H D Z hZ
  let Z' := Z.comap (perp D Z).subtype
  have h0 : ∀ x : perp D Z, Z'.mkQ x = 0 ↔ (x : D.La) ∈ Z := fun x => Submodule.Quotient.mk_eq_zero Z'
  obtain ⟨D', e, h1, h2⟩ := Quot.exists_datum D Z (perp D Z) (perp D Z ⧸ Z')
    (Submodule.inclusion hZ.1).toAddMonoidHom.toIntLinearMap (perp D Z).subtype.toAddMonoidHom.toIntLinearMap
    Z'.mkQ.toAddMonoidHom.toIntLinearMap (fun _ _ => rfl) (fun _ _ => rfl) (Submodule.inclusion_injective hZ.1)
    Subtype.val_injective Z'.mkQ_surjective
    (fun y => (h0 y).trans ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.2⟩)
    (fun y => ⟨fun h => ⟨⟨y, fun z hz => h ⟨z, hz⟩⟩, rfl⟩, fun ⟨x, hx⟩ z => hx ▸ x.2 z z.2⟩)
    (fun n x hn ⟨y, hy⟩ => ⟨⟨x, hZ.2 n x hn (hy ▸ y.2)⟩, rfl⟩)
  exact ⟨D', e.toLinearMap ∘ₗ Z'.mkQ, ⟨e.surjective.comp Z'.mkQ_surjective,
    fun x => e.map_eq_zero_iff.trans (h0 x), h1⟩, h2⟩

end GlobalTheory.LowDat

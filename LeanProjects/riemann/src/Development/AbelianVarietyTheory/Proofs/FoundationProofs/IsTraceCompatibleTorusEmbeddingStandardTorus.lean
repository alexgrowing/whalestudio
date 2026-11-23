import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaConj

def CjF (D : D7) {N N' : ℕ} (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (F F' : VC D N N' → ℂ) : Prop :=
  Differentiable ℂ F ∧ Differentiable ℂ F' ∧
    ∀ α, taylor D F α ∈ M ∧ taylor D F' α = cj M ρ (taylor D F α)

def LaS (D : D7) (T : Tor D) {N N' : ℕ} (Y : Set (Matrix (Fin N') (Fin N) D.host.E)) :
    AddSubgroup (VC D N N') :=
  AddSubgroup.closure {z | ∃ w ∈ T.abelian₂, ∃ A ∈ Y, z = w • embV D T A}

def Comm (D : D7) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : ℕ)
    (Y : Set (Matrix (Fin N') (Fin N) D.host.E)) : Prop :=
  (∀ y ∈ Y, ∃ a : Fin r → 𝓞 D.host.K, k • y = ∑ j, (a j : D.host.K) • b j) ∧
    ∀ j, k • b j ∈ AddSubgroup.closure Y

def Good (D : D7) (T : Tor D) : Prop :=
  ∃ e : D.what₂.Tau → D.host.E →+* ℂ, (∀ τ x, T.emb τ x = e τ x) ∧
    (∀ τ (a : D.host.K), e τ (a : D.host.E) = D.host.φ₀ (a : D.host.E)) ∧
    ∀ y : D.host.E, ∑ τ, e τ y = D.host.φ₀ ((Algebra.trace D.host.K D.host.E y : D.host.K) : D.host.E)

def aU (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (F : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun z => al D T x * U D T x F z

def RepInd (D : D7) (T : Tor D) {N N' : ℕ} (A₁ A₂ : AddSubgroup (VC D N N')) (F : VC D N N' → ℂ) : Prop :=
  ∀ x ∈ A₂, ∀ y ∈ A₂, x - y ∈ A₁ → aU D T x F = aU D T y F

def Tr (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) :
    Submodule Qbar (VC D N N' → ℂ) :=
  Submodule.span Qbar {F | ∃ t : VC D N N', (∃ m : ℕ, 0 < m ∧ m • t ∈ LaB D T b) ∧
    F = U D T t (pullB D T b (sgStar T.abelian₂))}

theorem La_eq (D : D7) (T : Tor D) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    La D T L L' = LaS D T (YYl D L L' : Set (Matrix (Fin N') (Fin N) D.host.E)) := rfl

theorem LaB_eq (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) :
    LaB D T b = LaS D T (Set.range b) := by
  unfold LaB LaS
  congr 1
  ext z
  constructor
  · rintro ⟨w, hw, j, rfl⟩; exact ⟨w, hw, b j, ⟨j, rfl⟩, rfl⟩
  · rintro ⟨w, hw, _, ⟨j, rfl⟩, rfl⟩; exact ⟨w, hw, j, rfl⟩

theorem comm_range (D : D7) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) :
    Comm D b 1 (Set.range b) := by
  refine ⟨?_, fun j => ?_⟩
  · rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  · rw [one_nsmul]; exact AddSubgroup.subset_closure ⟨j, rfl⟩

theorem Comm.mul {D : D7} {N N' r : ℕ} {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} {k : ℕ}
    {Y : Set (Matrix (Fin N') (Fin N) D.host.E)} (h : Comm D b k Y) (m : ℕ) : Comm D b (m * k) Y := by
  refine ⟨fun y hy => ?_, fun j => ?_⟩
  · obtain ⟨a, ha⟩ := h.1 y hy
    refine ⟨fun j => (m : 𝓞 D.host.K) * a j, ?_⟩
    rw [mul_nsmul', ha, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Nat.cast_smul_eq_nsmul D.host.K, smul_smul]
    simp
  · rw [mul_nsmul']; exact AddSubgroup.nsmul_mem _ (h.2 j) m

theorem emb_conj (D : D7) (e : D.host.E →+* ℂ) (x : D.host.E) :
    e (D.host.conj x) = (starRingEnd ℂ) (e x) := by
  exact D.host.conjE_apply e x

theorem cj_mem {M : IntermediateField ℚ ℂ} (ρ : M →ₐ[ℚ] ℂ) {x : ℂ} (h : x ∈ M) :
    cj M ρ x = ρ ⟨x, h⟩ := by
  simp [cj, TaylorLogMetric.liftM, h]

theorem cj_add {M : IntermediateField ℚ ℂ} (ρ : M →ₐ[ℚ] ℂ) {x y : ℂ} (hx : x ∈ M) (hy : y ∈ M) :
    cj M ρ (x + y) = cj M ρ x + cj M ρ y := by
  rw [cj_mem ρ hx, cj_mem ρ hy, cj_mem ρ (add_mem hx hy), ← map_add]; rfl

theorem cj_mul {M : IntermediateField ℚ ℂ} (ρ : M →ₐ[ℚ] ℂ) {x y : ℂ} (hx : x ∈ M) (hy : y ∈ M) :
    cj M ρ (x * y) = cj M ρ x * cj M ρ y := by
  rw [cj_mem ρ hx, cj_mem ρ hy, cj_mem ρ (mul_mem hx hy), ← map_mul]; rfl

theorem cj_zero {M : IntermediateField ℚ ℂ} (ρ : M →ₐ[ℚ] ℂ) : cj M ρ 0 = 0 := by
  rw [cj_mem ρ (zero_mem M)]; exact map_zero ρ

theorem cj_one {M : IntermediateField ℚ ℂ} (ρ : M →ₐ[ℚ] ℂ) : cj M ρ 1 = 1 := by
  rw [cj_mem ρ (one_mem M)]; exact map_one ρ

theorem cj_neg_one {M : IntermediateField ℚ ℂ} (ρ : M →ₐ[ℚ] ℂ) : cj M ρ (-1) = -1 := by
  rw [cj_mem ρ (neg_mem (one_mem M))]
  have : (⟨-1, neg_mem (one_mem M)⟩ : M) = -1 := rfl
  rw [this, map_neg, map_one]

theorem isTraceCompatibleTorusEmbedding_standardTorus (D : D7) (h : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Good D (tor0 D cc δ) :=
  ⟨fun τ => embT D τ, fun _ _ => rfl, h.1, h.2⟩

def cjEmb (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (h : ∀ τ x, embT D τ x ∈ M)
    (τ : D.what₂.Tau) : D.host.E →+* ℂ :=
  (ρ : M →+* ℂ).comp ((embT D τ).codRestrict M.toSubfield (h τ))

theorem cjEmb_apply (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (h : ∀ τ x, embT D τ x ∈ M)
    (τ : D.what₂.Tau) (x : D.host.E) : cjEmb D M ρ h τ x = cj M ρ (embT D τ x) := by
  rw [cj_mem ρ (h τ x)]; rfl

theorem good_torConj (D : D7) (h : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hK : FixK D M ρ) (hD : DataIn D (tor0 D cc δ) M) :
    Good D (torConj D (tor0 D cc δ) M ρ) := by
  have hM : ∀ τ x, embT D τ x ∈ M := hD.1
  refine ⟨cjEmb D M ρ hM, fun τ x => (cjEmb_apply D M ρ hM τ x).symm, fun τ a => ?_, fun y => ?_⟩
  · rw [cjEmb_apply, h.1 τ a]; exact (hK a).2
  · rw [← (hK _).2, ← h.2 y, cj_mem ρ (sum_mem fun τ _ => hM τ y)]
    have : (⟨∑ τ, embT D τ y, sum_mem fun τ _ => hM τ y⟩ : M) = ∑ τ, ⟨embT D τ y, hM τ y⟩ := by
      apply Subtype.ext; simp
    rw [this, map_sum]
    rfl

theorem Good.embV_add {D : D7} {T : Tor D} (h : Good D T) {N N' : ℕ}
    (A B : Matrix (Fin N') (Fin N) D.host.E) : embV D T (A + B) = embV D T A + embV D T B := by
  obtain ⟨e, he, -, -⟩ := h
  funext τ i j
  simp [embV, he]

theorem Good.embV_smul {D : D7} {T : Tor D} (h : Good D T) {N N' : ℕ} (a : D.host.K)
    (A : Matrix (Fin N') (Fin N) D.host.E) :
    embV D T (a • A) = D.host.φ₀ (a : D.host.E) • embV D T A := by
  obtain ⟨e, he, hK, -⟩ := h
  funext τ i j
  have : (a • A) i j = (a : D.host.E) * A i j := rfl
  simp only [embV, he, this, map_mul, hK, Pi.smul_apply, smul_eq_mul]

def Good.embHom {D : D7} {T : Tor D} (h : Good D T) (N N' : ℕ) :
    Matrix (Fin N') (Fin N) D.host.E →+ VC D N N' :=
  AddMonoidHom.mk' (embV D T) h.embV_add

theorem Good.coordB_embV {D : D7} {T : Tor D} (h : Good D T) {N N' r : ℕ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : TaylorLogMetric.Orthonormal D b) (i j : Fin r) :
    coordB D T b j (embV D T (b i)) = if i = j then 1 else 0 := by
  obtain ⟨e, he, hK, hT⟩ := h
  have h1 := hT (∑ a, ∑ c, b i a c * D.host.conj (b j a c))
  have h2 := hb i j
  unfold hYY at h2
  rw [h2] at h1
  have h3 : coordB D T b j (embV D T (b i)) = ∑ τ, e τ (∑ a, ∑ c, b i a c * D.host.conj (b j a c)) := by
    simp only [coordB, embV, he, map_sum, map_mul, emb_conj]
  rw [h3, h1]
  split_ifs <;> simp

theorem coordB_add (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (j : Fin r) (x y : VC D N N') : coordB D T b j (x + y) = coordB D T b j x + coordB D T b j y := by
  simp [coordB, add_mul, Finset.sum_add_distrib]

theorem coordB_smul (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (j : Fin r) (c : ℂ) (x : VC D N N') : coordB D T b j (c • x) = c * coordB D T b j x := by
  simp [coordB, Finset.mul_sum, mul_assoc]

def coordL (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (j : Fin r) : VC D N N' →ₗ[ℂ] ℂ where
  toFun := coordB D T b j
  map_add' := coordB_add D T b j
  map_smul' := coordB_smul D T b j

theorem Good.coordB_sum {D : D7} {T : Tor D} (h : Good D T) {N N' r : ℕ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : TaylorLogMetric.Orthonormal D b) (c : Fin r → ℂ) (j : Fin r) :
    coordB D T b j (∑ i, c i • embV D T (b i)) = c j := by
  change coordL D T b j _ = _
  rw [map_sum]
  have : ∀ i, coordL D T b j (c i • embV D T (b i)) = if i = j then c i else 0 := fun i => by
    change coordB D T b j _ = _
    rw [coordB_smul, h.coordB_embV hb]; simp
  simp [this]

theorem Hf_add_left (D : D7) (T : Tor D) {N N' : ℕ} (x y w : VC D N N') :
    Hf D T (x + y) w = Hf D T x w + Hf D T y w := by
  simp [Hf, add_mul, Finset.sum_add_distrib, add_div]

theorem Hf_add_right (D : D7) (T : Tor D) {N N' : ℕ} (x y w : VC D N N') :
    Hf D T w (x + y) = Hf D T w x + Hf D T w y := by
  simp [Hf, mul_add, Finset.sum_add_distrib, add_div]

theorem Hf_smul_left (D : D7) (T : Tor D) {N N' : ℕ} (c : ℂ) (x w : VC D N N') :
    Hf D T (c • x) w = c * Hf D T x w := by
  simp [Hf, Finset.mul_sum, mul_assoc, mul_div_assoc, Finset.sum_div]

theorem Hf_conj (D : D7) (T : Tor D) {N N' : ℕ} (x w : VC D N N') :
    Hf D T w x = (starRingEnd ℂ) (Hf D T x w) := by
  simp [Hf, mul_comm]

theorem U_U (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') (F : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (U D T y F) z = ee (-(Hf D T x y).im / 2) * U D T (x + y) F z := by
  unfold U ee
  rw [add_assoc z x y, mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  rw [Hf_add_left, Hf_add_right, Hf_add_left, Hf_add_right, Hf_add_right, Hf_conj D T x y]
  have := Complex.sub_conj (Hf D T x y)
  push_cast at this ⊢
  linear_combination (-(Real.pi : ℂ) / 2) * this

theorem U_zero (D : D7) (T : Tor D) {N N' : ℕ} (F : VC D N N' → ℂ) : U D T 0 F = F := by
  funext z; simp [U, Hf]

theorem differentiable_U (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') {F : VC D N N' → ℂ}
    (hF : Differentiable ℂ F) : Differentiable ℂ (U D T x F) := by
  unfold U Hf
  fun_prop

theorem taylor_add (D : D7) {N N' : ℕ} {F G : VC D N N' → ℂ} (hF : Differentiable ℂ F)
    (hG : Differentiable ℂ G) (α : Mono D N N') :
    taylor D (F + G) α = taylor D F α + taylor D G α := by
  have aF : ContDiffAt ℂ (Multiset.card α.toMultiset) F 0 :=
    (SCV.analyticOnNhd_of_differentiable hF Set.univ 0 (Set.mem_univ _)).contDiffAt
  have aG : ContDiffAt ℂ (Multiset.card α.toMultiset) G 0 :=
    (SCV.analyticOnNhd_of_differentiable hG Set.univ 0 (Set.mem_univ _)).contDiffAt
  unfold taylor
  rw [iteratedFDeriv_add_apply aF aG]
  simp [add_div]

theorem taylor_mul (D : D7) {N N' : ℕ} (c : ℂ) {F : VC D N N' → ℂ} (hF : Differentiable ℂ F)
    (α : Mono D N N') : taylor D (fun z => c * F z) α = c * taylor D F α := by
  have aF : ContDiffAt ℂ (Multiset.card α.toMultiset) F 0 :=
    (SCV.analyticOnNhd_of_differentiable hF Set.univ 0 (Set.mem_univ _)).contDiffAt
  unfold taylor
  have : (fun z => c * F z) = c • F := rfl
  rw [this, iteratedFDeriv_const_smul_apply aF]
  simp [mul_div_assoc]

theorem taylor_zero (D : D7) {N N' : ℕ} (α : Mono D N N') : taylor D (0 : VC D N N' → ℂ) α = 0 := by
  have := taylor_mul D 0 (F := (0 : VC D N N' → ℂ)) (differentiable_const 0) α
  simp only [zero_mul] at this
  exact this

theorem CjF.zero (D : D7) {N N' : ℕ} (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) :
    CjF D M ρ (0 : VC D N N' → ℂ) 0 :=
  ⟨differentiable_const 0, differentiable_const 0, fun α => by
    rw [taylor_zero, cj_zero]; exact ⟨zero_mem _, rfl⟩⟩

theorem CjF.add {D : D7} {N N' : ℕ} {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}
    {F F' G G' : VC D N N' → ℂ} (h : CjF D M ρ F F') (h' : CjF D M ρ G G') :
    CjF D M ρ (F + G) (F' + G') :=
  ⟨h.1.add h'.1, h.2.1.add h'.2.1, fun α => by
    rw [taylor_add D h.1 h'.1, taylor_add D h.2.1 h'.2.1, cj_add ρ (h.2.2 α).1 (h'.2.2 α).1,
      (h.2.2 α).2, (h'.2.2 α).2]
    exact ⟨add_mem (h.2.2 α).1 (h'.2.2 α).1, rfl⟩⟩

theorem CjF.mul {D : D7} {N N' : ℕ} {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}
    {F F' : VC D N N' → ℂ} (h : CjF D M ρ F F') {c : ℂ} (hc : c ∈ M) :
    CjF D M ρ (fun z => c * F z) (fun z => cj M ρ c * F' z) :=
  ⟨h.1.const_mul c, h.2.1.const_mul _, fun α => by
    rw [taylor_mul D _ h.1, taylor_mul D _ h.2.1, cj_mul ρ hc (h.2.2 α).1, (h.2.2 α).2]
    exact ⟨mul_mem hc (h.2.2 α).1, rfl⟩⟩

theorem CjF.sum {D : D7} {N N' : ℕ} {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {ι : Type*}
    (s : Finset ι) {F F' : ι → VC D N N' → ℂ} (h : ∀ i ∈ s, CjF D M ρ (F i) (F' i)) :
    CjF D M ρ (fun z => ∑ i ∈ s, F i z) (fun z => ∑ i ∈ s, F' i z) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact CjF.zero D M ρ
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end GlobalTheory.ThetaConj

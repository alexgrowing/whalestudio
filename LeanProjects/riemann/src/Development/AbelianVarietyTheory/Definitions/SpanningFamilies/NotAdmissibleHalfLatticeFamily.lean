import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible

open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)

namespace GlobalTheory.SW.Model

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cc_cc (x : E) : cc (cc x) = x := by simp [cc]

theorem cc_integral {x : E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (cc x) :=
  hx.map ((IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom)

omit [IsCMField E] in
theorem mem_stdL {m : ℕ} (x : Fin m → E) : x ∈ stdL E m ↔ ∀ a, IsIntegral ℤ (x a) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      intro a
      by_cases h : a = b
      · subst h; simpa using isIntegral_one
      · simpa [Pi.single_apply, h] using isIntegral_zero
    | zero => intro a; exact isIntegral_zero
    | add x y _ _ hx hy => intro a; exact (hx a).add (hy a)
    | smul c x _ hx =>
      intro a
      have : (c • x) a = (c : E) * x a := rfl
      rw [this]; exact c.isIntegral_coe.mul (hx a)
  · intro hx
    have : x = ∑ a, (⟨x a, hx a⟩ : 𝓞 E) • (Pi.single a 1 : Fin m → E) := by
      ext b
      rw [Finset.sum_apply, Finset.sum_eq_single b]
      · change x b = x b * (Pi.single b (1 : E) : Fin m → E) b
        simp
      · intro a _ h
        change x a * (Pi.single a (1 : E) : Fin m → E) b = 0
        simp [Pi.single_apply, Ne.symm h]
      · simp
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem herm_one {m : ℕ} (x y : Fin m → E) : herm 1 x y = ∑ a, x a * cc (y a) := by
  unfold herm
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a] <;> simp +contextual [Matrix.one_apply, eq_comm]

theorem stdL_mem_Vset (n M : ℕ) : stdL E n ∈ Vset E n M := by
  refine ⟨Submodule.fg_span (Set.finite_range _), fun x => ⟨fun hx y hy => ?_, fun h => ?_⟩,
    1, one_pos, Nat.coprime_one_left M, by simp, by simp⟩
  · rw [herm_one]
    rw [mem_stdL] at hx hy
    exact IsIntegral.sum _ fun a _ => (hx a).mul (cc_integral (hy a))
  · rw [mem_stdL]
    intro a
    have := h (Pi.single a 1) (Submodule.subset_span ⟨a, rfl⟩)
    rw [herm_one, Finset.sum_eq_single a] at this
    · simpa [cc] using this
    · intro b _ hb; simp [Pi.single_apply, hb, cc]
    · simp

theorem one_mem_DH (n M : ℕ) : (1 : Matrix (Fin n) (Fin n) E) ∈ DH E n M := by
  refine ⟨?_, 1, one_pos, Nat.coprime_one_left M, 0, fun _ _ => isIntegral_zero, by simp⟩
  have : ccT (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    ext i j; by_cases h : i = j <;> simp [ccT, cc, Matrix.one_apply, h, eq_comm]
  rw [this, one_mul]

omit [IsCMField E] in
theorem nat_smul_mem {m : ℕ} (Λ : Lt E m) (s : ℕ) {v : Fin m → E} (hv : v ∈ Λ) :
    (s : E) • v ∈ Λ := by
  rw [Nat.cast_smul_eq_nsmul]; exact Λ.toAddSubgroup.nsmul_mem hv s

omit [IsCMField E] in
theorem mem_of_coprime {m : ℕ} (Λ : Lt E m) {s R : ℕ} (h : s.Coprime R) {v : Fin m → E}
    (h1 : (s : E) • v ∈ Λ) (h2 : (R : E) • v ∈ Λ) : v ∈ Λ := by
  have hc : IsCoprime (s : ℤ) (R : ℤ) := Nat.isCoprime_iff_coprime.2 h
  obtain ⟨a, b, hab⟩ := hc
  have e : v = a • ((s : E) • v) + b • ((R : E) • v) := by
    rw [← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul, smul_smul, ← add_smul]
    have : (a : E) * s + b * R = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → E) hab
    rw [this, one_smul]
  rw [e]
  exact Λ.add_mem (Λ.toAddSubgroup.zsmul_mem h1 a) (Λ.toAddSubgroup.zsmul_mem h2 b)

open Classical in

def indFam (E : Type) [Field E] [NumberField E] (n N : ℕ) : Fam E n N := fun Λ x =>
  if ColsIn Λ x then 1 else 0

theorem admissible_indicator_functions {n N M R : ℕ} (hM : 0 < M) (hR : 0 < R) : admitted M R (indFam E n N) := by
  refine ⟨⟨hM, hR⟩, ?_, ?_, ?_, ?_⟩
  · intro h _ Λ _ Λ' _ hm x
    have : ColsIn Λ' (h * x) ↔ ColsIn Λ x := by
      refine forall_congr' fun a => ?_
      rw [hm]
      rfl
    classical exact if_congr this rfl rfl
  · intro Λ _ x hx a
    have : ColsIn Λ x := by
      by_contra h; exact hx (if_neg h)
    exact nat_smul_mem Λ R (this a)
  · intro Λ _ x y hy
    have : ColsIn Λ (x + (R : E) • y) ↔ ColsIn Λ x := by
      refine forall_congr' fun a => ?_
      exact Λ.add_mem_iff_left (nat_smul_mem Λ R (hy a))
    classical exact if_congr this rfl rfl
  · rintro Λ _ Λ' _ ⟨s, _, hs, h1, h2⟩ x hx hx'
    have hsR : s.Coprime R := Nat.Coprime.coprime_mul_right_right hs
    have : ColsIn Λ x ↔ ColsIn Λ' x :=
      forall_congr' fun a => ⟨fun h => mem_of_coprime Λ' hsR (h1 _ h) (hx' a),
        fun h => mem_of_coprime Λ hsR (h2 _ h) (hx a)⟩
    classical exact if_congr this rfl rfl

theorem indFam_ne_zero (n N M : ℕ) : ∃ Λ ∈ Vset E n M, indFam E n N Λ 0 = 1 :=
  ⟨stdL E n, stdL_mem_Vset n M, if_pos fun _ => (stdL E n).zero_mem⟩

theorem I_mem_Hn (Ψ : Finset (E →+* ℂ)) (N : ℕ) :
    (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ) : CM Ψ N N) ∈ Hn Ψ N := by
  intro τ
  have : imH (I • (1 : Matrix (Fin N) (Fin N) ℂ)) = 1 := by
    unfold imH
    rw [conjTranspose_smul, conjTranspose_one, ← sub_smul, smul_smul]
    have : (2 * I)⁻¹ * (I - star I) = 1 := by
      have : star I = -I := conj_I
      rw [this]; field_simp; ring
    rw [this, one_smul]
  simpa [this] using Matrix.PosDef.one

theorem ccT_J (N : ℕ) : ccT (Matrix.J (Fin N) E) = -Matrix.J (Fin N) E := by
  have : (Matrix.J (Fin N) E).map cc = Matrix.J (Fin N) E := by
    ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [Matrix.J, cc, Matrix.one_apply, h]
  rw [ccT, this, Matrix.J_transpose]

theorem J_mem_UU (N : ℕ) : Matrix.J (Fin N) E ∈ UU E N := by
  change ccT _ * _ * _ = _
  rw [ccT_J, neg_mul, Matrix.J_squared]; simp

theorem one_mem_UU (N : ℕ) : (1 : M2 E N) ∈ UU E N := by
  change ccT _ * _ * _ = _
  have : ccT (1 : M2 E N) = 1 := by
    ext i j; by_cases h : i = j <;> simp [ccT, cc, Matrix.one_apply, h, eq_comm]
  rw [this]; simp

theorem transH_one (Ψ : Finset (E →+* ℂ)) {n N : ℕ} (φ : Matrix (Fin n) (Fin N) E → ℂ) :
    TransH Ψ (1 : M2 E N) φ φ := by
  intro Z _ z z'
  have h11 : (1 : M2 E N).toBlocks₁₁ = 1 := by rw [← Matrix.fromBlocks_one]; rfl
  have h12 : (1 : M2 E N).toBlocks₁₂ = 0 := by rw [← Matrix.fromBlocks_one]; rfl
  have h21 : (1 : M2 E N).toBlocks₂₁ = 0 := by rw [← Matrix.fromBlocks_one]; rfl
  have h22 : (1 : M2 E N).toBlocks₂₂ = 1 := by rw [← Matrix.fromBlocks_one]; rfl
  have d1 : ∀ τ, hDen Ψ (1 : M2 E N) Z τ = 1 := fun τ => by simp [hDen, h21, h22]
  have d2 : ∀ τ, hDen' Ψ (1 : M2 E N) Z τ = 1 := fun τ => by simp [hDen', h21, h22]
  have a : hAct Ψ (1 : M2 E N) Z = Z := by funext τ; simp [hAct, d1, h11, h12]
  have f : hFac Ψ (1 : M2 E N) Z z z' = 1 := by simp [hFac, d1, h21]
  rw [a, f, one_mul]
  congr 1
  · funext τ; ext k i; simp [d2]
  · funext τ; ext k i; simp [d1]

theorem transH_translation (Ψ : Finset (E →+* ℂ)) {n N : ℕ} (β : Matrix (Fin N) (Fin N) E)
    (ψ : Matrix (Fin n) (Fin N) E → ℂ) :
    TransH Ψ (Matrix.fromBlocks 1 β 0 1) (fun x => ψ x * chiH Ψ β x) ψ := by
  intro Z _ z z'
  have d1 : ∀ τ, hDen Ψ (Matrix.fromBlocks 1 β 0 1) Z τ = 1 := fun τ => by simp [hDen]
  have d2 : ∀ τ, hDen' Ψ (Matrix.fromBlocks 1 β 0 1) Z τ = 1 := fun τ => by simp [hDen']
  have a : hAct Ψ (Matrix.fromBlocks 1 β 0 1) Z = fun τ => Z τ + β.map τ.1 := by
    funext τ; simp [hAct, d1]
  have f : hFac Ψ (Matrix.fromBlocks 1 β 0 1) Z z z' = 1 := by simp [hFac, d1]
  have e1 : (fun τ => Matrix.of fun k => (hDen' Ψ (Matrix.fromBlocks 1 β 0 1) Z τ)⁻¹ *ᵥ z τ k) = z := by
    funext τ; ext k i; simp [d2]
  have e2 : (fun τ => Matrix.of fun k => z' τ k ᵥ* (hDen Ψ (Matrix.fromBlocks 1 β 0 1) Z τ)⁻¹) = z' := by
    funext τ; ext k i; simp [d1]
  rw [a, f, one_mul, e1, e2]
  unfold thH
  congr 1
  funext x
  rw [mul_assoc (ψ x), chiH, ← Complex.exp_add, ← mul_add]
  congr 3
  unfold expo
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hc : ∀ t : E, τ.1 (cc t) = conj (τ.1 t) := fun t => by
    simp [cc, IsCMField.complexEmbedding_complexConj]
  rw [Matrix.trace, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : τ.1 ((x * β * ccT x).diag k) =
      (fun a => τ.1 (x k a)) ⬝ᵥ β.map τ.1 *ᵥ (fun a => conj (τ.1 (x k a))) := by
    simp only [Matrix.diag, Matrix.mul_apply, ccT, Matrix.transpose_apply, Matrix.map_apply,
      map_sum, map_mul, hc, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [this, Matrix.add_mulVec, dotProduct_add]
  ring

omit [IsCMField E] in

theorem expo_ofQ (Ψ : Finset (E →+* ℂ)) {n N : ℕ} (m : Matrix (Fin n) (QI E N) ℚ) (Z : CM Ψ N N)
    (z z' : CM Ψ n N) :
    ∑ k, (qv (m k) ⬝ᵥ tauOf Ψ Z *ᵥ qv (m k) + 2 * (qv (m k) ⬝ᵥ zetaOf Ψ z z' k)) =
      2 * expo Ψ (ofQ m) Z z z' := by
  unfold expo
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  set e : Ψ → Fin (Module.finrank ℚ E) → ℂ := fun τ j => τ.1 (Module.finBasis ℚ E j) with he
  have hx : ∀ (τ : Ψ) a, τ.1 (ofQ m k a) = ∑ j, (m k (a, j) : ℂ) * e τ j := fun τ a => by
    simp [ofQ, he, Rat.smul_def]
  have hq : ∀ τ : Ψ, (fun a => τ.1 (ofQ m k a)) ⬝ᵥ Z τ *ᵥ (fun a => conj (τ.1 (ofQ m k a))) =
      ∑ p : QI E N, ∑ q : QI E N, (m k p : ℂ) * (e τ p.2 * Z τ p.1 q.1 * conj (e τ q.2) * m k q) := by
    intro τ
    simp only [hx, dotProduct, Matrix.mulVec, Fintype.sum_prod_type, map_sum, map_mul,
      Finset.sum_mul, Finset.mul_sum, map_ratCast]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Eq.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm) ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have hl : ∀ τ : Ψ, (fun a => τ.1 (ofQ m k a)) ⬝ᵥ z τ k + z' τ k ⬝ᵥ (fun a => conj (τ.1 (ofQ m k a))) =
      ∑ p : QI E N, (m k p : ℂ) * (e τ p.2 * z τ k p.1 + z' τ k p.1 * conj (e τ p.2)) := by
    intro τ
    simp only [hx, dotProduct, Fintype.sum_prod_type, map_sum, map_mul,
      Finset.sum_mul, Finset.mul_sum, map_ratCast, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [add_assoc, hq, hl]
  have h1 : qv (m k) ⬝ᵥ tauOf Ψ Z *ᵥ qv (m k) = 2 * ∑ τ : Ψ, ∑ p : QI E N, ∑ q : QI E N,
      (m k p : ℂ) * (e τ p.2 * Z τ p.1 q.1 * conj (e τ q.2) * m k q) := by
    have s1 : ∑ τ : Ψ, ∑ p : QI E N, ∑ q : QI E N,
        (m k p : ℂ) * (e τ p.2 * Z τ p.1 q.1 * conj (e τ q.2) * m k q) =
        ∑ p : QI E N, ∑ q : QI E N, ∑ τ : Ψ,
        (m k p : ℂ) * (e τ p.2 * Z τ p.1 q.1 * conj (e τ q.2) * m k q) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    have s2 : ∑ p : QI E N, ∑ q : QI E N, ∑ τ : Ψ,
        (m k p : ℂ) * (e τ p.2 * Z τ p.1 q.1 * conj (e τ q.2) * m k q) =
        ∑ p : QI E N, ∑ q : QI E N, ∑ τ : Ψ,
        (m k p : ℂ) * (e τ q.2 * Z τ q.1 p.1 * conj (e τ p.2) * m k q) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring
    rw [two_mul, s1]
    nth_rewrite 2 [s2]
    simp only [dotProduct, Matrix.mulVec, tauOf, qv, Matrix.of_apply, Finset.sum_mul,
      Finset.mul_sum, add_mul, mul_add, Finset.sum_add_distrib, he]
  have h2 : qv (m k) ⬝ᵥ zetaOf Ψ z z' k = ∑ τ : Ψ, ∑ p : QI E N,
      (m k p : ℂ) * (e τ p.2 * z τ k p.1 + z' τ k p.1 * conj (e τ p.2)) := by
    simp only [dotProduct, zetaOf, qv, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [h1, h2, Finset.sum_add_distrib]
  ring

theorem transH_levi (Ψ : Finset (E →+* ℂ)) {n N : ℕ} {A D : Matrix (Fin N) (Fin N) E}
    (h : ccT D * A = 1) (φ : Matrix (Fin n) (Fin N) E → ℂ) :
    TransH Ψ (Matrix.fromBlocks A 0 0 D) φ
      (fun x => (∏ τ : Ψ, τ.1 D.det ^ n) * φ (x * A)) := by
  intro Z _ z z'
  have h' : A * ccT D = 1 := mul_eq_one_comm.1 h
  have e : ∀ τ : Ψ, (D.map τ.1)ᴴ * A.map τ.1 = 1 := fun τ => by
    rw [← Base.ccT_map, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have e' : ∀ τ : Ψ, (A.map τ.1)ᴴ * D.map τ.1 = 1 := fun τ => by
    simpa using congrArg Matrix.conjTranspose (e τ)
  have d1 : ∀ τ, hDen Ψ (Matrix.fromBlocks A 0 0 D) Z τ = D.map τ.1 := fun τ => by simp [hDen]
  have d2 : ∀ τ, hDen' Ψ (Matrix.fromBlocks A 0 0 D) Z τ = (D.map τ.1)ᴴ := fun τ => by
    simp [hDen']
  have i1 : ∀ τ : Ψ, (D.map τ.1)⁻¹ = (A.map τ.1)ᴴ := fun τ => Matrix.inv_eq_left_inv (e' τ)
  have i2 : ∀ τ : Ψ, ((D.map τ.1)ᴴ)⁻¹ = A.map τ.1 := fun τ => Matrix.inv_eq_right_inv (e τ)
  have a : hAct Ψ (Matrix.fromBlocks A 0 0 D) Z = fun τ => A.map τ.1 * Z τ * (A.map τ.1)ᴴ := by
    funext τ; simp [hAct, d1, i1]
  have f : hFac Ψ (Matrix.fromBlocks A 0 0 D) Z z z' = ∏ τ : Ψ, τ.1 D.det ^ n := by
    unfold hFac
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [d1, RingHom.map_det]
    simp
  have e1 : (fun τ => Matrix.of fun k => (hDen' Ψ (Matrix.fromBlocks A 0 0 D) Z τ)⁻¹ *ᵥ z τ k) =
      fun τ => z τ * (A.map τ.1)ᵀ := by
    funext τ; ext k i; simp [d2, i2, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  have e2 : (fun τ => Matrix.of fun k => z' τ k ᵥ* (hDen Ψ (Matrix.fromBlocks A 0 0 D) Z τ)⁻¹) =
      fun τ => z' τ * (A.map τ.1)ᴴ := by
    funext τ; ext k i; rw [d1, i1]; rfl
  rw [a, f, e1, e2]
  let σ : Matrix (Fin n) (Fin N) E ≃ Matrix (Fin n) (Fin N) E :=
    ⟨fun x => x * A, fun x => x * ccT D,
      fun x => by simp only [Matrix.mul_assoc, h', Matrix.mul_one],
      fun x => by simp only [Matrix.mul_assoc, h, Matrix.mul_one]⟩
  unfold thH
  rw [← σ.tsum_eq (fun x => φ x * cexp (2 * Real.pi * I * expo Ψ x Z z z')), ← tsum_mul_left]
  refine tsum_congr fun x => ?_
  change _ = _ * (φ (x * A) * cexp (_ * expo Ψ (x * A) Z z z'))
  rw [mul_assoc]
  congr 4
  rw [Base.expo_eq_trace, Base.expo_eq_trace]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Matrix.map_mul, Matrix.conjTranspose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]

theorem lag_nontrivial (N : ℕ) : Nontrivial (Lag E (N + 1)) := by
  refine ⟨⟨⟨_, 1, Base.one_mem_UU, rfl⟩, ⟨_, _, Base.J_mem_UU, rfl⟩, fun h => ?_⟩⟩
  have h1 : botSpan (1 : M2 E (N + 1)) = botSpan (Matrix.J (Fin (N + 1)) E) := congrArg Subtype.val h
  have h2 : (Matrix.J (Fin (N + 1)) E) (Sum.inr 0) ∈ botSpan (1 : M2 E (N + 1)) := by
    rw [h1]; exact Submodule.subset_span ⟨0, rfl⟩
  have h3 : botSpan (1 : M2 E (N + 1)) ≤ LinearMap.ker (LinearMap.proj (Sum.inl 0)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    simp [Matrix.one_apply]
  simpa [Matrix.J] using h3 h2

open Classical in

def divFam (E : Type) [Field E] [NumberField E] (n N R : ℕ) : Fam E n N := fun Λ x =>
  if ColsIn Λ ((R : E) • x) then 1 else 0

theorem admissible_scaled_lattice_family {n N M R : ℕ} (hM : 0 < M) (hR : 0 < R) : admitted M R (divFam E n N R) := by
  classical
  refine ⟨⟨hM, hR⟩, ?_, ?_, ?_, ?_⟩
  · intro h _ Λ _ Λ' _ hm x
    have : ColsIn Λ' ((R : E) • (h * x)) ↔ ColsIn Λ ((R : E) • x) := by
      refine forall_congr' fun a => ?_
      rw [hm, ← Matrix.mul_smul]
      rfl
    exact if_congr this rfl rfl
  · intro Λ _ x hx
    by_contra h; exact hx (if_neg h)
  · intro Λ _ x y hy
    have : ColsIn Λ ((R : E) • (x + (R : E) • y)) ↔ ColsIn Λ ((R : E) • x) := by
      rw [smul_add]
      refine forall_congr' fun a => ?_
      exact Λ.add_mem_iff_left (nat_smul_mem Λ R (nat_smul_mem Λ R (hy a)))
    exact if_congr this rfl rfl
  · intro Λ _ Λ' _ _ x hx hx'
    exact (if_pos hx).trans (if_pos hx').symm

theorem not_admissible_half_lattice_family {n N M : ℕ} : ¬ admitted M 1 (divFam E (n + 1) (N + 1) 2) := by
  classical
  intro h
  have h1 := h.supp _ (stdL_mem_Vset (n + 1) M) (Matrix.of fun _ _ => (2⁻¹ : E)) (by
    have : ColsIn (stdL E (n + 1)) (((2 : ℕ) : E) •
        (Matrix.of fun _ _ => (2⁻¹ : E) : Matrix (Fin (n + 1)) (Fin (N + 1)) E)) := fun a =>
      (mem_stdL _).2 fun k => by simpa using isIntegral_one
    simp only [divFam, if_pos this]; exact one_ne_zero)
  have h2 : IsIntegral ℤ (2⁻¹ : E) := by simpa using (mem_stdL _).1 (h1 0) 0
  have h3 : IsIntegral ℤ (2⁻¹ : ℚ) := by
    rw [← isIntegral_algebraMap_iff (B := E) (algebraMap ℚ E).injective]; simpa using h2
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  have : (2 : ℚ) * k = 1 := by
    have : (k : ℚ) = 2⁻¹ := by simpa using hk
    rw [this]; norm_num
  have : (2 : ℤ) * k = 1 := by exact_mod_cast this
  omega

theorem exists_isType : ∃ Ψ : Finset (E →+* ℂ), IsType Ψ ∧ Ψ.Nonempty := by
  classical
  let Ψ : Finset (E →+* ℂ) := Finset.univ.filter fun τ => (InfinitePlace.mk τ).embedding = τ
  have hT : IsType Ψ := by
    intro τ
    have hne : ComplexEmbedding.conjugate τ ≠ τ := IsTotallyComplex.complexEmbedding_not_isReal τ
    simp only [Ψ, Finset.mem_filter, Finset.mem_univ, true_and, InfinitePlace.mk_conjugate_eq]
    rcases InfinitePlace.mk_eq_iff.1 (InfinitePlace.mk_embedding (InfinitePlace.mk τ)) with h | h
    · rw [h]; simp [hne.symm]
    · have h2 : (InfinitePlace.mk τ).embedding = ComplexEmbedding.conjugate τ := by
        rw [← h]; ext x; simp
      rw [h2]; simp [hne]
  refine ⟨Ψ, hT, ?_⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ Ψ
  · exact ⟨τ, h⟩
  · exact ⟨_, by simpa [h] using (hT τ).not⟩

theorem wt_rank_zero (M : ℕ) (Λ : Lt E 0) : wt M Λ = 1 := by
  have : {h ∈ DH E 0 M | Moves h Λ Λ} = {1} := by
    ext h
    obtain rfl : h = 1 := Subsingleton.elim _ _
    simp [one_mem_DH, Base.moves_one]
  simp [wt, this]

theorem neg_one_mem_DH (n : ℕ) : (-1 : Matrix (Fin n) (Fin n) E) ∈ DH E n 2 := by
  refine ⟨?_, 1, one_pos, by norm_num, -1, fun i j => ?_, ?_⟩
  · have : ccT (-1 : Matrix (Fin n) (Fin n) E) = -1 := by
      ext i j; by_cases h : i = j <;> simp [ccT, cc, Matrix.one_apply, h, eq_comm]
    rw [this]; simp
  · by_cases h : i = j <;> simp [Matrix.one_apply, h, isIntegral_zero, isIntegral_one.neg]
  · ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]; norm_num

omit [IsCMField E] in

theorem twist_indFam_zero {n N R : ℕ} (Λ : Lt E n) :
    twist R (stdL E N) (indFam E n N) Λ 0 = 1 := by
  have h : (∀ ξ ∈ stdL E N, (R : E) • ((0 : Matrix (Fin n) (Fin N) E) *ᵥ ξ) ∈ Λ) ∧
      ∃ s : ℕ, s ≡ 1 [MOD R ^ 2] ∧ ∀ v ∈ stdL E N, (s : E) • v ∈ stdL E N :=
    ⟨fun _ _ => by simp, 1, Nat.ModEq.refl 1, by simp⟩
  unfold twist
  rw [dif_pos h, smul_zero]
  exact if_pos fun _ => Λ.zero_mem

theorem exists_concrete : ∃ (_ : IsCMField (CyclotomicField 3 ℚ))
    (Ψ : Finset (CyclotomicField 3 ℚ →+* ℂ)), IsType Ψ ∧ Ψ.Nonempty := by
  have : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  have : IsCMField (CyclotomicField 3 ℚ) :=
    IsCyclotomicExtension.Rat.isCMField (S := {3}) _ ⟨3, rfl, by norm_num⟩
  exact ⟨this, exists_isType⟩

end

end GlobalTheory.SW.Model

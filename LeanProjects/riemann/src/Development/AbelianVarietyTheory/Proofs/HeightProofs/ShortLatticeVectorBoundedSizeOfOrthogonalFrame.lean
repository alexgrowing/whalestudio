import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsIntMulIsIntegralOfTrace

open GlobalTheory.SmoothForms GlobalTheory.HermClass Module Submodule NumberField Matrix

namespace GlobalTheory.SmoothForms.Short

theorem one_le_norm_mul_pow {E : Type} [Field E] [NumberField E] {a : E} (ha : IsIntegral ℤ a) (h0 : a ≠ 0)
    {T : ℝ} (hT : 1 ≤ T) (haT : house a ≤ T) (ψ : E →+* ℂ) : 1 ≤ ‖ψ a‖ * T ^ finrank ℚ E := by
  classical
  have h1 : (1 : ℝ) ≤ ∏ φ : E →+* ℂ, ‖φ a‖ := by
    have h := Algebra.norm_eq_prod_embeddings ℚ ℂ a
    rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ a) _ (fun _ => rfl)] at h
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm ℚ ha)
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact (Algebra.norm_ne_zero_iff (R := ℚ)).2 h0 (by rw [← hm, map_zero])
    rw [← norm_prod, ← h, ← hm]
    simp only [algebraMap_int_eq, eq_intCast, eq_ratCast, Rat.cast_intCast, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hm0
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ψ)] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  refine (Finset.prod_le_prod (g := fun _ => T) (fun _ _ => norm_nonneg _)
    fun φ _ => (norm_le_pi_norm (canonicalEmbedding E a) φ).trans haT).trans ?_
  rw [Finset.prod_const, ← Embeddings.card E ℂ]
  exact pow_le_pow_right₀ hT (Finset.card_le_univ _)

theorem exists_short_coord {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {V : Type} [AddCommGroup V] [Module F V] {ι : Type} [Fintype ι] (e : Basis ι F V)
    (q : LinearMap.BilinForm F V) (he : ∀ k l, l ≠ k → q (e l) (e k) = 0) {κ : Type} [Fintype κ] [DecidableEq κ]
    (b : κ → V) (hκ : Fintype.card κ = finrank ℚ F * Fintype.card ι) {t : ℝ} (ht : 0 < t)
    (h0 : (Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j))).det ≠ 0)
    (h1 : |(((Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j))).det : ℚ) : ℝ)| <
      (t ^ Fintype.card κ) ^ 2) :
    ∃ z : κ → ℤ, z ≠ 0 ∧ ∀ φ : F →+* ℂ,
      ‖φ (q (∑ i, z i • b i) (∑ i, z i • b i))‖ ≤ Fintype.card ι * t ^ 2 ∧
      ∀ k, ‖φ (e.repr (∑ i, z i • b i) k)‖ ^ 2 * ‖φ (q (e k) (e k))‖ ≤ t ^ 2 := by
  classical
  set ρ : (F →+* ℂ) → (F →+* ℝ) := fun φ => (IsTotallyReal.complexEmbedding_isReal φ).embedding
    with hρ
  have hρc : ∀ φ x, ((ρ φ x : ℝ) : ℂ) = φ x := fun φ x => by simp [hρ]
  have hqe : ∀ x y, q x y = ∑ k, e.repr x k * e.repr y k * q (e k) (e k) := by
    intro x y
    conv_lhs => rw [← e.sum_repr x, ← e.sum_repr y]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k]
    · ring
    · intro l _ hl
      rw [he k l hl, mul_zero]
    · simp
  have htr : ∀ x : F, ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, ρ φ x := by
    intro x
    have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := F) (x := x)
    rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => φ x) _ (fun _ => rfl)] at h
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum, hρc, ← h]
    simp
  let ε : κ ≃ (F →+* ℂ) × ι := Fintype.equivOfCardEq (by
    rw [hκ, Fintype.card_prod, Embeddings.card])
  let a : κ → ℝ := fun j => ρ (ε j).1 (q (e (ε j).2) (e (ε j).2))
  let B : Matrix κ κ ℝ := Matrix.of fun i j => ρ (ε j).1 (e.repr (b i) (ε j).2)
  set T : Matrix κ κ ℚ := Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j)) with hT
  have hTB : (Rat.castHom ℝ).mapMatrix T = B * Matrix.diagonal a * Bᵀ := by
    ext i i'
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, RingHom.mapMatrix_apply, Matrix.map_apply, hT, Matrix.of_apply,
      eq_ratCast, htr, Matrix.transpose_apply, B, a]
    rw [Fintype.sum_equiv ε _ (fun p => ρ p.1 (e.repr (b i) p.2) * ρ p.1 (q (e p.2) (e p.2)) *
      ρ p.1 (e.repr (b i') p.2)) (fun _ => rfl), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [hqe, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul]; ring
  have hdT : ((T.det : ℚ) : ℝ) = B.det ^ 2 * ∏ j, a j := by
    have := (Rat.castHom ℝ).map_det T
    rw [hTB, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at this
    rw [← eq_ratCast (Rat.castHom ℝ), this]; ring
  let A : Matrix κ κ ℝ := B * Matrix.diagonal fun j => Real.sqrt |a j|
  have hdA : A.det ^ 2 = |((T.det : ℚ) : ℝ)| := by
    rw [hdT, Matrix.det_mul, Matrix.det_diagonal, mul_pow, ← Finset.prod_pow, abs_mul,
      Finset.abs_prod, abs_of_nonneg (sq_nonneg B.det)]
    simp only [Real.sq_sqrt (abs_nonneg _)]
  have hA0 : A.det ≠ 0 := by
    intro hz
    rw [hz] at hdA
    apply h0
    have : ((T.det : ℚ) : ℝ) = 0 := by simpa using hdA.symm
    exact_mod_cast this
  have hA1 : |A.det| < t ^ Fintype.card κ := by
    apply abs_lt_of_sq_lt_sq _ (by positivity)
    rwa [hdA]
  obtain ⟨z, hz0, hz⟩ := exists_int_vecMul_lt A hA0 ht hA1
  refine ⟨z, hz0, fun φ => ?_⟩
  set v := ∑ i, z i • b i with hv
  have key : ∀ k, ‖ρ φ (e.repr v k * e.repr v k * q (e k) (e k))‖ ≤ t ^ 2 := by
    intro k
    have h2 := hz (ε.symm (φ, k))
    have h3 : ∑ i, (z i : ℝ) * A i (ε.symm (φ, k)) =
        ρ φ (e.repr v k) * Real.sqrt |ρ φ (q (e k) (e k))| := by
      have hc : e.repr v k = ∑ i, (z i : F) * e.repr (b i) k := by
        rw [← e.coord_apply, hv, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_zsmul, zsmul_eq_mul, e.coord_apply]
      rw [hc, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [A, Matrix.mul_diagonal, B, a, Matrix.of_apply, Equiv.apply_symm_apply,
        mul_assoc, map_mul, map_intCast]
    rw [h3] at h2
    have h4 := (sq_lt_sq' (abs_lt.1 h2).1 (abs_lt.1 h2).2).le
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)] at h4
    rw [map_mul, map_mul, Real.norm_eq_abs, abs_mul, abs_mul_self]
    rwa [sq] at h4
  refine ⟨?_, fun k => ?_⟩
  · rw [← hρc, Complex.norm_real, hqe, map_sum]
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _k : ι, t ^ 2 := Finset.sum_le_sum fun k _ => key k
      _ = _ := by simp
  · have := key k
    rw [← Complex.norm_real, hρc, map_mul, map_mul, norm_mul, norm_mul, ← sq] at this
    exact this

theorem exists_imaginary (E : Type) [Field E] [NumberField E] [IsCMField E] :
    ∃ δ : E, δ ≠ 0 ∧ IsIntegral ℤ δ ∧ star δ = -δ := by
  obtain ⟨x, hx⟩ : ∃ x : E, star x ≠ x := by
    by_contra hc
    push Not at hc
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext hc)
  obtain ⟨M, hM, hMa⟩ := exists_int_mul_isIntegral E (Set.finite_singleton x)
  have hi := hMa x rfl
  refine ⟨M * x - star (M * x), ?_, hi.sub (isIntegral_star hi), by simp⟩
  rw [star_mul', star_intCast, ← mul_sub]
  exact mul_ne_zero (by exact_mod_cast hM) (sub_ne_zero.2 hx.symm)

theorem size_sum_le {E : Type} [Field E] [NumberField E] [IsCMField E]
    {V : Type} [AddCommGroup V] [Module E V] {h : V →ₗ[E] V →ₗ⋆[E] E} {Λ : Submodule ℤ V} {N : ℤ}
    {ν : V → ℝ} {B : ℝ} (H : Sized h Λ N ν B) {ι : Type} (s : Finset ι) (f : ι → V) :
    ν (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ν (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := H.smul_le 0 0
    simpa [house] using this
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (H.add_le _ _).trans (by linarith)

theorem shortSmall (E : Type) [Field E] [NumberField E] [IsCMField E] (hfr : FrameSmall E) : ShortSmall E := by
  classical
  intro n hn N hN
  obtain ⟨k, hk⟩ := hfr n
  obtain ⟨D, hD, hDa⟩ := exists_int_mul_isIntegral_of_trace E
  obtain ⟨δ, hδ0, hδi, hδ⟩ := exists_imaginary E
  set F := maximalRealSubfield E with hF
  have hM0 : N * D * 2 ≠ 0 := by positivity
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt
    ((2 * n : ℕ) * (|((N * D * 2 : ℤ) : ℝ)| + 1) + (1 + house δ)) (one_lt_two (α := ℝ))
  refine ⟨(2 * n : ℕ) * (|((N * D * 2 : ℤ) : ℝ)| + 1) ^ 2,
    m + (1 + (m + k) * 2) * finrank ℚ E + (m + k), ?_⟩
  intro V _ _ _ h Λ ν B hV H
  have hs := H.symm
  have hfg := H.fg
  have hO := H.stable
  have hdual := H.dual
  have hsp : span E (Λ : Set V) = ⊤ := by
    rw [eq_top_iff, ← H.span]; exact span_mono fun x hx => hx.1
  obtain ⟨e, heΛ, heo, he⟩ := hk V h Λ N ν B hV H
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ E)
  have : IsScalarTower ℚ E V := IsScalarTower.of_compHom ℚ E V
  have : Module.Finite ℤ Λ := Module.Finite.iff_fg.2 hfg
  have : IsAddTorsionFree V := .of_module_rat V
  have : Module.Free ℤ Λ := inferInstance
  let β := Module.Free.chooseBasis ℤ Λ
  let κ := Module.Free.ChooseBasisIndex ℤ Λ
  let b : κ → V := fun i => β i
  have hbZ : LinearIndependent ℤ b := β.linearIndependent.map' Λ.subtype (ker_subtype Λ)
  have hbQ : LinearIndependent ℚ b := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hbZ
  have hbΛ : ∀ x ∈ Λ, ∃ c : κ → ℤ, x = ∑ i, c i • b i := fun x hx =>
    ⟨β.repr ⟨x, hx⟩, by
      have := congrArg Λ.subtype (β.sum_repr ⟨x, hx⟩)
      rw [map_sum] at this
      exact this.symm⟩
  have hbs : ⊤ ≤ span ℚ (Set.range b) := by
    have hΛ : ∀ x ∈ Λ, x ∈ span ℚ (Set.range b) := fun x hx => by
      obtain ⟨c, rfl⟩ := hbΛ x hx
      exact sum_mem fun i _ => zsmul_mem (subset_span (Set.mem_range_self i)) _
    have key : ∀ x ∈ span E (Λ : Set V), ∀ a : E, a • x ∈ span ℚ (Set.range b) := by
      intro x hx
      induction hx using span_induction with
      | mem x hx =>
        intro a
        obtain ⟨M, hM, hMa⟩ := exists_int_mul_isIntegral E (Set.finite_singleton a)
        have h1 := smul_mem _ (M : ℚ)⁻¹ (hΛ _ (hO _ (hMa a rfl) x hx))
        rw [← smul_assoc, ← smul_mul_assoc, Algebra.smul_def] at h1
        have hM' : (M : E) ≠ 0 := by exact_mod_cast hM
        simpa [hM'] using h1
      | zero => intro a; simp
      | add x y _ _ hx hy => intro a; rw [smul_add]; exact add_mem (hx a) (hy a)
      | smul c x _ hx => intro a; rw [smul_smul]; exact hx _
    intro x _
    simpa using key x (hsp ▸ mem_top) 1
  have hFV : finrank F V = 2 * n := by
    rw [← finrank_mul_finrank F E V, hV, Algebra.IsQuadraticExtension.finrank_eq_two]
  have : FiniteDimensional F V := Module.Finite.trans E V
  have hκ : Fintype.card κ = finrank ℚ F * finrank F V := by
    rw [← finrank_eq_card_basis (Basis.mk hbQ hbs), ← finrank_mul_finrank ℚ E V,
      ← finrank_mul_finrank F E V, ← finrank_mul_finrank ℚ F E, mul_assoc]
  have hreal : ∀ x y, h x y + h y x ∈ F := fun x y => by
    rw [← IsCMField.complexConj_eq_self_iff]
    change star _ = _
    rw [star_add, ← hs, ← hs, add_comm]
  have hstF : ∀ c : F, starRingEnd E (c : E) = c := fun c => IsCMField.complexConj_apply_eq_self E c
  let q : LinearMap.BilinForm F V := LinearMap.mk₂ F (fun x y => ⟨h x y + h y x, hreal x y⟩)
    (fun x x' y => Subtype.ext (by simp; ring))
    (fun c x y => Subtype.ext (by simp [Subfield.smul_def, hstF]; ring))
    (fun x y y' => Subtype.ext (by simp; ring))
    (fun c x y => Subtype.ext (by simp [Subfield.smul_def, hstF]; ring))
  have hq : ∀ x y, (q x y : E) = h x y + h y x := fun _ _ => rfl
  have hqs : LinearMap.IsSymm q := ⟨fun x y => Subtype.ext (by simp [hq, add_comm])⟩
  have htr : ∀ x y, Algebra.trace ℚ F (q x y) = Algebra.trace ℚ E (h x y) := fun x y => by
    have h1 := Algebra.trace_trace (R := ℚ) (S := F) (T := E) (algebraMap F E (q x y))
    rw [Algebra.trace_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two, map_nsmul] at h1
    have h2 : algebraMap F E (q x y) = h x y + star (h x y) := by rw [← hs]; rfl
    rw [h2, map_add, trace_star, two_nsmul] at h1
    linarith
  set T : Matrix κ κ ℚ := Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j)) with hT
  obtain ⟨hT0, hT1⟩ := det_ne_zero_and_abs_le T hM0 (by
    intro x hx i
    set y : V := ∑ i, x i • b i with hy
    have h1 : ∀ j, ∃ m : ℤ, Algebra.trace ℚ E (h y (b j)) = m := fun j => by
      obtain ⟨m, hm⟩ := hx j
      refine ⟨m, ?_⟩
      rw [← hm, hy, map_sum, LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← algebraMap_smul E, map_smul, LinearMap.smul_apply, algebraMap_smul, map_smul, ← htr]
      rfl
    have h2 : ∀ w ∈ Λ, ∃ m : ℤ, Algebra.trace ℚ E (h y w) = m := fun w hw => by
      obtain ⟨c, rfl⟩ := hbΛ w hw
      choose m hm using h1
      refine ⟨∑ j, c j * m j, ?_⟩
      rw [map_sum, map_sum, Int.cast_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, map_zsmul, hm, zsmul_eq_mul, Int.cast_mul]
    have h3 : (N : E) • (D : E) • y ∈ Λ := hdual _ fun w hw => by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      refine hDa _ fun t ht => ?_
      obtain ⟨m, hm⟩ := h2 _ (hO _ (isIntegral_star ht) w hw)
      exact ⟨m, by rw [← hm, map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul, mul_comm]⟩
    obtain ⟨c, hc⟩ := hbΛ _ h3
    have h4 : ∑ i, ((N : ℚ) * D * x i - c i) • b i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, Int.cast_smul_eq_zsmul, ← hc, mul_smul,
        ← Finset.smul_sum, ← hy, sub_self]
    have h5 := Fintype.linearIndependent_iff.1 hbQ _ h4 i
    exact ⟨2 * c i, by push_cast; linarith⟩)
  have hcard : Fintype.card κ ≠ 0 := by
    rw [hκ, hFV]; exact mul_ne_zero finrank_pos.ne' (by omega)
  set M : ℝ := |((N * D * 2 : ℤ) : ℝ)| with hM
  have hM' : 0 ≤ M := abs_nonneg _
  let s : Bool → E := fun u => if u then δ else 1
  have hs0 : ∀ u, s u ≠ 0 := fun u => by cases u <;> simp [s, hδ0]
  have hsi : ∀ u, IsIntegral ℤ (s u) := fun u => by cases u <;> simp [s, hδi, isIntegral_one]
  have hsh : ∀ u, house (s u) ≤ 1 + house δ := fun u => by
    have h1 := house_intCast (K := E) 1
    have h2 := house_nonneg δ
    cases u <;> simp [s] at h1 ⊢
    linarith
  let g : Fin n × Bool → V := fun p => s p.2 • e p.1
  have hgΛ : ∀ p, g p ∈ Λ := fun p => hO _ (hsi _) _ (heΛ _)
  have hgo : ∀ p l, l ≠ p → q (g l) (g p) = 0 := by
    rintro ⟨i, u⟩ ⟨j, w⟩ hne
    apply Subtype.ext
    rw [hq]
    by_cases hij : j = i
    · subst hij
      have : w ≠ u := fun h0 => hne (by rw [h0])
      cases u <;> cases w <;> simp [g, s, starRingEnd_apply, hδ] at this ⊢
    · simp [g, heo j i hij, heo i j (Ne.symm hij)]
  have hg0 : ∀ p, (q (g p) (g p) : E) ≠ 0 := fun p => by
    rw [hq, ← two_mul]
    simp [g, hs0, (he p.1).1]
  have hgli : LinearIndependent F g := LinearMap.linearIndependent_of_isOrthoᵢ (B := q)
    (fun p l hpl => hgo l p hpl) fun p h0 => hg0 p (by rw [h0]; rfl)
  have hcι : Fintype.card (Fin n × Bool) = 2 * n := by simp [mul_comm]
  let γ : Basis (Fin n × Bool) F V := basisOfLinearIndependentOfCardEqFinrank' g hgli (by rw [hcι, hFV])
  have hγ : ∀ p, γ p = g p := fun p => by simp [γ]
  obtain ⟨z, hz0, hz⟩ := exists_short_coord γ q (fun p l hl => by rw [hγ, hγ]; exact hgo p l hl) b
    (by rw [hκ, hcι, hFV]) (t := M + 1) (by positivity) hT0 (by
    have h1 : |((T.det : ℚ) : ℝ)| ≤ M ^ Fintype.card κ := by rw [hM]; exact_mod_cast hT1
    have h2 : M ^ Fintype.card κ < (M + 1) ^ Fintype.card κ :=
      pow_lt_pow_left₀ (by linarith) hM' hcard
    have h3 : 1 ≤ (M + 1) ^ Fintype.card κ := one_le_pow₀ (by linarith)
    refine h1.trans_lt (h2.trans_le ?_)
    nlinarith)
  refine ⟨∑ i, z i • b i, sum_mem fun i _ => Λ.smul_mem _ (β i).2, fun h0 => hz0 ?_, ?_, ?_⟩
  · exact funext (Fintype.linearIndependent_iff.1 hbZ z h0)
  · rw [house, pi_norm_le_iff_of_nonneg (by positivity)]
    intro φ
    have h1 := (hz (φ.comp (algebraMap F E))).1
    rw [hcι] at h1
    refine le_trans ?_ h1
    change ‖φ (h _ _)‖ ≤ ‖φ (h _ _ + h _ _)‖
    rw [← two_mul, map_mul, norm_mul, map_ofNat, Complex.norm_ofNat]
    linarith [norm_nonneg (φ (h (∑ i, z i • b i) (∑ i, z i • b i)))]
  · set v := ∑ i, z i • b i with hv
    have hB := H.two_le
    have hB1 : 1 ≤ B := by linarith
    have hBm : (2 : ℝ) ^ m ≤ B ^ m := pow_le_pow_left₀ (by norm_num) hB m
    have hδn := house_nonneg δ
    have hn0 : (0 : ℝ) ≤ (2 * n : ℕ) * (M + 1) := by positivity
    have hgν : ∀ p, ν (g p) ≤ B ^ (m + k) := fun p => by
      refine (H.smul_le _ _).trans ?_
      rw [pow_add]
      exact mul_le_mul ((hsh _).trans (by linarith)) (he p.1).2 (H.nonneg _) (by positivity)
    have hga : ∀ p, house (q (g p) (g p) : E) ≤ B ^ (1 + (m + k) * 2) := fun p => by
      rw [hq, pow_add, pow_one, pow_mul]
      refine (house_add_le _ _).trans ?_
      have h1 : house (h (g p) (g p)) ≤ (B ^ (m + k)) ^ 2 := by
        refine (H.form_le _ _).trans ?_
        rw [sq]
        exact mul_le_mul (hgν p) (hgν p) (H.nonneg _) (by positivity)
      have h2 : 0 ≤ (B ^ (m + k)) ^ 2 := by positivity
      nlinarith
    set U : ℝ := (B ^ (1 + (m + k) * 2)) ^ finrank ℚ E with hU
    have hU1 : 1 ≤ U := one_le_pow₀ (one_le_pow₀ hB1)
    have hc : ∀ p, house (γ.repr v p : E) ≤ (M + 1) * U := fun p => by
      rw [house, pi_norm_le_iff_of_nonneg (by positivity)]
      intro φ
      have h1 : ‖φ (γ.repr v p : E)‖ ^ 2 * ‖φ (q (γ p) (γ p) : E)‖ ≤ (M + 1) ^ 2 :=
        (hz (φ.comp (algebraMap F E))).2 p
      rw [hγ] at h1
      have h2 := one_le_norm_mul_pow (a := (q (g p) (g p) : E))
        (by rw [hq]; exact (H.int _ (hgΛ p) _ (hgΛ p)).add (H.int _ (hgΛ p) _ (hgΛ p))) (hg0 p)
        (one_le_pow₀ hB1) (hga p) φ
      rw [← hU] at h2
      change ‖φ (γ.repr v p : E)‖ ≤ _
      refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
      calc ‖φ (γ.repr v p : E)‖ ^ 2 ≤ ‖φ (γ.repr v p : E)‖ ^ 2 * (‖φ (q (g p) (g p) : E)‖ * U) :=
            le_mul_of_one_le_right (by positivity) h2
        _ ≤ (M + 1) ^ 2 * U := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ ((M + 1) * U) ^ 2 := by
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    calc ν v = ν (∑ p, γ.repr v p • γ p) := by rw [γ.sum_repr]
      _ ≤ ∑ p, ν (γ.repr v p • γ p) := size_sum_le H _ _
      _ ≤ ∑ _p : Fin n × Bool, (M + 1) * U * B ^ (m + k) := Finset.sum_le_sum fun p _ => by
          rw [hγ]
          exact (H.smul_le (γ.repr v p : E) (g p)).trans
            (mul_le_mul (hc p) (hgν p) (H.nonneg _) (by positivity))
      _ = (2 * n : ℕ) * (M + 1) * U * B ^ (m + k) := by
          rw [Finset.sum_const, Finset.card_univ, hcι, nsmul_eq_mul]; ring
      _ ≤ B ^ m * U * B ^ (m + k) := by gcongr; linarith
      _ = _ := by rw [hU, ← pow_mul, ← pow_add, ← pow_add]

end GlobalTheory.SmoothForms.Short

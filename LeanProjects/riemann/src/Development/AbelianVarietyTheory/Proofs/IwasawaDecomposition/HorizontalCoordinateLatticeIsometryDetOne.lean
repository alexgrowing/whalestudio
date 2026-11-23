import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RelabBijective

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix

namespace GlobalTheory.ShFam.HorIso

section General

variable {R L J : Type} [CommRing R] [AddCommGroup L] [Module R L] [Fintype J] [DecidableEq J]

theorem multilinear_add_sub_mem (F : MultilinearMap R (fun _ : J => L) R) (I : Ideal R) (v w : J → L)
    (hw : ∀ j, w j ∈ I • (⊤ : Submodule R L)) : F (w + v) - F v ∈ I * Ideal.span (Set.range F) := by
  have key : ∀ (y : J → L) (j : J) (z : L), z ∈ I • (⊤ : Submodule R L) →
      F (Function.update y j z) ∈ I * Ideal.span (Set.range F) := by
    intro y j z hz
    refine Submodule.smul_induction_on hz (fun r hr t _ => ?_) (fun a b ha hb => ?_)
    · rw [F.map_update_smul, smul_eq_mul]
      exact Ideal.mul_mem_mul hr (Ideal.subset_span ⟨_, rfl⟩)
    · rw [F.map_update_add]
      exact add_mem ha hb
  rw [F.map_add_univ, ← Finset.add_sum_erase _ _ (Finset.mem_univ ∅), Finset.piecewise_empty, add_sub_cancel_left]
  refine Ideal.sum_mem _ fun s hs => ?_
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 (Finset.ne_of_mem_erase hs)
  have := key (s.piecewise w v) j (w j) (hw j)
  rwa [← Finset.piecewise_eq_of_mem s w v hj, Function.update_eq_self] at this

theorem multiplier_congr [IsDedekindDomain R] (F : MultilinearMap R (fun _ : J => L) R) (I : Ideal R) (g : L → L)
    (hg : ∀ v, g v - v ∈ I • (⊤ : Submodule R L)) (v₀ : J → L) (h₀ : F v₀ ≠ 0) (c D : R)
    (h : ∀ v : J → L, c * F (fun j => g (v j)) = D * F v) : ∃ i ∈ I, D = c * (1 + i) := by
  have hN : Ideal.span (Set.range F) ≠ 0 := fun e => h₀ (by
    have : F v₀ ∈ Ideal.span (Set.range F) := Ideal.subset_span ⟨_, rfl⟩
    rw [e] at this
    simpa using this)
  have hle : Ideal.span {D - c} * Ideal.span (Set.range F) ≤ (Ideal.span {c} * I) * Ideal.span (Set.range F) := by
    rw [Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨_, rfl, _, ⟨v, rfl⟩, rfl⟩
    have h1 := multilinear_add_sub_mem F I v (fun j => g (v j) - v j) fun j => hg _
    have h2 : (fun j => g (v j) - v j) + v = fun j => g (v j) := by ext j; simp
    rw [h2] at h1
    have h3 : (D - c) * F v = c * (F (fun j => g (v j)) - F v) := by rw [mul_sub, h]; ring
    show (D - c) * F v ∈ _
    rw [h3, mul_assoc]
    exact Ideal.mul_mem_mul (Ideal.subset_span rfl) h1
  rw [← Ideal.dvd_iff_le, mul_dvd_mul_iff_right hN, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem,
    Ideal.mem_span_singleton_mul] at hle
  obtain ⟨i, hi, e⟩ := hle
  exact ⟨i, hi, by rw [mul_add, e]; ring⟩

theorem exists_coord [Module.Finite R L] (x : J → L) (hx : LinearIndependent R x)
    (hs : ∀ v, ∃ n : ℕ, n ≠ 0 ∧ n • v ∈ Submodule.span R (Set.range x)) :
    ∃ (n : ℕ) (ψ : L →ₗ[R] (J → R)), n ≠ 0 ∧ (∀ v, n • v = ∑ k, ψ v k • x k) ∧
      ∀ k, ψ (x k) = Pi.single k (n : R) := by
  obtain ⟨s, hs'⟩ := Module.Finite.fg_top (R := R) (M := L)
  choose d hd0 hd using hs
  have hn : ∀ v, (∏ t ∈ s, d t) • v ∈ Submodule.span R (Set.range x) := by
    intro v
    have hv : v ∈ Submodule.span R (s : Set L) := hs' ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem d ht
      rw [he, mul_comm, mul_smul]
      exact nsmul_mem (hd t) e
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
    | smul a b _ hb => rw [smul_comm]; exact Submodule.smul_mem _ _ hb
  set n := ∏ t ∈ s, d t
  let ψ : L →ₗ[R] (J → R) := (Finsupp.linearEquivFunOnFinite R R J).toLinearMap ∘ₗ hx.repr ∘ₗ
    LinearMap.codRestrict _ (n • LinearMap.id) hn
  have hψ : ∀ v, n • v = ∑ k, ψ v k • x k := fun v => by
    have := hx.linearCombination_repr ⟨n • v, hn v⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at this
    exact this.symm
  refine ⟨n, ψ, Finset.prod_ne_zero_iff.2 fun t _ => hd0 t, hψ, fun k => ?_⟩
  refine hx.fintypeLinearCombination_injective ?_
  rw [Fintype.linearCombination_apply, ← hψ, Fintype.linearCombination_apply_single, Nat.cast_smul_eq_nsmul]

end General

theorem horVal_change {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {G B B' : Matrix (m ⊕ n) (m ⊕ n) ℂ} {C : Matrix n (m ⊕ n) ℂ} {C' : Matrix m (m ⊕ n) ℂ} (hG : G.det ≠ 0)
    (hB : Bᵀ * G * B' = G) (h0 : C * ((Gᵀ)⁻¹ * C'ᵀ) = 0) (hR : ∃ R : Matrix m (m ⊕ n) ℂ, R * ((Gᵀ)⁻¹ * C'ᵀ) = 1)
    (hS : ∃ S : Matrix (m ⊕ n) n ℂ, C * S = 1) :
    (C * B * ((Gᵀ)⁻¹ * (C' * B')ᵀ) = 0 ∧ (∃ R : Matrix m (m ⊕ n) ℂ, R * ((Gᵀ)⁻¹ * (C' * B')ᵀ) = 1) ∧
      ∃ S : Matrix (m ⊕ n) n ℂ, C * B * S = 1) ∧
    horVal ((Gᵀ)⁻¹ * (C' * B')ᵀ) (C * B) = horVal ((Gᵀ)⁻¹ * C'ᵀ) C * B.det := by
  obtain ⟨R, hR⟩ := hR
  obtain ⟨S, hS⟩ := hS
  have hu : IsUnit (Gᵀ).det := by rw [Matrix.det_transpose]; exact hG.isUnit
  have h1 : B'ᵀ * Gᵀ * B = Gᵀ := by
    have := congrArg Matrix.transpose hB
    simpa [Matrix.mul_assoc] using this
  have h2 : B * ((Gᵀ)⁻¹ * B'ᵀ * Gᵀ) = 1 := by
    rw [mul_eq_one_comm, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc B'ᵀ, h1, Matrix.nonsing_inv_mul _ hu]
  have h3 : B * ((Gᵀ)⁻¹ * B'ᵀ) = (Gᵀ)⁻¹ := by
    have := congrArg (· * (Gᵀ)⁻¹) h2
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu] using this
  have h4 : B * ((Gᵀ)⁻¹ * (C' * B')ᵀ) = (Gᵀ)⁻¹ * C'ᵀ := by
    rw [Matrix.transpose_mul, ← Matrix.mul_assoc _ B'ᵀ, ← Matrix.mul_assoc, h3]
  have a0 : C * B * ((Gᵀ)⁻¹ * (C' * B')ᵀ) = 0 := by rw [Matrix.mul_assoc, h4, h0]
  have aR : R * B * ((Gᵀ)⁻¹ * (C' * B')ᵀ) = 1 := by rw [Matrix.mul_assoc, h4, hR]
  have aS : C * B * (((Gᵀ)⁻¹ * B'ᵀ * Gᵀ) * S) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc B, h2, Matrix.one_mul, hS]
  refine ⟨⟨a0, ⟨_, aR⟩, ⟨_, aS⟩⟩, ?_⟩
  rw [horVal_eq a0 aR aS, horVal_eq h0 hR hS, ← Matrix.fromRows_mul, Matrix.det_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eq_one_of_norm_eq_one (l : Level H) (hl : ∀ p : ℕ, p.Prime → l.GoodAt p) (d : 𝓞 E)
    (hd : ∀ ρ : E →+* ℂ, ‖ρ d‖ = 1) (hm : d - 1 ∈ l.Mb) : d = 1 := by
  obtain ⟨k, hk, hdk⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ d.isIntegral_coe hd
  have hfin : IsOfFinOrder d := isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, by ext; simpa using hdk⟩
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (mt orderOf_eq_one_iff.1 hne)
  set z := d ^ (orderOf d / p) with hz
  have ho : orderOf z = p := orderOf_pow_orderOf_div hfin.orderOf_pos.ne' hpd
  have hz1 : z - 1 ∈ l.Mb := Ideal.mem_of_dvd _ (sub_one_dvd_pow_sub_one d _) hm
  have hsum : ∑ i ∈ Finset.range p, z ^ i = 0 :=
    (ho ▸ IsPrimitiveRoot.orderOf z : IsPrimitiveRoot z p).geom_sum_eq_zero hp.one_lt
  have hpm : (p : 𝓞 E) ∈ l.Mb := by
    have : (p : 𝓞 E) = -∑ i ∈ Finset.range p, (z ^ i - 1) := by simp [Finset.sum_sub_distrib, hsum]
    rw [this]
    exact neg_mem (Ideal.sum_mem _ fun i _ => Ideal.mem_of_dvd _ (sub_one_dvd_pow_sub_one z _) hz1)
  have hpm' : (p : 𝓞 E) ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpm
  have h2 := Ideal.mul_mem_mul hpm hpm'
  rw [l.prod, Ideal.mem_span_singleton] at h2
  have h3 := map_dvd (Algebra.norm ℤ) h2
  have hn : ∀ a : ℕ, Algebra.norm ℤ (a : 𝓞 E) = (a : ℤ) ^ Module.finrank ℤ (𝓞 E) := fun a => by
    simpa using Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 E) (a : ℤ)
  rw [map_mul, hn, hn, ← pow_add] at h3
  have h4 : l.M ∣ p ^ (Module.finrank ℤ (𝓞 E) + Module.finrank ℤ (𝓞 E)) := by
    exact_mod_cast (dvd_pow_self (l.M : ℤ) Module.finrank_pos.ne').trans h3
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h4
  have h5 := hl p hp
  rw [Level.GoodAt, hj, hp.factorization_pow, Finsupp.single_eq_same, Nat.div_self (pow_pos hp.pos _)] at h5
  omega

theorem eq_zero_of_trace (z : E) (h : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * z) = 0) : z = 0 := by
  refine (traceForm_nondegenerate ℚ E).1 z fun y => ?_
  have : Algebra.traceForm ℚ E z = 0 := (integralBasis E).ext fun i => by
    rw [integralBasis_apply, Algebra.traceForm_apply, mul_comm]
    exact h _
  rw [this]; rfl

theorem sub_mem_of_isLev (l : Level H) (Di : Datum H) (gm : Di.La ≃ₗ[𝓞 E] Di.La) (h : IsLev l Di gm) (v : Di.La) :
    gm v - v ∈ l.Mb • (⊤ : Submodule (𝓞 E) Di.La) := by
  haveI := Di.proj
  have key : ∀ t ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), ∃ y ∈ l.Mb • (⊤ : Submodule (𝓞 E) Di.La),
      t • (gm v - v) = (l.M : 𝓞 E) • y := by
    intro t ht
    refine Submodule.mul_induction_on ht (fun a ha b hb => ?_) ?_
    · obtain ⟨e, he⟩ := h (b • v) (Submodule.smul_mem_smul hb Submodule.mem_top)
      refine ⟨a • e, Submodule.smul_mem_smul ha Submodule.mem_top, ?_⟩
      rw [mul_smul, smul_sub, ← map_smul, he, add_sub_cancel_left, smul_comm, Nat.cast_smul_eq_nsmul]
    · rintro a b ⟨y, hy, e⟩ ⟨y', hy', e'⟩
      exact ⟨y + y', add_mem hy hy', by rw [add_smul, e, e', smul_add]⟩
  obtain ⟨y, hy, e⟩ := key (l.M : 𝓞 E) (by rw [l.prod]; exact Ideal.subset_span rfl)
  have hM : (l.M : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  rwa [smul_right_injective Di.La hM e]

theorem exists_matrix (Di : Datum H) {J : Type} [Fintype J] [DecidableEq J] (x : J → Di.La) (hm : Matrix J J E)
    (hx : IsPerBasis Di x hm) (gm : Di.La ≃ₗ[𝓞 E] Di.La) (hg : IsIsom Di gm) :
    ∃ m : Matrix J J E, mᵀ * hm * m.map (IsCMField.complexConj E) = hm ∧
      (∀ (ρ : E →+* ℂ) (f : Di.La →+ ℂ), (∀ (a : 𝓞 E) v, f (a • v) = ρ a * f v) →
        ∀ k, f (gm (x k)) = ∑ j, f (x j) * ρ (m j k)) ∧
      ∀ I : Ideal (𝓞 E), (∀ v, gm v - v ∈ I • (⊤ : Submodule (𝓞 E) Di.La)) →
        ∃ d : 𝓞 E, d - 1 ∈ I ∧ m.det = d := by
  haveI := Di.fin
  obtain ⟨hli, hsp, htr, -⟩ := hx
  obtain ⟨n, ψ, hn, hψ, hψx⟩ := exists_coord x hli hsp
  have hnE : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn
  let A : Matrix J J (𝓞 E) := Matrix.of fun j k => ψ (gm (x k)) j
  have hA : ∀ k, n • gm (x k) = ∑ j, A j k • x j := fun k => hψ _
  refine ⟨(n : E)⁻¹ • A.map (algebraMap (𝓞 E) E), ?_, ?_, ?_⟩
  · ext k k'
    rw [← sub_eq_zero]
    refine eq_zero_of_trace _ fun a => ?_
    have hb : ∀ (b : 𝓞 E) u w, Di.EF u (b • w) = Di.EF (H.bar b • u) w := fun b u w => by
      rw [Di.adj]
      congr 2
      ext
      rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
    have h1 : (n : ℤ) * (n : ℤ) * Di.EF (a • x k) (x k') =
        ∑ j, ∑ j', Di.EF ((H.bar (A j' k') * (a * A j k)) • x j) (x j') := by
      have e1 : (n : ℤ) * (n : ℤ) * Di.EF (a • x k) (x k') = Di.EF (a • n • gm (x k)) (n • gm (x k')) := by
        rw [← hg, map_smul, smul_comm a n, map_nsmul, map_nsmul]
        simp [mul_assoc]
      rw [e1, hA, hA, Finset.smul_sum, LinearMap.map_sum₂]
      simp only [map_sum, LinearMap.sum_apply, hb, mul_smul]
    have h2 := congrArg (Int.cast : ℤ → ℚ) h1
    push_cast at h2
    simp only [htr, ← map_sum] at h2
    have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn
    rw [mul_sub, map_sub, sub_eq_zero]
    refine mul_left_cancel₀ (mul_ne_zero hnQ hnQ) ?_
    rw [h2, ← smul_eq_mul, ← map_smul, Algebra.smul_def]
    congr 1
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    simp only [map_mul, map_natCast, map_inv₀, H.bar_eq, RingOfIntegers.coe_eq_algebraMap]
    field_simp
  · intro ρ f hf k
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    refine mul_left_cancel₀ hnC ?_
    rw [← nsmul_eq_mul, ← map_nsmul, hA, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hf, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, map_inv₀]
    field_simp
  · intro I hI
    let F : MultilinearMap (𝓞 E) (fun _ : J => Di.La) (𝓞 E) :=
      (Matrix.detRowAlternating (n := J) (R := 𝓞 E)).toMultilinearMap.compLinearMap fun _ => ψ
    have hF : ∀ v, F v = (Matrix.of fun j => ψ (v j)).det := fun v => rfl
    have hnO : (n : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hn
    have h0 : F x ≠ 0 := by
      have : (Matrix.of fun j => ψ (x j)) = (n : 𝓞 E) • (1 : Matrix J J (𝓞 E)) := by
        ext j k
        simp [hψx, Pi.single_apply, Matrix.one_apply, eq_comm]
      rw [hF, this, Matrix.det_smul, Matrix.det_one, mul_one]
      exact pow_ne_zero _ hnO
    obtain ⟨i, hi, e⟩ := multiplier_congr F I gm hI x h0 ((n : 𝓞 E) ^ Fintype.card J) A.det fun v => by
      rw [hF, hF, ← Matrix.det_smul, mul_comm, ← Matrix.det_transpose A, ← Matrix.det_mul]
      congr 1
      ext1 j k
      have := congrArg (fun u => ψ (gm u) k) (hψ (v j))
      simpa [Matrix.mul_apply, A] using this
    refine ⟨1 + i, by simpa using hi, ?_⟩
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, e]
    simp only [map_mul, map_pow, map_natCast]
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hnE, one_pow, one_mul]

theorem perVal_isom (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (c : Coeff l) (σ : c.F →+* ℂ) (Di : Datum H) (τ : E →+* ℂ) (x : Idx Dw τ → Di.La)
    (hm : Matrix (Idx Dw τ) (Idx Dw τ) E) (Q : Di.La →+ (Letter Dw → ℂ)) (gm : Di.La ≃ₗ[𝓞 E] Di.La)
    (hx : IsPerBasis Di x hm) (hQ : GoodPer c σ τ x hm Q) (hg : IsIsom Di gm) :
    GoodPer c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom) ∧
      ‖perVal c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom)‖ = ‖perVal c σ τ x hm Q‖ ∧
      ((∀ p : ℕ, p.Prime → l.GoodAt p) → IsLev l Di gm →
        perVal c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom) = perVal c σ τ x hm Q) := by
  obtain ⟨m, hgram, hper, hdet⟩ := exists_matrix Di x hm hx gm hg
  obtain ⟨hlin, h0, hR, hS⟩ := hQ
  have hP : ∀ ρ : E →+* ℂ, perMat x (Q.comp gm.toLinearMap.toAddMonoidHom) ρ =
      perMat x Q ρ * m.map (Formalism.L2.PjFree.relab c σ ρ) := fun ρ => by
    ext i k
    exact hper (Formalism.L2.PjFree.relab c σ ρ) ((Pi.evalAddMonoidHom (fun _ => ℂ) (⟨ρ, i⟩ : Letter Dw)).comp Q)
      (fun a v => hlin a v ⟨ρ, i⟩) k
  have hG : ∀ ρ : E →+* ℂ, (m.map ρ)ᵀ * hm.map ρ * m.map (conjEmb ρ) = hm.map ρ := fun ρ => by
    have h1 : m.map (conjEmb ρ) = (m.map (IsCMField.complexConj E)).map ρ := by
      ext i j
      exact (IsCMField.complexEmbedding_complexConj E ρ _).symm
    rw [h1, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hgram]
  have hdm : ∀ (ρ : E →+* ℂ) (u : Matrix (Idx Dw τ) (Idx Dw τ) E), (u.map ρ).det = ρ u.det := fun ρ u =>
    (RingHom.map_det ρ u).symm
  have hG0 : ∀ ρ : E →+* ℂ, (hm.map ρ).det ≠ 0 := fun ρ => by
    rw [hdm]; exact (map_ne_zero ρ).2 hx.2.2.2
  have hnorm : ∀ ρ : E →+* ℂ, ‖ρ m.det‖ = 1 := fun ρ => by
    have h1 := congrArg Matrix.det (hG ρ)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_right_comm, mul_eq_right₀ (hG0 ρ), hdm, hdm] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one, show conjEmb ρ m.det = starRingEnd ℂ (ρ m.det) from rfl, Complex.norm_conj] at h2
    nlinarith [norm_nonneg (ρ m.det)]
  have hG1 := hG (Formalism.L2.PjFree.relab c σ τ)
  rw [← GlobalTheory.UnifDataTest.relab_conj] at hG1
  obtain ⟨hgood, hval⟩ := horVal_change (hG0 _) hG1 h0 hR hS
  have hv : perVal c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom) =
      perVal c σ τ x hm Q * Formalism.L2.PjFree.relab c σ τ m.det := by
    rw [perVal, kerMat, hP, hP, hval, hdm]; rfl
  refine ⟨⟨fun a v z => ?_, ?_⟩, ?_, fun hl hlev => ?_⟩
  · simpa using hlin a (gm v) z
  · rw [kerMat, hP, hP]; exact hgood
  · rw [hv, norm_mul, hnorm, mul_one]
  · obtain ⟨d, hd, e⟩ := hdet l.Mb (sub_mem_of_isLev l Di gm hlev)
    rw [hv, e, eq_one_of_norm_eq_one l hl d (fun ρ => e ▸ hnorm ρ) hd]
    simp

end GlobalTheory.ShFam.HorIso

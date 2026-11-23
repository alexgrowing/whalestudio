import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal

namespace GlobalTheory.CompanionTheory.SiegelChar

section Abstract

variable {E : Type} [CommRing E] {R : Type} [Ring R] [Algebra E R] {c : E → E} {σ : R →+ R}
  {G : Type} [Group G] {φ : G →* R} {e f : R}

theorem lower_triv (hsm : ∀ (a : E) (x : R), σ (a • x) = c a • σ x) (h1 : σ 1 = 1)
    {i2 i3 : E} (h2 : 2 * i2 = 1) (h3 : 3 * i3 = 1) (c2 : c 2 = 2) (ci2 : c i2 = i2) (ci3 : c i3 = i3)
    (hinj : Function.Injective φ) (hsurj : ∀ x, σ x * x = 1 → ∃ g, φ g = x)
    (hef : e + f = 1) (hee : e * e = e) (hff : f * f = f) (hef0 : e * f = 0) (hfe0 : f * e = 0)
    (hse : σ e = f) (hsf : σ f = e) (lam : G →* ℂˣ) (s : R) (hes : e * s = 0) (hsf0 : s * f = 0) (hs : σ s = -s) :
    ∃ n, φ n = 1 + s ∧ lam n = 1 := by
  have hsfe : ∀ t : R, e * t = 0 → f * t = t := fun t ht => by
    calc f * t = e * t + f * t := by rw [ht, zero_add]
      _ = t := by rw [← add_mul, hef, one_mul]
  have htee : ∀ t : R, t * f = 0 → t * e = t := fun t ht => by
    calc t * e = t * e + t * f := by rw [ht, add_zero]
      _ = t := by rw [← mul_add, hef, mul_one]
  have hsq : ∀ t : R, e * t = 0 → t * f = 0 → t * t = 0 := fun t h1' h2' => by
    calc t * t = (t * e) * (f * t) := by rw [htee t h2', hsfe t h1']
      _ = t * (e * f) * t := by simp only [mul_assoc]
      _ = 0 := by rw [hef0, mul_zero, zero_mul]
  have hpow : ∀ (y : R), y * y = 0 → ∀ k : ℕ, (1 + y) ^ k = 1 + (k : R) * y := by
    intro y hy k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, Nat.cast_succ]
      have hky : (k : R) * y * y = 0 := by rw [mul_assoc, hy, mul_zero]
      calc (1 + (k : R) * y) * (1 + y) = 1 + (k : R) * y + y + (k : R) * y * y := by noncomm_ring
        _ = 1 + ((k : R) + 1) * y := by rw [hky]; noncomm_ring
  have hnat : ∀ (k : ℕ) (a : E) (t : R), (k : R) * (a • t) = ((k : E) * a) • t := by
    intro k a t
    rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul E, smul_smul]
  have hunit : ∀ t : R, σ t = -t → t * t = 0 → σ (1 + t) * (1 + t) = 1 := by
    intro t hts htt
    rw [map_add, h1, hts]
    calc (1 + -t) * (1 + t) = 1 - t * t := by noncomm_ring
      _ = 1 := by rw [htt, sub_zero]
  have h2' : i2 * 2 = 1 := by rw [mul_comm, h2]
  have key : ∀ (t : R), e * t = 0 → t * f = 0 → σ t = -t → ∀ n : G, φ n = 1 + t → lam n ^ 3 = 1 := by
    intro t hte htf hts n hn
    obtain ⟨d, hd⟩ : ∃ d : R, d = (2 : E) • e + i2 • f := ⟨_, rfl⟩
    obtain ⟨d', hd'⟩ : ∃ d' : R, d' = i2 • e + (2 : E) • f := ⟨_, rfl⟩
    have hdd' : d * d' = 1 := by
      rw [hd, hd']
      simp only [add_mul, mul_add, smul_mul_smul_comm, hee, hff, hef0, hfe0, smul_zero, add_zero,
        zero_add, h2, h2', one_smul, hef]
    have hd'd : d' * d = 1 := by
      rw [hd, hd']
      simp only [add_mul, mul_add, smul_mul_smul_comm, hee, hff, hef0, hfe0, smul_zero, add_zero,
        zero_add, h2, h2', one_smul, hef]
    have hσd : σ d * d = 1 := by
      rw [hd, map_add, hsm, hsm, c2, ci2, hse, hsf]
      simp only [add_mul, mul_add, smul_mul_smul_comm, hee, hff, hef0, hfe0, smul_zero, add_zero,
        zero_add, h2, h2', one_smul]
      first
        | exact hef
        | (rw [add_comm]; exact hef)
    obtain ⟨td, htd⟩ := hsurj d hσd
    have htdinv : φ td⁻¹ = d' := by
      have h0 : d * φ td⁻¹ = 1 := by rw [← htd, ← map_mul, mul_inv_cancel, map_one]
      calc φ td⁻¹ = (d' * d) * φ td⁻¹ := by rw [hd'd, one_mul]
        _ = d' := by rw [mul_assoc, h0, mul_one]
    have hdt : d * t = i2 • t := by
      rw [hd, add_mul, smul_mul_assoc, smul_mul_assoc, hte, smul_zero, zero_add, hsfe t hte]
    have htd' : t * d' = i2 • t := by
      rw [hd', mul_add, mul_smul_comm, mul_smul_comm, htf, smul_zero, add_zero, htee t htf]
    have hm : φ (td * n * td⁻¹) = 1 + (i2 * i2) • t := by
      rw [map_mul, map_mul, htd, htdinv, hn, mul_add, mul_one, add_mul, hdd', hdt, smul_mul_assoc,
        htd', smul_smul]
    have hyy : ((i2 * i2) • t) * ((i2 * i2) • t) = 0 := by
      rw [smul_mul_smul_comm, hsq t hte htf, smul_zero]
    have hm4 : (td * n * td⁻¹) ^ 4 = n := by
      apply hinj
      rw [map_pow, hm, hpow _ hyy 4, hn, hnat]
      have h4 : ((4 : ℕ) : E) * (i2 * i2) = 1 := by
        push_cast
        calc (4 : E) * (i2 * i2) = (2 * i2) * (2 * i2) := by ring
          _ = 1 := by rw [h2, one_mul]
      rw [h4, one_smul]
    have hlm : lam (td * n * td⁻¹) = lam n := by
      rw [map_mul, map_mul, map_inv, mul_comm (lam td), mul_assoc, mul_inv_cancel, mul_one]
    have h4 : lam n = lam n ^ 4 := by
      conv_lhs => rw [← hm4]
      rw [map_pow, hlm]
    have h5 : lam n ^ 3 * lam n = 1 * lam n := by
      rw [one_mul, ← pow_succ]
      exact h4.symm
    exact mul_right_cancel h5
  obtain ⟨n, hn⟩ := hsurj (1 + s) (hunit s hs (hsq s hes hsf0))
  have hes' : e * (i3 • s) = 0 := by rw [mul_smul_comm, hes, smul_zero]
  have hsf' : (i3 • s) * f = 0 := by rw [smul_mul_assoc, hsf0, smul_zero]
  have hs' : σ (i3 • s) = -(i3 • s) := by rw [hsm, ci3, hs, smul_neg]
  obtain ⟨n', hn'⟩ := hsurj (1 + i3 • s) (hunit _ hs' (hsq _ hes' hsf'))
  have hn3 : n' ^ 3 = n := by
    apply hinj
    rw [map_pow, hn', hpow _ (hsq _ hes' hsf') 3, hn, hnat]
    have h3' : ((3 : ℕ) : E) * i3 = 1 := by
      push_cast
      exact h3
    rw [h3', one_smul]
  refine ⟨n, hn, ?_⟩
  rw [← hn3, map_pow]
  exact key _ hes' hsf' hs' n' hn'

theorem cell_triv (hmul : ∀ x y, σ (x * y) = σ y * σ x) (h1 : σ 1 = 1) (hu : ∀ g, σ (φ g) * φ g = 1)
    (hef : e + f = 1) (hee : e * e = e) (hff : f * f = f) (hef0 : e * f = 0) (hfe0 : f * e = 0)
    (hse : σ e = f) (hsf : σ f = e) (lam : G →* ℂˣ)
    (hlow : ∀ s, e * s = 0 → s * f = 0 → σ s = -s → ∃ n, φ n = 1 + s ∧ lam n = 1)
    (hP : ∀ g, f * φ g * e = 0 → lam g = 1) (g : G) (hg : IsUnit (φ g * e + f)) : lam g = 1 := by
  obtain ⟨x, hx⟩ : ∃ x : R, x = φ g := ⟨_, rfl⟩
  rw [← hx] at hg
  have hux : σ x * x = 1 := by rw [hx]; exact hu g
  obtain ⟨u, hu'⟩ := hg
  obtain ⟨w, hw⟩ : ∃ w : R, w = ↑u⁻¹ := ⟨_, rfl⟩
  have hwu : w * (x * e + f) = 1 := by rw [hw, ← hu', Units.inv_mul]
  have huw : (x * e + f) * w = 1 := by rw [hw, ← hu', Units.mul_inv]
  have he2 : ∀ z, e * (e * z) = e * z := fun z => by rw [← mul_assoc, hee]
  have hf2 : ∀ z, f * (f * z) = f * z := fun z => by rw [← mul_assoc, hff]
  have hef2 : ∀ z, e * (f * z) = 0 := fun z => by rw [← mul_assoc, hef0, zero_mul]
  have hfe2 : ∀ z, f * (e * z) = 0 := fun z => by rw [← mul_assoc, hfe0, zero_mul]
  have hwf : w * f = f := by
    have h0 : (x * e + f) * f = f := by rw [add_mul, mul_assoc, hef0, mul_zero, zero_add, hff]
    calc w * f = w * ((x * e + f) * f) := by rw [h0]
      _ = f := by rw [← mul_assoc, hwu, one_mul]
  have hwxe : w * (x * e) = e := by
    have h0 : (x * e + f) * e = x * e := by rw [add_mul, mul_assoc, hee, hfe0, add_zero]
    calc w * (x * e) = w * ((x * e + f) * e) := by rw [h0]
      _ = e := by rw [← mul_assoc, hwu, one_mul]
  have hxe : x * e = e * x * e + f * x * e := by rw [← add_mul, ← add_mul, hef, one_mul]
  have hwfxe : w * (f * x * e) = f * x * e := by rw [← mul_assoc, ← mul_assoc, hwf]
  have hweaxe : w * (e * x * e) = e - f * x * e := by
    have h0 : w * (e * x * e) + w * (f * x * e) = e := by rw [← mul_add, ← hxe, hwxe]
    rw [← hwfxe]
    exact eq_sub_of_add_eq h0
  obtain ⟨s, hs_def⟩ : ∃ s : R, s = -(f * w * e) := ⟨_, rfl⟩
  have hsa : s * (e * x * e) = f * x * e := by
    have h1' : f * w * e * (e * x * e) = f * (w * (e * x * e)) := by simp only [mul_assoc, he2]
    rw [hs_def, neg_mul, h1', hweaxe, mul_sub, hfe0, zero_sub, neg_neg]
    simp only [mul_assoc, hf2]
  have haa' : e * x * e * (e * w * e) = e := by
    have h := congrArg (fun z => e * z * e) huw
    simp only [add_mul, mul_add, mul_assoc, hef2, add_zero, one_mul, mul_one, hee] at h
    simp only [mul_assoc, he2]
    exact h
  have hσ3 : ∀ a b d : R, σ (a * b * d) = σ d * σ b * σ a := by
    intro a b d
    rw [hmul (a * b) d, hmul a b, ← mul_assoc]
  have hσc : σ (f * x * e) = f * σ x * e := by rw [hσ3, hse, hsf]
  have hσa : σ (e * x * e) = f * σ x * f := by rw [hσ3, hse]
  have hrel : σ (f * x * e) * (e * x * e) + σ (e * x * e) * (f * x * e) = 0 := by
    rw [hσc, hσa]
    simp only [mul_assoc, he2, hf2]
    rw [← mul_add, ← mul_add, ← add_mul, hef, one_mul, ← mul_assoc (σ x) x e, hux, one_mul, hfe0]
  have hes : e * s = 0 := by
    rw [hs_def, mul_neg]
    simp only [mul_assoc, hef2, neg_zero]
  have hsf : s * f = 0 := by
    rw [hs_def, neg_mul]
    simp only [mul_assoc, hef0, mul_zero, neg_zero]
  have hse' : s * e = s := by simp only [hs_def, neg_mul, mul_assoc, hee]
  have hfs : f * s = s := by simp only [hs_def, mul_neg, ← mul_assoc, hff]
  have hs_eq : s = f * x * e * (e * w * e) := by
    calc s = s * e := hse'.symm
      _ = s * (e * x * e * (e * w * e)) := by rw [haa']
      _ = f * x * e * (e * w * e) := by rw [← mul_assoc, hsa]
  have hσce : σ (f * x * e) * e = σ (f * x * e) := by
    rw [hσc]
    simp only [mul_assoc, hee]
  have hσc2 : σ (f * x * e) = -(σ (e * x * e) * s) := by
    calc σ (f * x * e) = σ (f * x * e) * e := hσce.symm
      _ = σ (f * x * e) * (e * x * e * (e * w * e)) := by rw [haa']
      _ = (σ (f * x * e) * (e * x * e)) * (e * w * e) := (mul_assoc _ _ _).symm
      _ = (-(σ (e * x * e) * (f * x * e))) * (e * w * e) := by rw [eq_neg_of_add_eq_zero_left hrel]
      _ = -(σ (e * x * e) * s) := by rw [hs_eq, neg_mul, mul_assoc (σ (e * x * e))]
  have hσs : σ s = -s := by
    calc σ s = σ (f * x * e * (e * w * e)) := by rw [← hs_eq]
      _ = σ (e * w * e) * σ (f * x * e) := hmul _ _
      _ = -(σ (e * w * e) * σ (e * x * e) * s) := by rw [hσc2, mul_neg, ← mul_assoc]
      _ = -(σ (e * x * e * (e * w * e)) * s) := by rw [hmul (e * x * e) (e * w * e)]
      _ = -s := by rw [haa', hse, hfs]
  obtain ⟨n, hn, hln⟩ := hlow s hes hsf hσs
  have hss : s * s = 0 := by
    calc s * s = (s * e) * (f * s) := by rw [hse', hfs]
      _ = s * (e * f) * s := by simp only [mul_assoc]
      _ = 0 := by rw [hef0, mul_zero, zero_mul]
  have hninv : φ n⁻¹ = 1 - s := by
    have h0 : (1 + s) * φ n⁻¹ = 1 := by rw [← hn, ← map_mul, mul_inv_cancel, map_one]
    have h1s : (1 - s) * (1 + s) = 1 := by
      calc (1 - s) * (1 + s) = 1 - s * s := by noncomm_ring
        _ = 1 := by rw [hss, sub_zero]
    calc φ n⁻¹ = ((1 - s) * (1 + s)) * φ n⁻¹ := by rw [h1s, one_mul]
      _ = 1 - s := by rw [mul_assoc, h0, mul_one]
  have hsfxe : s * (f * x * e) = 0 := by rw [← mul_assoc, ← mul_assoc, hsf, zero_mul, zero_mul]
  have hsxe : s * (x * e) = f * x * e := by rw [hxe, mul_add, hsa, hsfxe, add_zero]
  have hpar : f * φ (n⁻¹ * g) * e = 0 := by
    rw [map_mul, hninv, ← hx]
    calc f * ((1 - s) * x) * e = f * x * e - f * (s * (x * e)) := by noncomm_ring
      _ = 0 := by rw [← mul_assoc f s, hfs, hsxe, sub_self]
  calc lam g = lam (n * (n⁻¹ * g)) := by rw [mul_inv_cancel_left]
    _ = 1 := by rw [map_mul, hln, hP _ hpar, one_mul]

end Abstract

theorem finite_nonunit {F : Type} [Field F] {E : Type} [CommRing E] [Algebra F E] [Module.Finite F E]
    (p : Polynomial E) (τ : E) (h : IsUnit (p.eval τ)) : {t : F | ¬ IsUnit (p.eval (algebraMap F E t))}.Finite := by
  classical
  haveI : IsArtinianRing E := IsArtinianRing.of_finite F E
  have hmax : {m : Ideal E | m.IsMaximal}.Finite := IsArtinianRing.setOf_isMaximal_finite E
  have key : ∀ m : Ideal E, m.IsMaximal → {t : F | p.eval (algebraMap F E t) ∈ m}.Finite := by
    intro m hm
    haveI := hm
    letI : Field (E ⧸ m) := Ideal.Quotient.field m
    obtain ⟨q, hq⟩ : ∃ q : Polynomial (E ⧸ m), q = p.map (Ideal.Quotient.mk m) := ⟨_, rfl⟩
    have hev : ∀ z : E, q.eval (Ideal.Quotient.mk m z) = Ideal.Quotient.mk m (p.eval z) := by
      intro z
      rw [hq, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    have hq0 : q ≠ 0 := by
      intro h0
      have h1 := hev τ
      rw [h0, Polynomial.eval_zero] at h1
      exact (h.map (Ideal.Quotient.mk m)).ne_zero h1.symm
    have hinj : Function.Injective ((Ideal.Quotient.mk m).comp (algebraMap F E)) := RingHom.injective _
    refine ((q.roots.toFinset.finite_toSet).preimage hinj.injOn).subset ?_
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, RingHom.comp_apply]
    rw [Polynomial.mem_roots hq0, Polynomial.IsRoot, hev]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ht
  refine (hmax.biUnion fun m hm => key m hm).subset ?_
  intro t ht
  obtain ⟨m, hm, htm⟩ := exists_max_ideal_of_mem_nonunits ht
  exact Set.mem_biUnion hm htm

theorem finite_nonunit_matrix {F : Type} [Field F] {E : Type} [CommRing E] [Algebra F E] [Module.Finite F E]
    {β : Type} [Fintype β] [DecidableEq β] (A B D : Matrix β β E) (τ : E) (h : IsUnit (A + τ • B + (τ * τ) • D)) :
    {t : F | ¬ IsUnit (A + algebraMap F E t • B + (algebraMap F E t * algebraMap F E t) • D)}.Finite := by
  classical
  set P : Matrix β β (Polynomial E) := A.map Polynomial.C + (Polynomial.X : Polynomial E) • B.map Polynomial.C
      + ((Polynomial.X : Polynomial E) * Polynomial.X) • D.map Polynomial.C with hP
  have hev : ∀ z : E, P.det.eval z = (A + z • B + (z * z) • D).det := by
    intro z
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [hP, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply] <;> ring
  refine (finite_nonunit (F := F) P.det τ ?_).subset ?_
  · rw [hev]
    exact (Matrix.isUnit_iff_isUnit_det _).mp h
  · intro t ht
    simp only [Set.mem_setOf_eq] at ht ⊢
    rw [hev]
    exact fun hu => ht ((Matrix.isUnit_iff_isUnit_det _).mpr hu)

theorem triv_of_cell {F : Type} [Field F] [Infinite F] {E : Type} [CommRing E] [Algebra F E] [Module.Finite F E]
    {β : Type} [Fintype β] [DecidableEq β] {c : E →ₐ[F] E} {ξ : E} (hξ : IsUnit ξ) (h2 : IsUnit (2 : E))
    (hc : c ξ = -ξ) {σ : Matrix β β E →+ Matrix β β E} {G : Type} [Group G] {φ : G →* Matrix β β E}
    {e f : Matrix β β E} (hsm : ∀ (a : E) x, σ (a • x) = c a • σ x) (hmul : ∀ x y, σ (x * y) = σ y * σ x) (h1 : σ 1 = 1)
    (hu : ∀ g, σ (φ g) * φ g = 1) (hsurj : ∀ x, σ x * x = 1 → ∃ g, φ g = x)
    (hef : e + f = 1) (hee : e * e = e) (hff : f * f = f) (hef0 : e * f = 0) (hfe0 : f * e = 0) (lam : G →* ℂˣ)
    (hcell : ∀ g, IsUnit (φ g * e + f) → lam g = 1) (g : G) : lam g = 1 := by
  classical
  have hinvmat : ∀ A B : Matrix β β E, A * B = 1 → B * A = 1 := fun A B h => mul_eq_one_comm.mp h
  have hunit_of : ∀ A B : Matrix β β E, A * B = 1 → IsUnit A :=
    fun A B h => ⟨⟨A, B, h, hinvmat A B h⟩, rfl⟩
  have hsmul_unit : ∀ (a : E) (A : Matrix β β E), IsUnit a → IsUnit A → IsUnit (a • A) := by
    intro a A ha hA
    rw [Algebra.smul_def]
    exact (ha.map (algebraMap E (Matrix β β E))).mul hA
  have htwo : ∀ A : Matrix β β E, IsUnit A → IsUnit (A + A) := by
    intro A hA
    rw [← two_smul E A]
    exact hsmul_unit 2 A h2 hA
  have fin1 : ∀ (A B : Matrix β β E) (τ : E), IsUnit (A + τ • B) →
      {t : F | ¬ IsUnit (A + algebraMap F E t • B)}.Finite := by
    intro A B τ h
    have h' : IsUnit (A + τ • B + (τ * τ) • (0 : Matrix β β E)) := by rwa [smul_zero, add_zero]
    have hfin := finite_nonunit_matrix (F := F) A B 0 τ h'
    simpa only [smul_zero, add_zero] using hfin
  have finE : ∀ (a b : E) (τ : E), IsUnit (a + b * τ) →
      {t : F | ¬ IsUnit (a + b * algebraMap F E t)}.Finite := by
    intro a b τ h
    have hfin := finite_nonunit (F := F) (Polynomial.C a + Polynomial.C b * Polynomial.X) τ (by simpa using h)
    simpa using hfin
  have hcF : ∀ t : F, c (algebraMap F E t) = algebraMap F E t := fun t => c.commutes t
  have hσF : ∀ (t : F) (y : Matrix β β E), σ (algebraMap F E t • y) = algebraMap F E t • σ y :=
    fun t y => by rw [hsm, hcF]
  have main : ∀ g : G, IsUnit (φ g + 1) → lam g = 1 := by
    intro g hg1
    obtain ⟨x, hx⟩ : ∃ x, x = φ g := ⟨_, rfl⟩
    rw [← hx] at hg1
    have hσx : σ x * x = 1 := by rw [hx]; exact hu g
    have hxσ : x * σ x = 1 := hinvmat _ _ hσx
    have hxu : IsUnit x := hunit_of _ _ hxσ
    have hN := fin1 (x + 1) (x - 1) 0 (by rwa [zero_smul, add_zero])
    have hD := fin1 (x + 1) (-(x - 1)) 0 (by rwa [zero_smul, add_zero])
    have hI := fin1 (x + 1) ((x - 1) * (e - f)) 0 (by rwa [zero_smul, add_zero])
    have hII := fin1 ((x + 1) * (x * e + f)) ((x - 1) * (f - x * e)) 1 (by
      rw [one_smul]
      have h0 : (x + 1) * (x * e + f) + (x - 1) * (f - x * e) = x * (e + f) + x * (e + f) := by
        noncomm_ring
      rw [h0, hef, mul_one]
      exact htwo x hxu)
    obtain ⟨s, hs⟩ := ((hN.union hD).union (hI.union hII)).infinite_compl.nonempty
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hs
    obtain ⟨⟨hNs, hDs⟩, hIs, hIIs⟩ := hs
    obtain ⟨N, hNdef⟩ : ∃ N : Matrix β β E, N = (x + 1) + algebraMap F E s • (x - 1) := ⟨_, rfl⟩
    obtain ⟨D, hDdef⟩ : ∃ D : Matrix β β E, D = (x + 1) + algebraMap F E s • (-(x - 1)) := ⟨_, rfl⟩
    rw [← hNdef] at hNs
    rw [← hDdef] at hDs
    obtain ⟨Ni, hNNi⟩ := hNs.exists_right_inv
    obtain ⟨Di, hDDi⟩ := hDs.exists_right_inv
    have hNiN : Ni * N = 1 := hinvmat _ _ hNNi
    have hDiD : Di * D = 1 := hinvmat _ _ hDDi
    have hc0 : Commute (x + 1) (x - 1) := by
      show (x + 1) * (x - 1) = (x - 1) * (x + 1)
      noncomm_ring
    have hcND : Commute N D := by
      rw [hNdef, hDdef]
      exact Commute.add_left (Commute.add_right (Commute.refl _) (hc0.neg_right.smul_right _))
        (Commute.add_right (hc0.symm.smul_left _) (((Commute.refl (x - 1)).neg_right.smul_left _).smul_right _))
    have hσN : σ N = σ x * D := by
      rw [hNdef, hDdef, map_add, map_add, h1, hσF, map_sub, h1, mul_add, mul_add, mul_one, hσx,
        mul_smul_comm, mul_neg, mul_sub, mul_one, hσx, neg_sub, add_comm 1 (σ x)]
    have hσD : σ D = σ x * N := by
      rw [hNdef, hDdef, map_add, map_add, h1, hσF, map_neg, map_sub, h1, mul_add, mul_add, mul_one, hσx,
        mul_smul_comm, mul_sub, mul_one, hσx, neg_sub, add_comm 1 (σ x)]
    have hA : σ (N * Di) * (N * Di) = 1 := by
      calc σ (N * Di) * (N * Di) = σ Di * (σ x * ((D * N) * Di)) := by
            rw [hmul, hσN]; simp only [mul_assoc]
        _ = σ Di * (σ x * N) := by rw [← hcND.eq, mul_assoc N D Di, hDDi, mul_one]
        _ = σ Di * σ D := by rw [hσD]
        _ = 1 := by rw [← hmul, hDDi, h1]
    obtain ⟨ga, hga⟩ := hsurj _ hA
    have hDiN : Di * N = N * Di := by
      calc Di * N = Di * N * (D * Di) := by rw [hDDi, mul_one]
        _ = Di * (N * D) * Di := by simp only [mul_assoc]
        _ = Di * (D * N) * Di := by rw [hcND.eq]
        _ = N * Di := by rw [← mul_assoc Di D N, hDiD, one_mul]
    have hNiD : Ni * D = D * Ni := by
      calc Ni * D = Ni * D * (N * Ni) := by rw [hNNi, mul_one]
        _ = Ni * (D * N) * Ni := by simp only [mul_assoc]
        _ = Ni * (N * D) * Ni := by rw [hcND.eq]
        _ = D * Ni := by rw [← mul_assoc Ni N D, hNiN, one_mul]
    have hNeDf : N * e + D * f = (x + 1) + algebraMap F E s • ((x - 1) * (e - f)) := by
      have h0 : (x + 1) * e + (x + 1) * f = x + 1 := by rw [← mul_add, hef, mul_one]
      have h3 : N * e + D * f = ((x + 1) * e + (x + 1) * f) + algebraMap F E s • ((x - 1) * (e - f)) := by
        rw [hNdef, hDdef]
        simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, neg_mul, mul_neg, smul_sub, smul_add, smul_neg, one_mul, mul_one, mul_assoc]
        abel
      rw [h3, h0]
    have hla : lam ga = 1 := by
      apply hcell
      have h0 : φ ga * e + f = Di * (N * e + D * f) := by
        rw [hga, mul_add, ← mul_assoc Di N e, ← mul_assoc Di D f, hDiD, one_mul, hDiN]
      rw [h0, hNeDf]
      exact (hunit_of _ _ hDiD).mul hIs
    have hgainv : φ ga⁻¹ = D * Ni := by
      have h0 : φ ga * φ ga⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      have h3 : D * Ni * (N * Di) = 1 := by
        calc D * Ni * (N * Di) = D * (Ni * N) * Di := by simp only [mul_assoc]
          _ = 1 := by rw [hNiN, mul_one, hDDi]
      calc φ ga⁻¹ = D * Ni * (N * Di) * φ ga⁻¹ := by rw [h3, one_mul]
        _ = D * Ni := by rw [mul_assoc (D * Ni) (N * Di) (φ ga⁻¹), ← hga, h0, mul_one]
    have hDxeNf : D * x * e + N * f = (x + 1) * (x * e + f) + algebraMap F E s • ((x - 1) * (f - x * e)) := by
      rw [hNdef, hDdef]
      simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, neg_mul, mul_neg, smul_sub, smul_add, smul_neg, one_mul, mul_one, mul_assoc]
      abel
    have hlb : lam (ga⁻¹ * g) = 1 := by
      apply hcell
      have h0 : φ (ga⁻¹ * g) * e + f = Ni * (D * x * e + N * f) := by
        rw [map_mul, hgainv, ← hx, mul_add, ← mul_assoc Ni N f, hNiN, one_mul, ← hNiD]
        simp only [mul_assoc]
      rw [h0, hDxeNf]
      exact (hunit_of _ _ hNiN).mul hIIs
    calc lam g = lam (ga * (ga⁻¹ * g)) := by rw [mul_inv_cancel_left]
      _ = 1 := by rw [map_mul, hla, hlb, one_mul]
  obtain ⟨x, hx⟩ : ∃ x, x = φ g := ⟨_, rfl⟩
  have hσx : σ x * x = 1 := by rw [hx]; exact hu g
  have hxu : IsUnit x := hunit_of _ _ (hinvmat _ _ hσx)
  obtain ⟨ξi, hξi⟩ := hξ.exists_right_inv
  have S1 := fin1 (x + 1) (ξ • (x - 1)) ξi (by
    rw [smul_smul, mul_comm, hξi, one_smul, show x + 1 + (x - 1) = x + x by abel]
    exact htwo x hxu)
  have S2 := finE 1 (-ξ) 0 (by simp)
  have S3 := finE 1 ξ 0 (by simp)
  obtain ⟨t, ht⟩ := ((S1.union S2).union S3).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at ht
  obtain ⟨⟨ht1, ht2⟩, ht3⟩ := ht
  obtain ⟨w, hw⟩ : ∃ w : E, w = 1 + -ξ * algebraMap F E t := ⟨_, rfl⟩
  obtain ⟨cw, hcw⟩ : ∃ cw : E, cw = 1 + ξ * algebraMap F E t := ⟨_, rfl⟩
  rw [← hw] at ht2
  rw [← hcw] at ht3
  have hcw' : c w = cw := by rw [hw, hcw, map_add, map_one, map_mul, map_neg, hc, neg_neg, hcF]
  obtain ⟨wi, hwwi⟩ := ht2.exists_right_inv
  obtain ⟨z, hz⟩ : ∃ z : E, z = cw * wi := ⟨_, rfl⟩
  have hcwi : c wi * cw = 1 := by rw [← hcw', ← map_mul, mul_comm, hwwi, map_one]
  have hcz : c z * z = 1 := by
    have hccw : c cw = w := by rw [hw, hcw, map_add, map_one, map_mul, hc, hcF]
    rw [hz, map_mul, hccw]
    calc w * c wi * (cw * wi) = (c wi * cw) * (w * wi) := by ring
      _ = 1 := by rw [hcwi, hwwi, one_mul]
  have hzc : z * c z = 1 := by rw [mul_comm, hcz]
  have hzs : σ (z • (1 : Matrix β β E)) * (z • 1) = 1 := by
    rw [hsm, h1, smul_mul_smul_comm, mul_one, hcz, one_smul]
  obtain ⟨gz, hgz⟩ := hsurj _ hzs
  have hlz : lam gz = 1 := by
    apply hcell
    rw [hgz, smul_mul_assoc, one_mul]
    apply hunit_of _ (c z • e + f)
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, hee, hff, hef0, hfe0,
      smul_zero, add_zero, zero_add, hzc, hcz, one_smul, hef]
  have hlg' : lam (g * gz) = 1 := by
    apply main
    rw [map_mul, ← hx, hgz, mul_smul_comm, mul_one]
    have hwz : w * z = cw := by
      rw [hz]
      calc w * (cw * wi) = cw * (w * wi) := by ring
        _ = cw := by rw [hwwi, mul_one]
    have h0 : w • (z • x + 1) = (x + 1) + algebraMap F E t • (ξ • (x - 1)) := by
      rw [smul_add, smul_smul, hwz, hw, hcw]
      simp only [add_smul, one_smul, mul_smul, smul_sub, neg_mul, neg_smul, smul_comm ξ (algebraMap F E t)]
      abel
    have h1' : z • x + 1 = wi • (w • (z • x + 1)) := by
      rw [smul_smul, mul_comm wi w, hwwi, one_smul]
    rw [h1', h0]
    exact hsmul_unit wi _ (⟨⟨wi, w, by rw [mul_comm]; exact hwwi, hwwi⟩, rfl⟩ : IsUnit wi) ht1
  calc lam g = lam (g * gz) * (lam gz)⁻¹ := by rw [map_mul, mul_inv_cancel_right]
    _ = 1 := by rw [hlg', hlz, inv_one, one_mul]

theorem char_trivial : ∀ (F : Type) [Field F] [CharZero F] [Invertible (2 : F)] (E : Type) [CommRing E] [Algebra F E] (c : E →ₐ[F] E) (ξ : E) (β ν : Type) [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] (J : Matrix β β E) (Cy : Matrix β ν E), IsQuad c ξ → IsHerm c J → IsLagr c J Cy → ∀ lam : UG c J →* ℂˣ, (∀ (p : UG c J) (t : GL ν E), ((p : GL β E) : Matrix β β E) * Cy = Cy * (t : Matrix ν ν E) → lam p = 1) → lam = 1 := by
  intro F _ _ _ E _ _ c ξ β ν _ _ _ _ J Cy hQ hH hL lam hpar
  classical
  obtain ⟨b, -, -⟩ := hQ.basis
  haveI : Module.Finite F E := Module.Finite.of_basis b
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  obtain ⟨hJh, hJdet⟩ := hH
  obtain ⟨hCy, Cx, M, hCx, hPM, hMP⟩ := hL
  obtain ⟨Ji, hJi⟩ : ∃ Ji : Matrix β β E, Ji = J⁻¹ := ⟨_, rfl⟩
  have hJJi : J * Ji = 1 := by rw [hJi]; exact Matrix.mul_nonsing_inv J hJdet
  have hJiJ : Ji * J = 1 := by rw [hJi]; exact Matrix.nonsing_inv_mul J hJdet
  let cm : Matrix β β E →+* Matrix β β E := (c.toRingHom).mapMatrix
  have hcm : ∀ x : Matrix β β E, cm x = x.map c := fun x => rfl
  let σ : Matrix β β E →+ Matrix β β E := AddMonoidHom.mk' (fun x => (J * cm x * Ji)ᵀ) (by
    intro x y
    simp only [map_add, Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add])
  have hσ : ∀ x, σ x = (J * cm x * Ji)ᵀ := fun x => rfl
  have hcm_smul : ∀ (a : E) (x : Matrix β β E), cm (a • x) = c a • cm x := by
    intro a x
    ext i j
    simp [hcm, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have hsm : ∀ (a : E) (x : Matrix β β E), σ (a • x) = c a • σ x := by
    intro a x
    rw [hσ, hσ, hcm_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul]
  have hmul : ∀ x y : Matrix β β E, σ (x * y) = σ y * σ x := by
    intro x y
    rw [hσ, hσ, hσ, map_mul, ← Matrix.transpose_mul]
    congr 1
    calc J * (cm x * cm y) * Ji = J * cm x * (Ji * J) * cm y * Ji := by
          rw [hJiJ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = J * cm x * Ji * (J * cm y * Ji) := by simp only [Matrix.mul_assoc]
  have h1 : σ 1 = 1 := by rw [hσ, map_one, Matrix.mul_one, hJJi, Matrix.transpose_one]
  have hkey : ∀ x : Matrix β β E, σ x * x = Jiᵀ * (xᵀ * J * x.map c)ᵀ := by
    intro x
    rw [hσ, hcm]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hJt : Jᵀ * Jiᵀ = 1 := by rw [← Matrix.transpose_mul, hJiJ, Matrix.transpose_one]
  have hJt' : Jiᵀ * Jᵀ = 1 := by rw [← Matrix.transpose_mul, hJJi, Matrix.transpose_one]
  have hunitary : ∀ x : Matrix β β E, σ x * x = 1 ↔ xᵀ * J * x.map c = J := by
    intro x
    rw [hkey]
    constructor
    · intro h
      have h' : (xᵀ * J * x.map c)ᵀ = Jᵀ := by
        calc (xᵀ * J * x.map c)ᵀ = Jᵀ * (Jiᵀ * (xᵀ * J * x.map c)ᵀ) := by
              rw [← Matrix.mul_assoc, hJt, Matrix.one_mul]
          _ = Jᵀ := by rw [h, Matrix.mul_one]
      exact Matrix.transpose_inj.mp h'
    · intro h
      rw [h, hJt']
  let φ : ↥(UG c J) →* Matrix β β E := (Units.coeHom (Matrix β β E)).comp (UG c J).subtype
  have hφ : ∀ g : ↥(UG c J), φ g = ((g : GL β E) : Matrix β β E) := fun g => rfl
  have hu : ∀ g : ↥(UG c J), σ (φ g) * φ g = 1 := fun g => (hunitary _).mpr g.2
  have hsurj : ∀ x, σ x * x = 1 → ∃ g, φ g = x := by
    intro x hx
    have hxσ : x * σ x = 1 := mul_eq_one_comm.mp hx
    exact ⟨⟨⟨x, σ x, hxσ, hx⟩, (hunitary x).mp hx⟩, rfl⟩
  have hinj : Function.Injective φ := fun a b h => Subtype.ext (Units.ext h)
  obtain ⟨Mt, hMt⟩ : ∃ Mt, Mt = M.toRows₁ := ⟨_, rfl⟩
  obtain ⟨Mb, hMb⟩ : ∃ Mb, Mb = M.toRows₂ := ⟨_, rfl⟩
  have hM : M = Matrix.fromRows Mt Mb := by rw [hMt, hMb, Matrix.fromRows_toRows]
  have hPM' : Cy * Mt + Cx * Mb = 1 := by rw [hM, Matrix.fromCols_mul_fromRows] at hPM; exact hPM
  rw [hM, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hMP
  obtain ⟨hMtCy, hMtCx, hMbCy, hMbCx⟩ := hMP
  obtain ⟨e, he⟩ : ∃ e : Matrix β β E, e = Cy * Mt := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : Matrix β β E, f = Cx * Mb := ⟨_, rfl⟩
  have hef : e + f = 1 := by rw [he, hf, hPM']
  have hee : e * e = e := by
    rw [he, Matrix.mul_assoc Cy Mt (Cy * Mt), ← Matrix.mul_assoc Mt Cy Mt, hMtCy, Matrix.one_mul]
  have hff : f * f = f := by
    rw [hf, Matrix.mul_assoc Cx Mb (Cx * Mb), ← Matrix.mul_assoc Mb Cx Mb, hMbCx, Matrix.one_mul]
  have hef0 : e * f = 0 := by
    rw [he, hf, Matrix.mul_assoc Cy Mt (Cx * Mb), ← Matrix.mul_assoc Mt Cx Mb, hMtCx, Matrix.zero_mul,
      Matrix.mul_zero]
  have hfe0 : f * e = 0 := by
    rw [he, hf, Matrix.mul_assoc Cx Mb (Cy * Mt), ← Matrix.mul_assoc Mb Cy Mt, hMbCy, Matrix.zero_mul,
      Matrix.mul_zero]
  have hefc : Cy.map c * Mt.map c + Cx.map c * Mb.map c = 1 := by
    have h := congrArg cm hPM'
    rw [map_add, map_one, hcm, hcm, Matrix.map_mul, Matrix.map_mul] at h
    exact h
  have heft : Mtᵀ * Cyᵀ + Mbᵀ * Cxᵀ = 1 := by
    have h := congrArg Matrix.transpose hPM'
    rwa [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_one] at h
  have K : J * (Cx.map c * Mb.map c) = Mtᵀ * Cyᵀ * J := by
    have A1 : Mtᵀ * Cyᵀ * J = Mtᵀ * Cyᵀ * J * Cx.map c * Mb.map c := by
      calc Mtᵀ * Cyᵀ * J = Mtᵀ * Cyᵀ * J * (Cy.map c * Mt.map c + Cx.map c * Mb.map c) := by
            rw [hefc, Matrix.mul_one]
        _ = Mtᵀ * (Cyᵀ * J * Cy.map c) * Mt.map c + Mtᵀ * Cyᵀ * J * Cx.map c * Mb.map c := by
            simp only [Matrix.mul_add, Matrix.mul_assoc]
        _ = Mtᵀ * Cyᵀ * J * Cx.map c * Mb.map c := by
            rw [hCy, Matrix.mul_zero, Matrix.zero_mul, zero_add]
    have A2 : J * (Cx.map c * Mb.map c) = Mtᵀ * Cyᵀ * J * Cx.map c * Mb.map c := by
      calc J * (Cx.map c * Mb.map c) = (Mtᵀ * Cyᵀ + Mbᵀ * Cxᵀ) * J * (Cx.map c * Mb.map c) := by
            rw [heft, Matrix.one_mul]
        _ = Mtᵀ * Cyᵀ * J * Cx.map c * Mb.map c + Mbᵀ * (Cxᵀ * J * Cx.map c) * Mb.map c := by
            simp only [Matrix.add_mul, Matrix.mul_assoc]
        _ = Mtᵀ * Cyᵀ * J * Cx.map c * Mb.map c := by
            rw [hCx, Matrix.mul_zero, Matrix.zero_mul, add_zero]
    rw [A2, ← A1]
  have hσe : σ e = f := by
    have B1 : J * (Cy.map c * Mt.map c) = Mbᵀ * Cxᵀ * J := by
      have h1' : Cy.map c * Mt.map c = 1 - Cx.map c * Mb.map c := eq_sub_of_add_eq hefc
      have h2' : Mbᵀ * Cxᵀ = 1 - Mtᵀ * Cyᵀ := eq_sub_of_add_eq' heft
      rw [h1', Matrix.mul_sub, Matrix.mul_one, K, h2', Matrix.sub_mul, Matrix.one_mul]
    rw [he, hf, hσ, hcm, Matrix.map_mul, B1, Matrix.mul_assoc (Mbᵀ * Cxᵀ) J Ji, hJJi, Matrix.mul_one,
      Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
  have hσf : σ f = e := by
    rw [he, hf, hσ, hcm, Matrix.map_mul, K, Matrix.mul_assoc (Mtᵀ * Cyᵀ) J Ji, hJJi, Matrix.mul_one,
      Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
  have hP : ∀ g : ↥(UG c J), f * φ g * e = 0 → lam g = 1 := by
    intro g hg
    obtain ⟨x, hx⟩ : ∃ x, x = φ g := ⟨_, rfl⟩
    rw [← hx] at hg
    have hxe : x * e = e * x * e := by
      calc x * e = (e + f) * x * e := by rw [hef, Matrix.one_mul]
        _ = e * x * e := by rw [Matrix.add_mul, Matrix.add_mul, hg, add_zero]
    have heCy : e * Cy = Cy := by rw [he, Matrix.mul_assoc, hMtCy, Matrix.mul_one]
    have hxCy : x * Cy = Cy * (Mt * x * Cy) := by
      calc x * Cy = x * (e * Cy) := by rw [heCy]
        _ = e * x * e * Cy := by rw [← Matrix.mul_assoc, hxe]
        _ = Cy * (Mt * x * Cy) := by
            rw [Matrix.mul_assoc (e * x) e Cy, heCy, he]
            simp only [Matrix.mul_assoc]
    have hexCy : e * (x * Cy) = x * Cy := by
      rw [hxCy, ← Matrix.mul_assoc, heCy]
    obtain ⟨xi, hxi⟩ : ∃ xi, xi = φ g⁻¹ := ⟨_, rfl⟩
    have hxxi : xi * x = 1 := by rw [hxi, hx, ← map_mul, inv_mul_cancel, map_one]
    have ht't : Mt * xi * Cy * (Mt * x * Cy) = 1 := by
      calc Mt * xi * Cy * (Mt * x * Cy) = Mt * xi * ((Cy * Mt) * (x * Cy)) := by
            simp only [Matrix.mul_assoc]
        _ = Mt * xi * (x * Cy) := by rw [← he, hexCy]
        _ = Mt * (xi * x) * Cy := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hxxi, Matrix.mul_one, hMtCy]
    have htt' : Mt * x * Cy * (Mt * xi * Cy) = 1 := mul_eq_one_comm.mp ht't
    apply hpar g ⟨Mt * x * Cy, Mt * xi * Cy, htt', ht't⟩
    show φ g * Cy = Cy * (Mt * x * Cy)
    rw [← hx]
    exact hxCy
  have hi2 : (2 : E) * algebraMap F E (⅟2) = 1 := by
    rw [← map_ofNat (algebraMap F E) 2, ← map_mul, mul_invOf_self, map_one]
  have h3F : (3 : F) ≠ 0 := three_ne_zero
  have hi3 : (3 : E) * algebraMap F E (3⁻¹) = 1 := by
    rw [← map_ofNat (algebraMap F E) 3, ← map_mul, mul_inv_cancel₀ h3F, map_one]
  have c2 : c 2 = 2 := map_ofNat c 2
  have ci2 : c (algebraMap F E (⅟2)) = algebraMap F E (⅟2) := c.commutes _
  have ci3 : c (algebraMap F E (3⁻¹)) = algebraMap F E (3⁻¹) := c.commutes _
  have hlow : ∀ s, e * s = 0 → s * f = 0 → σ s = -s → ∃ n, φ n = 1 + s ∧ lam n = 1 :=
    fun s hes hsf0 hs => lower_triv (c := ⇑c) (σ := σ) (φ := φ) hsm h1 hi2 hi3 c2 ci2 ci3 hinj hsurj
      hef hee hff hef0 hfe0 hσe hσf lam s hes hsf0 hs
  have hcell : ∀ g, IsUnit (φ g * e + f) → lam g = 1 :=
    fun g hg => cell_triv (σ := σ) (φ := φ) hmul h1 hu hef hee hff hef0 hfe0 hσe hσf lam hlow hP g hg
  have h2E : IsUnit (2 : E) := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (isUnit_of_invertible (2 : F)).map _
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.one_apply]
  exact triv_of_cell (F := F) (c := c) hQ.unit h2E hQ.anti hsm hmul h1 hu hsurj hef hee hff hef0 hfe0 lam hcell g

end GlobalTheory.CompanionTheory.SiegelChar

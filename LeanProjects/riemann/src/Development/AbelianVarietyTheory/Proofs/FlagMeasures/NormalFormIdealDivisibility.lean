import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameBlockAppend
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow

noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.PosIso

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] in

theorem exists_section (M : Submodule (𝓞 K) V) (hM : M.FG) (φ : V →ₗ[K] K) (h0 : ∃ y ∈ M, φ y ≠ 0) :
    ∃ v ∈ Submodule.span K (M : Set V), φ v = 1 ∧ ∀ y ∈ M, φ y • v ∈ M := by
  let J : Submodule (𝓞 K) K := M.map (φ.restrictScalars (𝓞 K))
  have hJ : J.FG := hM.map _
  let I : FractionalIdeal (𝓞 K)⁰ K := ⟨J, FractionalIdeal.isFractional_of_fg hJ⟩
  have hI : I ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := h0
    intro h
    have : φ y ∈ I := ⟨y, hy, rfl⟩
    rw [h] at this
    exact hy0 (by simpa using this)
  have h1 : (1 : K) ∈ ((I * I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _
  rw [FractionalIdeal.coe_mul] at h1
  have key : ∀ w ∈ (I : Submodule (𝓞 K) K) * ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
      ∃ v ∈ Submodule.span K (M : Set V), φ v = w ∧ ∀ y ∈ M, φ y • v ∈ M := by
    intro w hw
    refine Submodule.mul_induction_on hw ?_ ?_
    · rintro _ ⟨y0, hy0, rfl⟩ β hβ
      refine ⟨β • y0, Submodule.smul_mem _ _ (Submodule.subset_span hy0), by simp [mul_comm], fun y hy => ?_⟩
      have hm : φ y * β ∈ (I * I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) :=
        FractionalIdeal.mul_mem_mul (show φ y ∈ I from ⟨y, hy, rfl⟩) hβ
      rw [mul_inv_cancel₀ hI, FractionalIdeal.mem_one_iff] at hm
      obtain ⟨o, ho⟩ := hm
      rw [smul_smul, ← ho, algebraMap_smul]
      exact M.smul_mem _ hy0
    · rintro _ _ ⟨v, hv, rfl, h⟩ ⟨v', hv', rfl, h'⟩
      exact ⟨v + v', add_mem hv hv', by simp, fun y hy => by rw [smul_add]; exact add_mem (h y hy) (h' y hy)⟩
  exact key 1 h1

omit [NumberField K] in

theorem det_smul_mem (H : HermSpace K V) (Λ : Submodule (𝓞 K) V) {j : ℕ} (x x' : Fin j → V)
    (hx : ∀ a, x a ∈ Λ) (hG : ∀ a b, H.B (x a) (x' b) ∈ (1 : Submodule (𝓞 K) K)) (p : Fin j → K)
    (hp : ∀ b, H.B (∑ a, p a • x a) (x' b) ∈ (1 : Submodule (𝓞 K) K)) :
    (Matrix.of fun a b => H.B (x a) (x' b)).det • (∑ a, p a • x a) ∈ Λ := by
  choose G0 hG0 using fun a b => Submodule.mem_one.1 (hG a b)
  choose η hη using fun b => Submodule.mem_one.1 (hp b)
  set G : Matrix (Fin j) (Fin j) K := Matrix.of fun a b => H.B (x a) (x' b) with hGdef
  have hGm : G = (algebraMap (𝓞 K) K).mapMatrix (Matrix.of G0) := by
    ext a b; simp [hGdef, ← hG0]
  have h1 : Matrix.vecMul p G = fun b => algebraMap (𝓞 K) K (η b) := by
    funext b
    rw [hη]
    simp [Matrix.vecMul, dotProduct, hGdef, map_sum]
  have h2 : G.det • p = Matrix.vecMul (Matrix.vecMul p G) G.adjugate := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  have h3 : G.det * p a = algebraMap (𝓞 K) K (∑ b, η b * (Matrix.of G0).adjugate b a) := by
    have := congrFun h2 a
    rw [Pi.smul_apply, smul_eq_mul] at this
    rw [this, h1, hGm, ← RingHom.map_adjugate]
    simp [Matrix.vecMul, dotProduct, map_sum]
  rw [smul_smul, h3, algebraMap_smul]
  exact Λ.smul_mem _ (hx a)

omit [StarRing K] in
theorem ipow_add (𝔡 : Ideal (𝓞 K)) (h : 𝔡 ≠ ⊥) (m n : ℤ) : ipow 𝔡 (m + n) = ipow 𝔡 m * ipow 𝔡 n := by
  unfold ipow
  rw [zpow_add₀ (by simpa using h), FractionalIdeal.coe_mul]

omit [StarRing K] in
theorem ipow_zero (𝔡 : Ideal (𝓞 K)) : ipow 𝔡 0 = 1 := by
  unfold ipow; simp

omit [StarRing K] in
theorem ipow_sum (𝔡 : Ideal (𝓞 K)) (h : 𝔡 ≠ ⊥) {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    ipow 𝔡 (∑ i ∈ s, f i) = ∏ i ∈ s, ipow 𝔡 (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [ipow_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ipow_add _ h, ih]

theorem star_mem_one {x : K} (hx : x ∈ (1 : Submodule (𝓞 K) K)) : star x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hx
  have : IsIntegral ℤ (star (algebraMap (𝓞 K) K o)) :=
    (RingOfIntegers.isIntegral_coe o).map (starRingEnd K).toIntAlgHom
  exact Submodule.mem_one.2 ⟨⟨_, this⟩, rfl⟩

theorem star_mem_ipow_nat (𝔡 : Ideal (𝓞 K)) (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℕ) :
    ∀ x ∈ ipow 𝔡 n, star x ∈ ipow 𝔡 n := by
  induction n with
  | zero => intro x hx; simp only [Nat.cast_zero, ipow_zero] at hx ⊢; exact star_mem_one hx
  | succ n ih =>
    intro x hx
    rw [Nat.cast_succ, ipow_add _ h] at hx ⊢
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [star_mul']
      refine Submodule.mul_mem_mul (ih a ha) ?_
      simp only [ipow, zpow_one] at hb ⊢
      obtain ⟨o, ho, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hb
      obtain ⟨y, hy, hy'⟩ := hs o ho
      exact (FractionalIdeal.mem_coeIdeal _).2 ⟨y, hy, hy'⟩
    · intro a b ha hb; rw [star_add]; exact add_mem ha hb

theorem star_mem_ipow_neg (𝔡 : Ideal (𝓞 K)) (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℕ) :
    ∀ x ∈ ipow 𝔡 (-(n : ℤ)), star x ∈ ipow 𝔡 (-(n : ℤ)) := by
  have hne : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (n : ℤ)) ≠ 0 := zpow_ne_zero _ (by simpa using h)
  have key : ∀ x : K, x ∈ ipow 𝔡 (-(n : ℤ)) ↔ ∀ y ∈ ipow 𝔡 n, x * y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x
    unfold ipow
    rw [zpow_neg, FractionalIdeal.mem_coe, FractionalIdeal.mem_inv_iff hne]
    simp only [FractionalIdeal.mem_coe, ← FractionalIdeal.coe_one (S := (𝓞 K)⁰)]
  intro x hx
  rw [key] at hx ⊢
  intro y hy
  have := star_mem_one (hx _ (star_mem_ipow_nat 𝔡 h hs n y hy))
  simpa using this

omit [StarRing K] in
theorem prod_le_of_forall {ι : Type} [Fintype ι] (A : ι → Submodule (𝓞 K) K) (J : Submodule (𝓞 K) K)
    (h : ∀ f : ι → K, (∀ i, f i ∈ A i) → ∏ i, f i ∈ J) : ∏ i, A i ≤ J := by
  have : ∏ i, A i = ∏ i, Submodule.span (𝓞 K) (A i : Set K) := by simp
  rw [this, Submodule.prod_span, Submodule.span_le]
  intro y hy
  obtain ⟨f, hf, rfl⟩ := (Set.mem_fintype_prod _ _).1 hy
  exact h f hf

variable {H : HermSpace K V} {r : ℕ}

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem Xa_coords (F : FlagD H r) {j : ℕ} (hj : j ≤ r + 1) {n : ℕ} (hn : n ≤ j) {y : V} (hy : y ∈ F.Xa n) :
    ∃ p : Fin j → K, (∀ b : Fin j, n ≤ b.val → p b = 0) ∧ y = ∑ b, p b • F.e (Fin.castLE hj b) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    have hb' : b.val < n := hb
    refine ⟨Pi.single ⟨b.val, by omega⟩ 1, fun c hc => Pi.single_eq_of_ne ?_ _, ?_⟩
    · intro h; rw [h] at hc; simp at hc; omega
    · rw [Finset.sum_eq_single ⟨b.val, by omega⟩]
      · simp only [Pi.single_eq_same, one_smul]; rfl
      · intro c _ hc; rw [Pi.single_eq_of_ne hc, zero_smul]
      · simp
  | zero => exact ⟨0, by simp, by simp⟩
  | add y y' _ _ h h' =>
    obtain ⟨p, hp, rfl⟩ := h
    obtain ⟨p', hp', rfl⟩ := h'
    exact ⟨p + p', fun b hb => by simp [hp b hb, hp' b hb], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul a y _ h =>
    obtain ⟨p, hp, rfl⟩ := h
    exact ⟨a • p, fun b hb => by simp [hp b hb], by simp [Finset.smul_sum, smul_smul]⟩

omit [NumberField K] in
theorem exists_tri (F : FlagD H r) (Λ : Submodule (𝓞 K) V) (aa : Fin r → Submodule (𝓞 K) K) (hF : IsFrame F Λ aa)
    {j : ℕ} (hj : j ≤ r) (s : Fin j → K) (hs : ∀ a, s a ∈ aa (Fin.castLE hj a)) :
    ∃ A : Matrix (Fin j) (Fin j) K, A.det = ∏ a, s a ∧
      ∀ a, ∑ c, A a c • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) c) ∈ Λ := by
  have h : ∀ a : Fin j, ∃ p : Fin j → K, (∀ b : Fin j, a.val ≤ b.val → p b = 0) ∧
      s a • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a) -
        ∑ b, p b • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) b) ∈ Λ := by
    intro a
    have h1 := hs a
    rw [← hF.1] at h1
    obtain ⟨l, hl, ξ, hξ, he⟩ := Submodule.mem_sup.1 h1
    obtain ⟨p, hp, rfl⟩ := Xa_coords F (hj.trans (Nat.le_succ r)) (n := a.val) a.isLt.le hξ
    refine ⟨p, hp, ?_⟩
    have he' : l + ∑ b, p b • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) b) =
      s a • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a) := he
    rw [← he']; simpa using hl
  choose p hp hΛ using h
  refine ⟨Matrix.diagonal s - Matrix.of p, ?_, fun a => ?_⟩
  · rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp [hp a a le_rfl]
    · intro a b hab
      have hab' : a < b := hab
      simp [Matrix.diagonal_apply_ne _ hab'.ne, hp a b hab'.le]
  · convert hΛ a using 1
    simp [sub_smul, Finset.sum_sub_distrib, Matrix.diagonal_apply, ite_smul]

omit [NumberField K] in
theorem prod_smul_mem (F F' : FlagD H r) (Λ : Submodule (𝓞 K) V) (aa : Fin r → Submodule (𝓞 K) K)
    (hF : IsFrame F Λ aa) (hF' : IsFrame F' Λ aa)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K))
    {j : ℕ} (hj : j ≤ r) (s t : Fin j → K) (hs : ∀ a, s a ∈ aa (Fin.castLE hj a))
    (ht : ∀ a, t a ∈ aa (Fin.castLE hj a)) {ξ : V} (hξ : ξ ∈ F.Xa j)
    (hp : ∀ y ∈ Λ, y ∈ F'.X → H.B ξ y ∈ (1 : Submodule (𝓞 K) K)) :
    ((∏ a, s a) * Dl F F' j (hj.trans (Nat.le_succ r)) * star (∏ a, t a)) • ξ ∈ Λ := by
  obtain ⟨A, hA, hAΛ⟩ := exists_tri F Λ aa hF hj s hs
  obtain ⟨A', hA', hAΛ'⟩ := exists_tri F' Λ aa hF' hj t ht
  by_cases h0 : A.det = 0
  · rw [← hA, h0]; simp
  obtain ⟨q, -, rfl⟩ := Xa_coords F (hj.trans (Nat.le_succ r)) le_rfl hξ
  have hq : ∑ a, (Matrix.vecMul q A⁻¹) a • ∑ c, A a c • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) c) =
      ∑ c, q c • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) c) := by
    have : Matrix.vecMul (Matrix.vecMul q A⁻¹) A = q := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit h0), Matrix.vecMul_one]
    conv_rhs => rw [← this]
    generalize Matrix.vecMul q A⁻¹ = p
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  have hX : ∀ b, ∑ c, A' b c • F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) c) ∈ F'.X := fun b =>
    Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (e_mem_X F' (Fin.castLE hj c))
  have key := det_smul_mem H Λ _ _ hAΛ (fun a b => hint _ (hAΛ a) _ (hAΛ' b)) (Matrix.vecMul q A⁻¹)
    (fun b => by rw [hq]; exact hp _ (hAΛ' b) (hX b))
  rw [hq] at key
  convert key using 2
  rw [← hA, ← hA', ← Matrix.det_conjTranspose, Dl, ← Matrix.det_mul, ← Matrix.det_mul]
  congr 1
  ext a b
  simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.map_smulₛₗ, Matrix.submatrix_apply, Zhat, Matrix.conjTranspose_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, starRingEnd_apply]
  first
    | (refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring)
    | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring)

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem Dl_ne (N : NF H r) : Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) ≠ 0 := by
  have : (Zhat N.F N.F').submatrix (Fin.castLE (N.j_le.trans (Nat.le_succ r)))
      (Fin.castLE (N.j_le.trans (Nat.le_succ r))) = N.w.mat * Matrix.diagonal fun b => ((N.sgn b : ℤ) : K) := by
    ext a b
    simp [Zhat, N.pair, Matrix.mul_diagonal]
  rw [Dl, this, Matrix.det_mul, Matrix.det_diagonal]
  refine mul_ne_zero (GlobalTheory.SgLoc.PtAlg.isUnit_det N.w).ne_zero (Finset.prod_ne_zero_iff.2 fun b _ => ?_)
  exact_mod_cast (N.sgn b).ne_zero

theorem smul_mem_of_pairing (N : NF H r) (Λ : Submodule (𝓞 K) V) (hΛ : IsFramed N.F N.F' Λ N.aa) (γ : K)
    (hγ : ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range N.j, ((r : ℤ) - a)),
      γ * y / Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) ∈ (1 : Submodule (𝓞 K) K))
    {ξ : V} (hξ : ξ ∈ N.F.Xa N.j) (hp : ∀ y ∈ Λ, y ∈ N.F'.X → H.B ξ y ∈ (1 : Submodule (𝓞 K) K)) :
    γ • ξ ∈ Λ := by
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x hx
    rw [← hΛ.1.2, mem_dual_iff] at hx
    exact hx.2
  have hD := Dl_ne N
  set D := Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) with hDdef
  set m : ℤ := 2 * ∑ a ∈ Finset.range N.j, ((r : ℤ) - a) with hm
  let J : Submodule (𝓞 K) K := Λ.comap ((LinearMap.toSpanSingleton K V (D • ξ)).restrictScalars (𝓞 K))
  have h1 : ipow N.𝔡 (-m) ≤ J := by
    have e : -m = ∑ i : Fin N.j ⊕ Fin N.j,
        Sum.elim (fun a : Fin N.j => -((r : ℤ) - a.val)) (fun a : Fin N.j => -((r : ℤ) - a.val)) i := by
      rw [Fintype.sum_sum_type, hm, ← Fin.sum_univ_eq_sum_range (fun a : ℕ => (r : ℤ) - a)]
      simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_neg_distrib]
      ring
    rw [e, ipow_sum _ N.𝔡_ne]
    refine prod_le_of_forall _ _ fun f hf => ?_
    have := prod_smul_mem N.F N.F' Λ N.aa hΛ.2.1 hΛ.2.2 hint N.j_le (fun a => f (Sum.inl a))
      (fun a => star (f (Sum.inr a))) (fun a => hf (Sum.inl a)) (fun a => ?_) hξ hp
    · show (∏ i, f i) • (D • ξ) ∈ Λ
      convert this using 1
      rw [smul_smul, Fintype.prod_sum_type, star_prod]
      simp only [star_star]
      congr 1; ring
    · have h2 := hf (Sum.inr a)
      have ha : a.val ≤ r := a.isLt.le.trans N.j_le
      have e2 : (r : ℤ) - a.val = ((r - a.val : ℕ) : ℤ) := by push_cast [ha]; ring
      show _ ∈ ipow N.𝔡 (-((r : ℤ) - a.val))
      simp only [Sum.elim_inr] at h2
      rw [e2] at h2 ⊢
      exact star_mem_ipow_neg _ N.𝔡_ne N.𝔡_star _ _ h2
  have h2 : ∀ w ∈ ipow N.𝔡 m * ipow N.𝔡 (-m), γ / D * w ∈ ipow N.𝔡 (-m) := by
    intro w hw
    refine Submodule.mul_induction_on hw ?_ ?_
    · intro y hy y' hy'
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hγ y hy)
      have : γ / D * (y * y') = o • y' := by rw [Algebra.smul_def, ho]; ring
      rw [this]; exact Submodule.smul_mem _ _ hy'
    · intro a b ha hb; rw [mul_add]; exact add_mem ha hb
  have h3 := h1 (h2 1 (by rw [← ipow_add _ N.𝔡_ne, add_neg_cancel, ipow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩))
  have h4 : (γ / D * 1) • (D • ξ) ∈ Λ := h3
  rwa [smul_smul, mul_one, div_mul_cancel₀ _ hD] at h4

section Geometry
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def Ia (N : NF H r) (n : ℕ) : Submodule K V :=
  Submodule.span K ((fun b : Fin r => N.F.e b.castSucc) '' {b | N.j ≤ b.val ∧ b.val < n})

theorem e_mem_Ia (N : NF H r) (b : Fin r) {n : ℕ} (h : N.j ≤ b.val) (h' : b.val < n) :
    N.F.e b.castSucc ∈ Ia N n := Submodule.subset_span ⟨b, ⟨h, h'⟩, rfl⟩

theorem Ia_mono (N : NF H r) {m n : ℕ} (h : m ≤ n) : Ia N m ≤ Ia N n :=
  Submodule.span_mono (Set.image_mono fun _ hb => ⟨hb.1, lt_of_lt_of_le hb.2 h⟩)

theorem Ia_le (N : NF H r) (n : ℕ) : Ia N n ≤ N.F.Xa n :=
  Submodule.span_mono (Set.image_mono fun _ hb => hb.2)

theorem c_ne (N : NF H r) : N.c ≠ 0 := fun h => by simpa [h] using N.c_norm

theorem Ia_le' (N : NF H r) (n : ℕ) : Ia N n ≤ N.F'.Xa n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, hb, rfl⟩
  have h := Submodule.smul_mem _ N.c⁻¹ (e_mem_Xa N.F' b hb.2)
  rw [N.same _ hb.1, smul_smul, inv_mul_cancel₀ (c_ne N), one_smul] at h
  exact h

theorem Ia_X (N : NF H r) {n : ℕ} {y : V} (h : y ∈ Ia N n) : y ∈ N.F.X := Xa_le_X _ _ (Ia_le N n h)
theorem Ia_X' (N : NF H r) {n : ℕ} {y : V} (h : y ∈ Ia N n) : y ∈ N.F'.X := Xa_le_X _ _ (Ia_le' N n h)

theorem Xa_le_sup (N : NF H r) (n : ℕ) : N.F.Xa n ≤ N.F.Xa N.j ⊔ Ia N n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, hb, rfl⟩
  by_cases h : b.val < N.j
  · exact Submodule.mem_sup_left (e_mem_Xa N.F b h)
  · exact Submodule.mem_sup_right (e_mem_Ia N b (not_lt.1 h) hb)

theorem Xa_ist (N : NF H r) (b : Fin r) (hb : N.j ≤ b.val) : ∀ y ∈ N.F.Xa b.val, H.B y (N.ist b) = 0 :=
  perp_Xa N.F fun a ha => by rw [N.ist_e a b hb, if_neg (by rintro rfl; omega)]

theorem Ia_step (N : NF H r) (b : Fin r) (hb : N.j ≤ b.val) {y : V} (hy : y ∈ Ia N (b.val + 1)) :
    y - H.B y (N.ist b) • N.F.e b.castSucc ∈ Ia N b.val := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    simp only [N.ist_e a b hb]
    split_ifs with h
    · subst h; simp
    · have : a.val ≠ b.val := fun h' => h (Fin.ext h')
      have h2 := ha.2
      simpa using e_mem_Ia N a ha.1 (show a.val < b.val by omega)
  | zero => simp
  | add y y' _ _ h h' =>
    convert add_mem h h' using 1
    simp only [map_add, LinearMap.add_apply]; module
  | smul a y _ h =>
    convert Submodule.smul_mem _ a h using 1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; module

theorem Ia_bot (N : NF H r) {n : ℕ} (h : n ≤ N.j) {y : V} (hy : y ∈ Ia N n) : y = 0 := by
  have : Ia N n ≤ ⊥ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    have := hb.1; have := hb.2; omega
  exact this hy

theorem II_le (N : NF H r) : II N.F N.F' ≤ Ia N r := by
  intro x hx
  obtain ⟨ξ, hξ, i, hi, rfl⟩ := Submodule.mem_sup.1 (Xa_le_sup N r hx.1)
  have hξ' : ξ ∈ N.F'.X := by simpa using sub_mem hx.2 (Ia_X' N hi)
  obtain ⟨p, -, rfl⟩ := Xa_coords N.F (N.j_le.trans (Nat.le_succ r)) le_rfl hξ
  have : p = 0 := by
    refine Matrix.eq_zero_of_vecMul_eq_zero (Dl_ne N) ?_
    funext b
    have := X_iso N.F' hξ' (e_mem_X N.F' (Fin.castLE N.j_le b))
    simpa [Matrix.vecMul, dotProduct, Zhat, map_sum] using this
  simpa [this] using hi

theorem hermForm_second_flag_X_z_eq_zero (N : NF H r) {y : V} (hy : y ∈ N.F'.X) : H.B y N.F.z = 0 := by
  have h := pairing_isotropicSpan_lastVector N.F' hy
  have e : N.F'.z = N.c • N.F.z := N.same (Fin.last r) N.j_le
  rw [e, LinearMap.map_smulₛₗ, smul_eq_mul, mul_eq_zero] at h
  exact h.resolve_left (by simpa using c_ne N)

theorem eich_apply (x v : V) (c : K) (y : V) :
    eich H x v c y = y + H.B y v • x - H.B y x • v + (c * H.B y x) • x := by
  simp only [eich, xv, LinearMap.add_apply, LinearMap.id_apply, LinearMap.sub_apply, LinearMap.smulRight_apply,
    LinearMap.flip_apply, LinearMap.smul_apply]
  module

theorem eich_inN (F : FlagD H r) (x v : V) (c : K) (hx : x ∈ F.X) (hxv : H.B x v = 0)
    (hc : c + star c = -H.B v v) (hlev : ∀ a : Fin r, H.B (F.e a.castSucc) v • x ∈ F.Xa a.val) :
    F.InN (eich H x v c) := by
  obtain ⟨h1, h2, h3⟩ := eichlerMapIsometry K V H x v c (X_iso F hx hx) hxv hc
  refine ⟨h1, ⟨Function.LeftInverse.injective h2, Function.RightInverse.surjective h3⟩, fun a => ?_, fun y hy => ?_⟩
  · simpa [eich_apply, e_X F _ hx] using hlev a
  · have : H.B y x = 0 := B_swap0 H (perp_X F hy x hx)
    simpa [eich_apply, this] using Submodule.smul_mem _ _ hx

def Gs (N : NF H r) : Subgroup (V ≃ₗ[K] V) := N.Rs ⊓ N.fixing (N.F.Xa N.j ⊔ N.F'.Xa N.j)

theorem exists_eich (N : NF H r) (x v : V) (c : K) (hx : x ∈ Ia N r) (hxv : H.B x v = 0)
    (hc : c + star c = -H.B v v)
    (hlev : ∀ a : Fin r, N.j ≤ a.val → H.B (N.F.e a.castSucc) v • x ∈ Ia N a.val)
    (h1 : ∀ a : Fin r, a.val < N.j → H.B (N.F.e a.castSucc) v = 0)
    (h2 : ∀ a : Fin r, a.val < N.j → H.B (N.F'.e a.castSucc) v = 0)
    (hW : v ∈ V0 N.F N.F' ⊔ N.Ist) :
    ∃ s ∈ Gs N, ∀ y, H.B y x = 0 → s y = y + H.B y v • x := by
  obtain ⟨-, e2, e3⟩ := eichlerMapIsometry K V H x v c (X_iso N.F (Ia_X N hx) (Ia_X N hx)) hxv hc
  let s : V ≃ₗ[K] V := LinearEquiv.ofLinear (eich H x v c) (eich H x (-v) (star c))
    (LinearMap.ext e3) (LinearMap.ext e2)
  have hs : ∀ y, H.B y x = 0 → s y = y + H.B y v • x := by
    intro y hy
    show eich H x v c y = _
    simp [eich_apply, hy]
  refine ⟨s, ⟨⟨Subgroup.subset_closure ⟨?_, ?_⟩, ?_⟩, ?_⟩, hs⟩
  · refine eich_inN N.F x v c (Ia_X N hx) hxv hc fun a => ?_
    by_cases h : a.val < N.j
    · simp [h1 a h]
    · exact Ia_le N _ (hlev a (not_lt.1 h))
  · refine eich_inN N.F' x v c (Ia_X' N hx) hxv hc fun a => ?_
    by_cases h : a.val < N.j
    · simp [h2 a h]
    · rw [N.same _ (not_lt.1 h), map_smul, LinearMap.smul_apply, smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ _ (Ia_le' N _ (hlev a (not_lt.1 h)))
  · refine (mem_fixingSubgroup_iff _).2 fun y hy => ?_
    have hy' := (mem_perp_iff H _ y).1 hy
    show s y = y
    rw [hs y (hy' x (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Ia_X N hx))))),
      hy' v hW]
    simp
  · refine (mem_fixingSubgroup_iff _).2 fun y hy => ?_
    show s y = y
    rw [hs y (perp_sup H (fun u hu => X_iso N.F (Xa_le_X _ _ hu) (Ia_X N hx))
      (fun u hu => X_iso N.F' (Xa_le_X _ _ hu) (Ia_X' N hx)) y hy),
      perp_sup H (perp_Xa N.F h1) (perp_Xa N.F' h2) y hy]
    simp

theorem exists_shear (N : NF H r) (b : Fin r) (hb : N.j ≤ b.val) {x : V} (hx : x ∈ Ia N b.val) :
    ∃ s ∈ Gs N, s N.F.z = N.F.z ∧ ∀ y ∈ N.F.X, s y = y + H.B y (N.ist b) • x := by
  obtain ⟨s, hs, h⟩ := exists_eich N x (N.ist b) 0 (Ia_mono N b.isLt.le hx) (Xa_ist N b hb x (Ia_le N _ hx))
    (by simp [N.ist_iso b b hb hb])
    (fun a _ => by
      rw [N.ist_e a b hb]
      split_ifs with h
      · subst h; simpa using hx
      · simp)
    (fun a ha => by rw [N.ist_e a b hb, if_neg (by rintro rfl; omega)])
    (fun a ha => N.ist_e' a b ha hb)
    (Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩))
  refine ⟨s, hs, ?_, fun y hy => h y (X_iso N.F hy (Ia_X N hx))⟩
  rw [h _ (z_X N.F (Ia_X N hx)), N.normalForm_dual_orthogonal_last b hb]; simp

theorem exists_move_alt (N : NF H r) {x : V} (hx : x ∈ Ia N r) :
    ∃ s ∈ Gs N, s N.F.z = N.F.z - x ∧ ∀ y ∈ N.F.X, s y = y := by
  have hz : ∀ y, H.B y (star N.F.T⁻¹ • N.F.z) = N.F.T⁻¹ * H.B y N.F.z := by
    intro y; rw [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul]
  obtain ⟨s, hs, h⟩ := exists_eich N x (star N.F.T⁻¹ • N.F.z)
    (-H.B (star N.F.T⁻¹ • N.F.z) (star N.F.T⁻¹ • N.F.z) / 2) hx
    (by rw [hz, pairing_isotropicSpan_lastVector N.F (Ia_X N hx), mul_zero])
    (by rw [star_div₀, star_neg, H.herm, star_ofNat]; ring)
    (fun a _ => by rw [hz, pairing_isotropicSpan_lastVector N.F (e_mem_X _ _)]; simp)
    (fun a _ => by rw [hz, pairing_isotropicSpan_lastVector N.F (e_mem_X _ _)]; simp)
    (fun a _ => by rw [hz, hermForm_second_flag_X_z_eq_zero N (e_mem_X _ _)]; simp)
    (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_insert _ _)))))
  refine ⟨s, hs, ?_, fun y hy => ?_⟩
  · rw [h _ (z_X N.F (Ia_X N hx)), hz, pairing_lastVector_lastVector, mul_neg, inv_mul_cancel₀ N.F.hT]; module
  · rw [h _ (X_iso N.F hy (Ia_X N hx)), hz, pairing_isotropicSpan_lastVector N.F hy]; simp

theorem exists_unitri (N : NF H r) (v : Fin r → V)
    (hv : ∀ b : Fin r, N.j ≤ b.val → v b - N.F.e b.castSucc ∈ Ia N b.val) :
    ∃ u ∈ Gs N, u N.F.z = N.F.z ∧ ∀ b : Fin r, N.j ≤ b.val → u (v b) = N.F.e b.castSucc := by
  have key : ∀ m : ℕ, ∃ u ∈ Gs N, u N.F.z = N.F.z ∧ ∀ b : Fin r, N.j ≤ b.val →
      u (v b) = if r ≤ b.val + m then N.F.e b.castSucc else v b := by
    intro m
    induction m with
    | zero => exact ⟨1, one_mem _, rfl, fun b _ => by rw [if_neg (by have := b.isLt; omega)]; rfl⟩
    | succ m ih =>
      obtain ⟨u, hu, huz, h⟩ := ih
      by_cases hm : N.j + m + 1 ≤ r
      · let b0 : Fin r := ⟨r - m - 1, by omega⟩
        have hb0 : N.j ≤ b0.val := by show N.j ≤ r - m - 1; omega
        have hb1 : b0.val = r - m - 1 := rfl
        obtain ⟨s, hs, hsz, hs'⟩ := exists_shear N b0 hb0 (neg_mem (hv b0 hb0))
        refine ⟨s * u, mul_mem hs hu, by simp [huz, hsz], fun b hb => ?_⟩
        have hvX : v b ∈ N.F.Xa (b.val + 1) := by
          have := add_mem (Xa_mono N.F (Nat.le_succ _) (Ia_le N _ (hv b hb))) (e_mem_Xa N.F b (Nat.lt_succ_self _))
          simpa using this
        rw [LinearEquiv.mul_apply, h b hb]
        by_cases h1 : r ≤ b.val + m
        · rw [if_pos h1, if_pos (by omega), hs' _ (e_mem_X _ _), N.ist_e b b0 hb0,
            if_neg (by rintro rfl; omega)]
          simp
        · rw [if_neg h1, hs' _ (Xa_le_X _ _ hvX)]
          by_cases h2 : b = b0
          · subst h2
            have h3 := Xa_ist N b0 hb0 _ (Ia_le N _ (hv b0 hb0))
            rw [map_sub, LinearMap.sub_apply, N.ist_e b0 b0 hb0, if_pos rfl, sub_eq_zero] at h3
            rw [if_pos (by omega), h3]; simp
          · have h3 : b.val ≠ b0.val := fun h' => h2 (Fin.ext h')
            rw [if_neg (by omega), Xa_ist N b0 hb0 _ (Xa_mono N.F (by omega) hvX)]
            simp
      · refine ⟨u, hu, huz, fun b hb => ?_⟩
        rw [h b hb, if_pos (by omega), if_pos (by omega)]
  obtain ⟨u, hu, huz, h⟩ := key r
  exact ⟨u, hu, huz, fun b hb => by rw [h b hb, if_pos (by omega)]⟩

end Geometry

theorem level_ind (N : NF H r) (M Q : Submodule (𝓞 K) V) (w : Fin r → V)
    (hw : ∀ b : Fin r, N.j ≤ b.val → w b - N.F.e b.castSucc ∈ Ia N b.val)
    (h : ∀ b : Fin r, N.j ≤ b.val → ∀ y ∈ M, y ∈ Ia N (b.val + 1) →
      H.B y (N.ist b) • w b ∈ M ∧ H.B y (N.ist b) • w b ∈ Q) :
    ∀ n ≤ r, ∀ y ∈ M, y ∈ Ia N n → y ∈ Q := by
  intro n
  induction n with
  | zero => intro _ y _ hy; rw [Ia_bot N (Nat.zero_le _) hy]; exact zero_mem _
  | succ n ih =>
    intro hn y hyM hy
    by_cases hj : N.j ≤ n
    · let b : Fin r := ⟨n, hn⟩
      obtain ⟨h1, h2⟩ := h b hj y hyM hy
      have h3 : y - H.B y (N.ist b) • w b ∈ Ia N n := by
        convert sub_mem (Ia_step N b hj hy) (Submodule.smul_mem _ (H.B y (N.ist b)) (hw b hj)) using 1
        module
      simpa using add_mem (ih (by omega) _ (sub_mem hyM h1) h3) h2
    · rw [Ia_bot N (by omega) hy]; exact zero_mem _

theorem smul_flag_vector_mem_reference_lattice (N : NF H r) (b : Fin r) {t : K} (ht : t ∈ N.aa b) : t • N.F.e b.castSucc ∈ N.P0 :=
  Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_iSup_of_mem b ⟨t, ht, rfl⟩)))

theorem hermForm_ist_mem_coeffIdeal_of_mem_reference (N : NF H r) (b : Fin r) (hb : N.j ≤ b.val) {y : V} (hy : y ∈ N.P0) :
    H.B y (N.ist b) ∈ N.aa b := by
  have : N.P0 ≤ (N.aa b).comap ((H.B.flip (N.ist b)).restrictScalars (𝓞 K)) := by
    refine sup_le (sup_le (sup_le (iSup_le fun a => ?_) (iSup₂_le fun a ha => ?_)) ?_) (iSup₂_le fun a ha => ?_)
    all_goals
      rintro _ ⟨t, ht, rfl⟩
      show H.B (t • _) (N.ist b) ∈ N.aa b
      rw [map_smul, LinearMap.smul_apply]
    · rw [N.ist_e a b hb]
      split_ifs with h
      · subst h; simpa using ht
      · simp
    · simp [N.ist_e' a b ha hb]
    · simp [N.normalForm_dual_orthogonal_last b hb]
    · simp [N.ist_iso a b ha hb]
  exact this hy

theorem exists_adapted (N : NF H r) (Λ : Submodule (𝓞 K) V) (hΛ : Λ.FG) (b : Fin r) (hb : N.j ≤ b.val) :
    ∃ v, v - N.F.e b.castSucc ∈ Ia N b.val ∧
      ∀ y ∈ Λ, y ∈ Ia N (b.val + 1) → H.B y (N.ist b) • v ∈ Λ := by
  by_cases h0 : ∃ y ∈ Λ ⊓ rs (𝓞 K) (Ia N (b.val + 1)), H.B.flip (N.ist b) y ≠ 0
  · obtain ⟨v, hv, h1, h⟩ := exists_section _ (hΛ.of_le inf_le_left) _ h0
    have hv' : v ∈ Ia N (b.val + 1) := (Submodule.span_le.2 fun y hy => hy.2) hv
    refine ⟨v, ?_, fun y hy hy' => (h y ⟨hy, hy'⟩).1⟩
    have := Ia_step N b hb hv'
    rwa [show H.B v (N.ist b) = 1 from h1, one_smul] at this
  · push_neg at h0
    refine ⟨N.F.e b.castSucc, by simp, fun y hy hy' => ?_⟩
    rw [show H.B y (N.ist b) = 0 from h0 y ⟨hy, hy'⟩]; simp

theorem smul_add_mem (N : NF H r) (Λ : Submodule (𝓞 K) V) (hΛ : IsFramed N.F N.F' Λ N.aa) (γ : 𝓞 K)
    (hγ : ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range N.j, ((r : ℤ) - a)),
      (γ : K) * y / Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) ∈ (1 : Submodule (𝓞 K) K))
    {y ξ : V} (hy : ∀ u ∈ N.F'.X, H.B y u = 0) (hξ : ξ ∈ N.F.Xa N.j) (h : y - ξ ∈ Λ) : γ • y ∈ Λ := by
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x hx
    rw [← hΛ.1.2, mem_dual_iff] at hx
    exact hx.2
  have h1 := smul_mem_of_pairing N Λ hΛ γ hγ hξ fun u hu hu' => by
    have := neg_mem (hint _ h u hu)
    simpa [hy u hu'] using this
  have h2 : γ • ξ ∈ Λ := by rw [← algebraMap_smul K γ ξ]; exact h1
  simpa [smul_sub] using add_mem (Λ.smul_mem γ h) h2

theorem normal_position : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∃ s ∈ N.Rs, (∀ y ∈ N.F.Xa N.j ⊔ N.F'.Xa N.j, s y = y) ∧ ∀ Λ' : Submodule (𝓞 K) V, Λ' = s • Λ → 𝔠 ^ 2 • (N.P0 ⊓ rs (𝓞 K) (II N.F N.F')) ≤ Λ' ∧ Λ' ⊓ rs (𝓞 K) (II N.F N.F') ≤ N.P0 ∧ 𝔠 • line 1 N.F.z ≤ Λ' := by
  intro K V _ _ _ _ _ _ _ _ H _ r N g Λ _ hT 𝔠 _ _ _ h𝔠
  have hΛ := hT.1
  have hγ : ∀ γ ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range N.j, ((r : ℤ) - a)),
      (γ : K) * y / Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) ∈ (1 : Submodule (𝓞 K) K) :=
    fun γ h y hy => (h𝔠 N.j _ le_rfl (Dl_ne N) γ h y hy).1
  have hfg : Λ.FG := ((isUnimod_iff H Λ).1 hΛ.1).1.fg
  choose! v hv hvΛ using exists_adapted N Λ hfg
  obtain ⟨u, hu, huz, huv⟩ := exists_unitri N v hv
  have hz : (1 : K) ∈ lead N.F Λ (Fin.last r) := by rw [hΛ.2.1.2]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  obtain ⟨l, hl, ξ, hξ, he⟩ := Submodule.mem_sup.1 hz
  have he' : l + ξ = (1 : K) • N.F.z := he
  obtain ⟨ξ₁, hξ₁, ξ₂, hξ₂, rfl⟩ := Submodule.mem_sup.1 (Xa_le_sup N r hξ)
  obtain ⟨E, hE, hEz, hEX⟩ := exists_move_alt N (neg_mem hξ₂)
  have hvX : ∀ b : Fin r, N.j ≤ b.val → v b ∈ Ia N r := fun b hb => by
    simpa using add_mem (Ia_mono N b.isLt.le (hv b hb)) (e_mem_Ia N b hb b.isLt)
  have hsv : ∀ b : Fin r, N.j ≤ b.val → ∀ t : K, (u * E) (t • v b) = t • N.F.e b.castSucc := fun b hb t => by
    rw [map_smul, LinearEquiv.mul_apply, hEX _ (Ia_X N (hvX b hb)), huv b hb]
  have hmem : ∀ y, y ∈ (u * E) • Λ ↔ ∃ x ∈ Λ, (u * E) x = y := fun y =>
    Submodule.mem_smul_pointwise_iff_exists _ _ _
  have hG := mul_mem hu hE
  refine ⟨u * E, hG.1, fun y hy => (mem_fixingSubgroup_iff _).1 hG.2 y hy, ?_⟩
  rintro _ rfl
  refine ⟨?_, ?_, ?_⟩
  · refine Submodule.smul_le.2 fun γ hγ2 y hy => ?_
    have hγ1 : γ ∈ 𝔠 := Ideal.pow_le_self two_ne_zero hγ2
    refine level_ind N N.P0 (((u * E) • Λ).comap (γ • LinearMap.id)) (fun b => N.F.e b.castSucc)
      (fun b _ => by simp) (fun b hb y hy _ => ?_) r le_rfl y hy.1 (II_le N hy.2)
    have ht := hermForm_ist_mem_coeffIdeal_of_mem_reference N b hb hy
    refine ⟨smul_flag_vector_mem_reference_lattice N b ht, ?_⟩
    generalize H.B y (N.ist b) = t at ht
    rw [← hΛ.2.1.1] at ht
    obtain ⟨l, hl, ξ, hξ, he⟩ := Submodule.mem_sup.1 ht
    have he' : l + ξ = t • N.F.e b.castSucc := he
    obtain ⟨η₁, hη₁, η₂, hη₂, rfl⟩ := Submodule.mem_sup.1 (Xa_le_sup N b.val hξ)
    have hI : t • N.F.e b.castSucc - η₂ ∈ Ia N (b.val + 1) :=
      sub_mem (Submodule.smul_mem _ _ (e_mem_Ia N b hb (Nat.lt_succ_self _))) (Ia_mono N (Nat.le_succ _) hη₂)
    have h1 := smul_add_mem N Λ hΛ γ (hγ γ hγ1) (fun w hw => X_iso N.F' (Ia_X' N hI) hw) hη₁
      (by convert hl using 1; rw [← he']; abel)
    rw [← algebraMap_smul K γ] at h1
    have h2 := hvΛ b hb _ h1 (Submodule.smul_mem _ _ hI)
    show γ • (t • N.F.e b.castSucc) ∈ (u * E) • Λ
    refine (hmem _).2 ⟨_, h2, ?_⟩
    rw [hsv b hb, ← algebraMap_smul K γ (t • _), smul_smul, map_smul, map_sub, map_smul, LinearMap.smul_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, N.ist_e b b hb, Xa_ist N b hb _ (Ia_le N _ hη₂), if_pos rfl,
      smul_eq_mul, smul_eq_mul, mul_one, sub_zero]
  · rintro y ⟨hy, hyI⟩
    obtain ⟨x, hx, rfl⟩ := (hmem y).1 hy
    have hxI : x ∈ Ia N r := by
      have : Ia N r ≤ (Ia N r).map ((u * E : V ≃ₗ[K] V) : V →ₗ[K] V) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨b, hb, rfl⟩
        exact ⟨v b, hvX b hb.1, by simpa using hsv b hb.1 1⟩
      obtain ⟨x', hx', e⟩ := this (II_le N hyI)
      rwa [← (u * E).injective e]
    refine level_ind N Λ (N.P0.comap (((u * E : V ≃ₗ[K] V) : V →ₗ[K] V).restrictScalars (𝓞 K))) v hv
      (fun b hb y hy hy' => ⟨hvΛ b hb y hy hy', ?_⟩) r le_rfl x hx hxI
    show (u * E) (_ • v b) ∈ N.P0
    rw [hsv b hb]
    refine smul_flag_vector_mem_reference_lattice N b ?_
    rw [← hΛ.2.1.1]
    show H.B y (N.ist b) • N.F.e b.castSucc ∈ Λ ⊔ rs (𝓞 K) (N.F.Xa b.val)
    have := sub_mem (Submodule.mem_sup_left hy) (Submodule.mem_sup_right (S := Λ)
      (show _ ∈ rs (𝓞 K) (N.F.Xa b.val) from Ia_le N _ (Ia_step N b hb hy')))
    simpa using this
  · refine Submodule.smul_le.2 ?_
    rintro γ hγ1 _ ⟨t, ht, rfl⟩
    obtain ⟨o, rfl⟩ := Submodule.mem_one.1 ht
    have h1 := smul_add_mem N Λ hΛ γ (hγ γ hγ1) (y := N.F.z - ξ₂)
      (fun w hw => by
        rw [map_sub, LinearMap.sub_apply, B_swap0 H (hermForm_second_flag_X_z_eq_zero N hw), X_iso N.F' (Ia_X' N hξ₂) hw, sub_zero]) hξ₁
      (by convert hl using 1; rw [one_smul] at he'; rw [← he']; abel)
    show γ • (algebraMap (𝓞 K) K o • N.F.z) ∈ (u * E) • Λ
    rw [algebraMap_smul, smul_comm]
    refine Submodule.smul_mem _ _ ((hmem _).2 ⟨_, h1, ?_⟩)
    rw [← algebraMap_smul K γ, ← algebraMap_smul K γ N.F.z, map_smul, LinearEquiv.mul_apply, map_sub, hEz,
      hEX _ (Ia_X N hξ₂)]
    simp [huz]

end GlobalTheory.DegCnt.PosIso

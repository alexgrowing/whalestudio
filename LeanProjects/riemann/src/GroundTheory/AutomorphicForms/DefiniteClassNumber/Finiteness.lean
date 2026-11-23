import Mathlib
import GroundTheory.AutomorphicForms.DefiniteClassNumber.Reconstruction

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField NumberField.InfinitePlace

section Arithmetic

variable {K : Type*} [Field K] [NumberField K]

theorem exists_int_trace_eq {t : K} (ht : IsIntegral ℤ t) : ∃ n : ℤ, Algebra.trace ℚ K t = n :=
  ⟨Algebra.trace ℤ (𝓞 K) ⟨t, ht⟩, (Algebra.coe_trace_int (K := K) ⟨t, ht⟩).symm⟩

theorem exists_int_isIntegral_of_trace :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ t : K, (∀ s, ∃ n : ℤ, Algebra.trace ℚ K (t * integralBasis K s) = n) →
      IsIntegral ℤ ((D : K) * t) := by
  classical
  let B := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) (integralBasis K)
  obtain ⟨D, hD0, hD⟩ := exists_int_mul_isIntegral (Finset.univ.image fun s => B s)
  refine ⟨D, hD0, fun t ht => ?_⟩
  have hexp : t = ∑ s, (Algebra.trace ℚ K (t * integralBasis K s) : K) * B s := by
    conv_lhs => rw [← B.sum_repr t]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, Rat.smul_def]
  rw [hexp, Finset.mul_sum]
  refine IsIntegral.sum _ fun s _ => ?_
  obtain ⟨n, hn⟩ := ht s
  rw [hn, Rat.cast_intCast, mul_left_comm]
  exact (isIntegral_algebraMap (x := n)).mul (hD _ (Finset.mem_image_of_mem _ (Finset.mem_univ s)))

end Arithmetic

section Cramer

theorem exists_int_factorial_mul_of_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    (Z : Matrix n n ℤ) (hZ : Z.det ≠ 0) (B : ℕ) (hB : Z.det.natAbs ≤ B) (c : n → ℚ)
    (hc : ∀ j, ∃ m : ℤ, (Z.map (Int.cast : ℤ → ℚ) *ᵥ c) j = m) (i : n) :
    ∃ m : ℤ, (B.factorial : ℚ) * c i = m := by
  choose w hw using hc
  have hZc : Z.map (Int.cast : ℤ → ℚ) *ᵥ c = fun j => (w j : ℚ) := funext hw
  have hadj : (Z.adjugate.map (Int.cast : ℤ → ℚ)) * Z.map (Int.cast : ℤ → ℚ) =
      (Z.det : ℚ) • (1 : Matrix n n ℚ) := by
    have h := congrArg (Int.castRingHom ℚ).mapMatrix (Matrix.adjugate_mul Z)
    simp only [map_mul, RingHom.mapMatrix_apply, Int.coe_castRingHom] at h
    rw [h]
    ext a b
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdetc : (Z.det : ℚ) • c = fun j => ((Z.adjugate *ᵥ w) j : ℚ) := by
    rw [← one_mulVec c, ← smul_mulVec, ← hadj, ← mulVec_mulVec, hZc]
    funext j
    simp [mulVec, dotProduct]
  have hdvd : Z.det ∣ (B.factorial : ℤ) := by
    rw [← Int.natAbs_dvd]
    exact_mod_cast Nat.dvd_factorial (Int.natAbs_pos.2 hZ) hB
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨q * (Z.adjugate *ᵥ w) i, ?_⟩
  have := congrFun hdetc i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  rw [show (B.factorial : ℚ) = ((Z.det * q : ℤ) : ℚ) by rw [← hq]; norm_cast]
  rw [Int.cast_mul, Int.cast_mul, mul_comm (Z.det : ℚ) (q : ℚ), mul_assoc, this]

end Cramer

section FiniteSets

theorem finite_rat_bounded (c : ℤ) (hc : c ≠ 0) (M : ℚ) :
    {q : ℚ | (∃ n : ℤ, (c : ℚ) * q = n) ∧ |q| ≤ M}.Finite := by
  apply ((Set.finite_Icc (-⌈|(c : ℚ)| * M⌉) ⌈|(c : ℚ)| * M⌉).image
    (fun n : ℤ => (n : ℚ) / c)).subset
  rintro q ⟨⟨n, hn⟩, hq⟩
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  have hnb : |(n : ℚ)| ≤ |(c : ℚ)| * M := by
    rw [← hn, abs_mul]
    exact mul_le_mul_of_nonneg_left hq (abs_nonneg _)
  have hce := Int.le_ceil (|(c : ℚ)| * M)
  refine ⟨n, ⟨?_, ?_⟩, ?_⟩
  · have := neg_abs_le (n : ℚ)
    have h : (-(⌈|(c : ℚ)| * M⌉ : ℚ)) ≤ n := by linarith
    exact_mod_cast h
  · have := le_abs_self (n : ℚ)
    have h : (n : ℚ) ≤ ⌈|(c : ℚ)| * M⌉ := by linarith
    exact_mod_cast h
  · show (n : ℚ) / c = q
    rw [div_eq_iff hc', ← hn]
    ring

end FiniteSets

section ShortBasis

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι E}
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)

omit [Fintype κ] [DecidableEq κ] in
theorem intBasis_smul_mem_adelicLattice {b : Basis κ K E}
    {g : unitaryPoints K E H (FinAdele K)} {x : ι → K ⊗[K] E} (hx : x ∈ adelicLattice b H g)
    (s : IntBasisIdx K) : (integralBasis K s) • x ∈ adelicLattice b H g := by
  have := intSmul_mem_adelicLattice hx (RingOfIntegers.basis K s)
  rwa [integralBasis_apply]

theorem exists_int_smul_mem_of_ratForm
    (hM : IsUnit (traceGram H b).det) {θ : K} (hθ0 : θ ≠ 0) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ (g : unitaryPoints K E H (FinAdele K)) (v : ι → K ⊗[K] E),
      (∀ x ∈ adelicLattice b H g, ∃ n : ℤ, ratForm H θ v x = n) →
        (m : K) • v ∈ adelicLattice b H g := by
  obtain ⟨D, hD0, hD⟩ := exists_int_isIntegral_of_trace (K := K)
  obtain ⟨m, hm0, hm⟩ := exists_int_smul_mem_of_forall_isIntegral b H hM ((D : K) * θ)
    (mul_ne_zero (by exact_mod_cast hD0) hθ0)
  refine ⟨m, hm0, fun g v hv => hm g v fun x hx => ?_⟩
  have := hD (θ * hermTrace K H K v x) fun s => by
    obtain ⟨n, hn⟩ := hv _ (intBasis_smul_mem_adelicLattice hx s)
    refine ⟨n, ?_⟩
    rw [← hn, ratForm_smul_right]
    ring_nf
  rwa [← mul_assoc] at this

theorem exists_short_basis_adelicLattice (hreal : ∀ w : InfinitePlace K, w.IsReal)
    (hHerm : IsHermitianFor (conjHom K E) H) {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    {c₀ : ℤ} (hc₀ : c₀ ≠ 0)
    (hQint : ∀ (g : unitaryPoints K E H (FinAdele K)) (x y : ι → K ⊗[K] E),
      x ∈ adelicLattice b H g → y ∈ adelicLattice b H g → ∃ n : ℤ, (c₀ : ℚ) * ratForm H θ x y = n)
    {m : ℤ} (hm0 : m ≠ 0)
    (hdual : ∀ (g : unitaryPoints K E H (FinAdele K)) (v : ι → K ⊗[K] E),
      (∀ x ∈ adelicLattice b H g, ∃ n : ℤ, ratForm H θ v x = n) → (m : K) • v ∈ adelicLattice b H g)
    (g : unitaryPoints K E H (FinAdele K)) :
    ∃ x : Fin (Fintype.card ((ι × κ) × IntBasisIdx K)) → ι → K ⊗[K] E,
      (∀ i, x i ∈ adelicLattice b H g) ∧ LinearIndependent ℝ (fun i => ratEmb b (x i)) ∧
      ∀ i, (ratForm H θ (x i) (x i) : ℝ) ≤ shortBasisBound (Fintype.card ((ι × κ) × IntBasisIdx K))
        (Real.sqrt (1 / (|(c₀ : ℝ)| * (m : ℝ) ^ 2))) ^ 2 := by
  classical
  set G := (ratGram H b θ).map (Rat.cast : ℚ → ℝ) with hGdef
  have hGs : Gᵀ = G := by rw [hGdef, ← Matrix.transpose_map, ratGram_transpose hHerm]
  have hGpos := ratGram_posDef (b := b) hreal hθ
  set L : AddSubgroup ((ι × κ) × IntBasisIdx K → ℝ) := (adelicLattice b H g).map (ratEmbHom b)
  have hgram : ∀ x y, ratEmb b x ⬝ᵥ (G *ᵥ ratEmb b y) = (ratForm H θ x y : ℝ) := ratEmb_gram b H θ
  have memL : ∀ z, z ∈ L ↔ ∃ x ∈ adelicLattice b H g, ratEmb b x = z := fun z => Iff.rfl
  set μ := Real.sqrt (1 / (|(c₀ : ℝ)| * (m : ℝ) ^ 2)) with hμdef
  have hc₀r : (0 : ℝ) < |(c₀ : ℝ)| := abs_pos.2 (by exact_mod_cast hc₀)
  have hmr : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hμ : 0 < μ := Real.sqrt_pos.2 (by positivity)

  obtain ⟨r, hr0, hr⟩ := exists_int_smul_mem_adelicLattice (b := b) (H := H) g
  have hr0' : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
  have hsingle : ∀ j, (Pi.single j (r : ℝ) : (ι × κ) × IntBasisIdx K → ℝ) ∈ L := by
    intro j
    refine (memL _).2 ⟨(r : K) • ofRatCoords b (Pi.single j 1),
      hr _ (isIntegral_vecCoords_ofRatCoords_single b j), ?_⟩
    funext j'
    simp only [ratEmb, ratCoords_intSmul, ratCoords_ofRatCoords, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply]
    split_ifs <;> simp
  have hLspan : Submodule.span ℝ (L : Set ((ι × κ) × IntBasisIdx K → ℝ)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = ∑ j, (v j / r) • (Pi.single j (r : ℝ) : (ι × κ) × IntBasisIdx K → ℝ) := by
      funext j'
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      field_simp
    rw [hv]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hsingle j))

  have hcS : ∀ z ∈ L, (c₀ : ℝ) • z ∈ {y : (ι × κ) × IntBasisIdx K → ℝ |
      ∀ x ∈ L, ∃ n : ℤ, y ⬝ᵥ (G *ᵥ x) = n} := by
    intro z hz x hx
    obtain ⟨x', hx', rfl⟩ := (memL z).1 hz
    obtain ⟨x'', hx'', rfl⟩ := (memL x).1 hx
    obtain ⟨n, hn⟩ := hQint g x' x'' hx' hx''
    refine ⟨n, ?_⟩
    rw [smul_dotProduct, hgram, smul_eq_mul]
    exact_mod_cast hn
  have hDspan : Submodule.span ℝ {y : (ι × κ) × IntBasisIdx K → ℝ |
      ∀ x ∈ L, ∃ n : ℤ, y ⬝ᵥ (G *ᵥ x) = n} = ⊤ := by
    rw [eq_top_iff, ← hLspan, Submodule.span_le]
    intro z hz
    have hz' : z = (c₀ : ℝ)⁻¹ • ((c₀ : ℝ) • z) := by
      rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hc₀), one_smul]
    rw [hz']
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hcS z hz))

  have hdet : IsUnit (ratGram H b θ).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hvr : (fun j => (v j : ℝ)) ≠ 0 := by
      intro h
      apply hv0
      funext j
      simpa using congrFun h j
    have := hGpos _ hvr
    have hmv : G *ᵥ (fun j => (v j : ℝ)) = 0 := by
      funext j
      have h := congrFun hv j
      simp only [mulVec, dotProduct, Pi.zero_apply] at h
      simp only [hGdef, mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply]
      exact_mod_cast h
    rw [hmv, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hmin : ∀ y : (ι × κ) × IntBasisIdx K → ℝ, (∀ x ∈ L, ∃ n : ℤ, y ⬝ᵥ (G *ᵥ x) = n) → y ≠ 0 →
      μ ^ 2 ≤ y ⬝ᵥ (G *ᵥ y) := by
    intro y hy hy0
    have hGy : ∀ j, ∃ q : ℚ, (G *ᵥ y) j = q := by
      intro j
      obtain ⟨n, hn⟩ := hy _ (hsingle j)
      refine ⟨n / r, ?_⟩
      have h1 : y ⬝ᵥ (G *ᵥ Pi.single j (r : ℝ)) = (G *ᵥ y) j * r := by
        rw [dotProduct_mulVec, ← mulVec_transpose, hGs, dotProduct_comm]
        simp [dotProduct, Pi.single_apply]
        ring
      push_cast
      rw [eq_div_iff hr0', ← h1, hn]
    choose zq hzq using hGy
    set yq := (ratGram H b θ)⁻¹ *ᵥ zq
    have hyq : y = fun j => (yq j : ℝ) := by
      have h1 : G *ᵥ (fun j => (yq j : ℝ)) = fun j => (zq j : ℝ) := by
        have hz : ratGram H b θ *ᵥ yq = zq := by
          rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
        funext j
        have h := congrFun hz j
        simp only [mulVec, dotProduct] at h
        simp only [hGdef, mulVec, dotProduct, Matrix.map_apply]
        rw [← h]
        push_cast
        rfl
      by_contra hne
      have hd : y - (fun j => (yq j : ℝ)) ≠ 0 := sub_ne_zero.2 hne
      have := hGpos _ hd
      rw [mulVec_sub, h1, show G *ᵥ y = fun j => (zq j : ℝ) from funext hzq, sub_self,
        dotProduct_zero] at this
      exact lt_irrefl _ this
    set v := ofRatCoords b yq
    have hv : ratEmb b v = y := by
      rw [hyq]
      funext j
      simp [ratEmb, v, ratCoords_ofRatCoords]
    have hvint : ∀ x ∈ adelicLattice b H g, ∃ n : ℤ, ratForm H θ v x = n := by
      intro x hx
      obtain ⟨n, hn⟩ := hy (ratEmb b x) ((memL _).2 ⟨x, hx, rfl⟩)
      refine ⟨n, ?_⟩
      rw [← hv, hgram] at hn
      exact_mod_cast hn
    have hmv := hdual g v hvint
    have hv0 : v ≠ 0 := by
      rintro h
      apply hy0
      rw [← hv, h]
      funext j
      simp [ratEmb, ratCoords_zero]
    have hmv0 : (m : K) • v ≠ 0 := smul_ne_zero (by exact_mod_cast hm0) hv0
    have hpos := ratForm_self_pos b hreal hθ hmv0
    obtain ⟨n, hn⟩ := hQint g _ _ hmv hmv
    have hge : (1 : ℚ) ≤ |(c₀ : ℚ)| * ratForm H θ ((m : K) • v) ((m : K) • v) := by
      have hne : (c₀ : ℚ) * ratForm H θ ((m : K) • v) ((m : K) • v) ≠ 0 :=
        mul_ne_zero (by exact_mod_cast hc₀) hpos.ne'
      rw [hn] at hne
      have hn0 : n ≠ 0 := by exact_mod_cast hne
      have h1 : (1 : ℚ) ≤ |(n : ℚ)| := by exact_mod_cast Int.one_le_abs hn0
      rw [← hn, abs_mul, abs_of_pos hpos] at h1
      exact h1
    have hQm : ratForm H θ ((m : K) • v) ((m : K) • v) = (m : ℚ) ^ 2 * ratForm H θ v v := by
      rw [show (m : K) = ((m : ℚ) : K) by norm_cast, ratForm_ratSmul_left, ratForm_ratSmul_right]
      ring
    rw [hQm] at hge
    have hge' : (1 : ℝ) ≤ |(c₀ : ℝ)| * ((m : ℝ) ^ 2 * (ratForm H θ v v : ℝ)) := by
      have := (Rat.cast_le (K := ℝ)).2 hge
      push_cast at this
      exact this
    rw [← hv, hgram, hμdef, Real.sq_sqrt (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨e, hli, he⟩ := exists_short_basis_gram G hGs hGpos L μ hμ hLspan hDspan hmin
  choose x hx hxe using fun i => (memL (e i)).1 (he i).1
  refine ⟨x, hx, ?_, fun i => ?_⟩
  · have : (fun i => ratEmb b (x i)) = e := funext hxe
    rw [this]
    exact hli
  · rw [← hgram, hxe]
    exact (he i).2

end ShortBasis

section Coordinates

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι E}
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)

omit [DecidableEq ι] [DecidableEq κ] in
theorem card_fin_eq_finrank {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K)) :
    Fintype.card (Fin N) = finrank ℚ ((ι × κ) × IntBasisIdx K → ℚ) := by
  rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, hN]

omit [DecidableEq ι] in
theorem ratForm_sum_left' {ι' : Type*} (θ : K) (s : Finset ι') (v : ι' → ι → K ⊗[K] E)
    (y : ι → K ⊗[K] E) : ratForm H θ (∑ i ∈ s, v i) y = ∑ i ∈ s, ratForm H θ (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := ratForm_add_left (H := H) θ 0 0 y
    rw [add_zero] at this
    simp only [Finset.sum_empty]
    linarith
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ratForm_add_left, ih]

omit [DecidableEq ι] in
theorem ratForm_sum_right' {ι' : Type*} (θ : K) (s : Finset ι') (x : ι → K ⊗[K] E)
    (v : ι' → ι → K ⊗[K] E) : ratForm H θ x (∑ i ∈ s, v i) = ∑ i ∈ s, ratForm H θ x (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := ratForm_add_right (H := H) θ x 0 0
    rw [add_zero] at this
    simp only [Finset.sum_empty]
    linarith
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ratForm_add_right, ih]

def ratBasis {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K)) {x : Fin N → ι → K ⊗[K] E}
    (hli : LinearIndependent ℝ fun i => ratEmb b (x i)) :
    Basis (Fin N) ℚ ((ι × κ) × IntBasisIdx K → ℚ) :=
  basisOfCard (linearIndependent_ratCoords hli) (card_fin_eq_finrank hN)

omit [Algebra.IsQuadraticExtension K E] [DecidableEq ι] [DecidableEq κ] in
theorem ratBasis_apply {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K))
    {x : Fin N → ι → K ⊗[K] E} (hli : LinearIndependent ℝ fun i => ratEmb b (x i)) (i : Fin N) :
    ratBasis b hN hli i = ratCoords b (x i) :=
  basisOfCard_apply _ _ _

def basisCoords {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K)) {x : Fin N → ι → K ⊗[K] E}
    (hli : LinearIndependent ℝ fun i => ratEmb b (x i)) (y : ι → K ⊗[K] E) : Fin N → ℚ :=
  fun i => (ratBasis b hN hli).repr (ratCoords b y) i

omit [Algebra.IsQuadraticExtension K E] [DecidableEq ι] [DecidableEq κ] in
theorem eq_sum_basisCoords {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K))
    {x : Fin N → ι → K ⊗[K] E} (hli : LinearIndependent ℝ fun i => ratEmb b (x i))
    (y : ι → K ⊗[K] E) : y = ∑ i, (basisCoords b hN hli y i : K) • x i := by
  apply ratCoords_injective b
  rw [ratCoords_sum]
  simp only [ratCoords_smul, ← ratBasis_apply b hN hli, basisCoords]
  exact ((ratBasis b hN hli).sum_repr _).symm

omit [Algebra.IsQuadraticExtension K E] [DecidableEq ι] [DecidableEq κ] in
theorem basisCoords_sum {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K))
    {x : Fin N → ι → K ⊗[K] E} (hli : LinearIndependent ℝ fun i => ratEmb b (x i))
    (c : Fin N → ℚ) : basisCoords b hN hli (∑ i, (c i : K) • x i) = c := by
  funext i
  simp only [basisCoords, ratCoords_sum, ratCoords_smul, ← ratBasis_apply b hN hli]
  have : ∑ i, c i • ratBasis b hN hli i = (ratBasis b hN hli).equivFun.symm c :=
    (Basis.equivFun_symm_apply _ _).symm
  rw [this]
  exact congrFun ((ratBasis b hN hli).equivFun.apply_symm_apply c) i

omit [DecidableEq κ] in

theorem exists_int_factorial_mul_basisCoords (hreal : ∀ w : InfinitePlace K, w.IsReal) {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    {c₀ : ℤ} (hc₀ : c₀ ≠ 0) {L : AddSubgroup (ι → K ⊗[K] E)}
    (hQint : ∀ x ∈ L, ∀ y ∈ L, ∃ n : ℤ, (c₀ : ℚ) * ratForm H θ x y = n)
    {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K)) {x : Fin N → ι → K ⊗[K] E}
    (hli : LinearIndependent ℝ fun i => ratEmb b (x i)) (hxL : ∀ i, x i ∈ L) {M : ℚ}
    (hM : ∀ i j, |ratForm H θ (x i) (x j)| ≤ M) (y : ι → K ⊗[K] E) (hy : y ∈ L) (i : Fin N) :
    ∃ n : ℤ, ((N.factorial * ⌈|(c₀ : ℚ)| * M⌉₊ ^ N).factorial : ℚ) * basisCoords b hN hli y i = n := by
  classical
  choose Z hZ using fun (j i : Fin N) => hQint (x i) (hxL i) (x j) (hxL j)
  set Zm : Matrix (Fin N) (Fin N) ℤ := Matrix.of Z
  set c := basisCoords b hN hli y
  have hyc : y = ∑ i, (c i : K) • x i := eq_sum_basisCoords b hN hli y

  have hZc : ∀ j, ∃ m : ℤ, (Zm.map (Int.cast : ℤ → ℚ) *ᵥ c) j = m := by
    intro j
    obtain ⟨n, hn⟩ := hQint y hy (x j) (hxL j)
    refine ⟨n, ?_⟩
    rw [← hn]
    conv_rhs => rw [hyc, ratForm_sum_left', Finset.mul_sum]
    simp only [mulVec, dotProduct, Matrix.map_apply, Zm, Matrix.of_apply, ← hZ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ratForm_ratSmul_left]
    ring

  have hZ0 : Zm.det ≠ 0 := by
    intro h0
    have h0' : (Zm.map (Int.cast : ℤ → ℚ)).det = 0 := by
      have := RingHom.map_det (Int.castRingHom ℚ) Zm
      rw [h0, map_zero] at this
      simpa [RingHom.mapMatrix_apply] using this.symm
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0'
    set u := ∑ i, (v i : K) • x i
    have hu : ∀ j, ratForm H θ u (x j) = 0 := by
      intro j
      have h := congrFun hv j
      simp only [mulVec, dotProduct, Matrix.map_apply, Zm, Matrix.of_apply, ← hZ,
        Pi.zero_apply] at h
      have : (c₀ : ℚ) * ratForm H θ u (x j) = 0 := by
        rw [ratForm_sum_left', Finset.mul_sum, ← h]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ratForm_ratSmul_left]
        ring
      exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hc₀)
    have huu : ratForm H θ u u = 0 := by
      conv_lhs => arg 4; rw [show u = ∑ i, (v i : K) • x i from rfl]
      rw [ratForm_sum_right']
      exact Finset.sum_eq_zero fun j _ => by rw [ratForm_ratSmul_right, hu, mul_zero]
    have hu0 : u = 0 := by
      by_contra hne
      have := ratForm_self_pos b hreal hθ hne
      linarith
    apply hv0
    have hc := basisCoords_sum b hN hli v
    rw [show ∑ i, ((v i : ℚ) : K) • x i = u from rfl, hu0] at hc
    rw [← hc]
    funext i
    simp [basisCoords, ratCoords_zero]

  have hZb : Zm.det.natAbs ≤ N.factorial * ⌈|(c₀ : ℚ)| * M⌉₊ ^ N := by
    have hentry : ∀ j i, |Zm j i| ≤ (⌈|(c₀ : ℚ)| * M⌉₊ : ℤ) := by
      intro j i
      have h1 : ((|Zm j i| : ℤ) : ℚ) = |(c₀ : ℚ)| * |ratForm H θ (x i) (x j)| := by
        simp only [Zm, Matrix.of_apply, Int.cast_abs, ← hZ, abs_mul]
      have h2 : |(c₀ : ℚ)| * |ratForm H θ (x i) (x j)| ≤ |(c₀ : ℚ)| * M :=
        mul_le_mul_of_nonneg_left (hM i j) (abs_nonneg _)
      have h3 : |(c₀ : ℚ)| * M ≤ (⌈|(c₀ : ℚ)| * M⌉₊ : ℚ) := Nat.le_ceil _
      have : ((|Zm j i| : ℤ) : ℚ) ≤ ((⌈|(c₀ : ℚ)| * M⌉₊ : ℤ) : ℚ) := by
        rw [h1]; push_cast; linarith
      exact_mod_cast this
    have hdet := Matrix.det_le (abv := AbsoluteValue.abs) (A := Zm) hentry
    rw [Fintype.card_fin] at hdet
    have : (Zm.det.natAbs : ℤ) ≤ ((N.factorial * ⌈|(c₀ : ℚ)| * M⌉₊ ^ N : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      simpa [nsmul_eq_mul] using hdet
    exact_mod_cast this
  exact exists_int_factorial_mul_of_mulVec Zm hZ0 _ hZb c hZc i

end Coordinates

section EBound

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι E}
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

omit [NumberField K] in

theorem conjBase_mul_self_algebraMap_mul (ω : K) (e : E) :
    conjBase K E K (algebraMap K (K ⊗[K] E) ω * (1 ⊗ₜ[K] e)) *
        (algebraMap K (K ⊗[K] E) ω * (1 ⊗ₜ[K] e)) =
      algebraMap K (K ⊗[K] E) (ω ^ 2 * Algebra.norm K e) := by
  rw [map_mul, conjBase_algebraMap, conjBase_tmul, map_mul, map_pow,
    Algebra.TensorProduct.algebraMap_apply' (Algebra.norm K e), ← mul_conj]
  have h2 : (1 : K) ⊗ₜ[K] (e * conj K E e) = ((1 : K) ⊗ₜ[K] e) * (1 ⊗ₜ[K] conj K E e) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [h2]
  ring

omit [NumberField K] [DecidableEq ι] in
theorem hermTrace_smul_smul_of {z : K ⊗[K] E} {n : K}
    (hz : conjBase K E K z * z = algebraMap K (K ⊗[K] E) n) (x : ι → K ⊗[K] E) :
    hermTrace K H K (z • x) (z • x) = n * hermTrace K H K x x := by
  rw [hermTrace, hermPair_smul_smul, hz, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rfl

theorem ratForm_smul_smul_le (hreal : ∀ w : InfinitePlace K, w.IsReal) {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    {z : K ⊗[K] E} {n : K} (hz : conjBase K E K z * z = algebraMap K (K ⊗[K] E) n)
    (x : ι → K ⊗[K] E) :
    (ratForm H θ (z • x) (z • x) : ℝ) ≤ (∑ w, |realEmb hreal w n|) * ratForm H θ x x := by
  rw [ratForm, ratForm, hermTrace_smul_smul_of hz, trace_eq_sum_realEmb hreal,
    trace_eq_sum_realEmb hreal, Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  have h0 : 0 ≤ realEmb hreal w (θ * hermTrace K H K x x) :=
    realEmb_mul_hermTrace_nonneg (b := b) hθ (hreal w) x
  rw [show θ * (n * hermTrace K H K x x) = n * (θ * hermTrace K H K x x) by ring, map_mul]
  have h1 : realEmb hreal w n ≤ ∑ w', |realEmb hreal w' n| :=
    (le_abs_self _).trans (Finset.single_le_sum (f := fun w' => |realEmb hreal w' n|)
      (fun w' _ => abs_nonneg _) (Finset.mem_univ w))
  nlinarith

end EBound

end GroundTheory.Automorphic

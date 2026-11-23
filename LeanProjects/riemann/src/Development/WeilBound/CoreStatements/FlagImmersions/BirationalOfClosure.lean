import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionReindexed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogRelationRatioReindex
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnitRatioDivisorSupportEq
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero

noncomputable section

namespace RootFieldNumerics.Ref.Zeros

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open GlobalTheory.CompanionTheory.Ar.Chg GlobalTheory.CompanionTheory.Ar.Chg.DegBlock
open GroundTheory.Heights₂.Heights.LowerBoundFree (mem_mCoordIdeal_of_aeval_eq_zero)
open GlobalTheory.CompanionTheory.Ar.Giv (aeval_eq_zero_of_mem_mCoordIdeal)

variable {K₀ K : Type} [Fintype K₀] [Fintype K] {J₀ : K₀ → Type} {J : K → Type} [∀ k, Fintype (J₀ k)]
  [∀ k, Fintype (J k)]

theorem homog_add {f g : MRing J} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem homog_neg {f : MRing J} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm k

theorem homog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing J) a := by
  intro m hm
  simp at hm

theorem homog_sum {X : Type} (s : Finset X) {f : X → MRing J} {a : K → ℕ} (h : ∀ x ∈ s, IsMultiHomog (f x) a) :
    IsMultiHomog (∑ x ∈ s, f x) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using homog_zero a
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact homog_add (h x (Finset.mem_insert_self x s)) (ih fun u hu => h u (Finset.mem_insert_of_mem hu))

theorem homog_pow {f : MRing J} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) : IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (isMultiHomog_one' (J₀ := J))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul' ih hf

theorem homog_X [DecidableEq K] (k : K) (i : J k) : IsMultiHomog (X ⟨k, i⟩ : MRing J) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg]
      intro e
      exact hb (eq_of_heq (Sigma.mk.inj e).2).symm
    · simp
  · rw [Pi.single_eq_of_ne h]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro e
    exact h (Sigma.mk.inj e).1.symm

theorem homog_mono (c : ∀ k, J k) (a : K → ℕ) : IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing J) ^ a k) a := by
  classical
  have h := isMultiHomog_prod' (J₀ := J) Finset.univ (f := fun k => (X ⟨k, c k⟩ : MRing J) ^ a k)
    (a := fun k => a k • Pi.single k 1) fun k _ => homog_pow (homog_X k (c k)) (a k)
  convert h using 1
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem exists_blkV {κ : K₀ → K} {v : (Σ k, J₀ k) → Σ k, J k} (hv : IsBlockMap κ v) :
    ∃ bx : ∀ k, J₀ k ≃ J (κ k), v = blkV κ bx := by
  have hq : ∀ k (i : J₀ k), ∃ i' : J (κ k), v ⟨k, i⟩ = ⟨κ k, i'⟩ := by
    intro k i
    have h1 := hv.2.2.1 ⟨k, i⟩
    generalize v ⟨k, i⟩ = q at h1
    obtain ⟨q1, q2⟩ := q
    simp only at h1
    subst h1
    exact ⟨q2, rfl⟩
  choose g hg using hq
  have hb : ∀ k, Function.Bijective (g k) := by
    intro k
    constructor
    · intro a b hab
      have : v ⟨k, a⟩ = v ⟨k, b⟩ := by rw [hg, hg, hab]
      exact eq_of_heq (Sigma.mk.inj (hv.2.1 this)).2
    · intro i'
      obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
      have h1 : κ p.1 = κ k := by rw [← hv.2.2.1 p, hp]
      obtain ⟨k₁, i⟩ := p
      obtain rfl : k₁ = k := hv.1 h1
      refine ⟨i, ?_⟩
      rw [hg] at hp
      exact eq_of_heq (Sigma.mk.inj hp).2
  refine ⟨fun k => Equiv.ofBijective (g k) (hb k), ?_⟩
  funext p
  obtain ⟨k, i⟩ := p
  exact hg k i

theorem common_den {Ω₀ : Type} [Field Ω₀] (y₀ : (Σ k, J₀ k) → Ω₀) (hB : Birational y₀) (b : ℕ → Ω₀) (n : ℕ) :
    ∃ (c : ℕ → MRing J₀) (a : K₀ → ℕ) (H : Ω₀), H ≠ 0 ∧ ∀ j ∈ Finset.range n,
      IsMultiHomog (c j) a ∧ aeval y₀ (c j) = b j * H := by
  classical
  choose d g h hg hh h0 he using fun j => hB (b j)
  refine ⟨fun j => g j * ∏ k ∈ (Finset.range n).erase j, h k, ∑ k ∈ Finset.range n, d k,
    ∏ k ∈ Finset.range n, aeval y₀ (h k), Finset.prod_ne_zero_iff.2 fun k _ => h0 k, fun j hj => ⟨?_, ?_⟩⟩
  · rw [← Finset.add_sum_erase _ _ hj]
    exact isMultiHomog_mul' (hg j) (isMultiHomog_prod' _ fun k _ => hh k)
  · rw [← Finset.mul_prod_erase _ _ hj, map_mul, map_prod, he, mul_assoc]

theorem zeros_proj {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (i : Ω₀ →+* Ω)
    {κ : K₀ → K} {v : (Σ k, J₀ k) → Σ k, J k} (hv : IsBlockMap κ v) (hy : ∀ p, y (v p) = i (y₀ p))
    (hB : Birational y₀) (halg : ∀ α : Ω, (letI := i.toAlgebra; IsAlgebraic Ω₀ α))
    {F : MRing J} {aF : K → ℕ} (hF : IsMultiHomog F aF) (hFP : F ∉ mCoordIdeal y) :
    ∃ (G : MRing J₀) (b : K₀ → ℕ), IsMultiHomog G b ∧ aeval y₀ G ≠ 0 ∧
      ∀ z ∈ mcPts (mCoordIdeal y), eval z (map (Int.castRingHom ℂ) F) = 0 →
        eval (fun p => z (v p)) (map (Int.castRingHom ℂ) G) = 0 := by
  classical
  letI := i.toAlgebra
  have hFy : aeval y F ≠ 0 := fun h => hFP (mem_mCoordIdeal_of_aeval_eq_zero y hF h)
  have hren : ∀ g : MRing J₀, aeval y (rename v g) = i (aeval y₀ g) := by
    intro g
    rw [aeval_rename, ← GlobalTheory.CompanionTheory.Ar.Rel.aeval_comp_ringHom i y₀ g]
    congr 2
    funext p
    exact hy p
  have key : ∀ c : ∀ k, J k, ∃ (G : MRing J₀) (b : K₀ → ℕ), IsMultiHomog G b ∧ aeval y₀ G ≠ 0 ∧
      ∀ z ∈ mcPts (mCoordIdeal y), (∀ k, z ⟨k, c k⟩ ≠ 0) → eval z (map (Int.castRingHom ℂ) F) = 0 →
        eval (fun p => z (v p)) (map (Int.castRingHom ℂ) G) = 0 := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · let M : MRing J := ∏ k, (X ⟨k, c k⟩ : MRing J) ^ aF k
      have hM : IsMultiHomog M aF := homog_mono c aF
      have hMy : aeval y M ≠ 0 := by
        simp only [M, map_prod, map_pow, aeval_X]
        exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
      set α : Ω := aeval y F / aeval y M with hα
      have hα0 : α ≠ 0 := div_ne_zero hFy hMy
      have hint : IsIntegral Ω₀ α := (halg α).isIntegral
      set p := minpoly Ω₀ α with hp
      have hp0 : p.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hα0
      have hpa : Polynomial.aeval α p = 0 := minpoly.aeval Ω₀ α
      rw [Polynomial.aeval_eq_sum_range] at hpa
      set n := p.natDegree
      obtain ⟨cc, a, H, hH, hcc⟩ := common_den y₀ hB (fun j => p.coeff j) (n + 1)
      have h0n : 0 ∈ Finset.range (n + 1) := by simp
      refine ⟨cc 0, a, (hcc 0 h0n).1, by rw [(hcc 0 h0n).2]; exact mul_ne_zero hp0 hH, ?_⟩
      intro z hz hzc hFz
      let Φ : MRing J := ∑ j ∈ Finset.range (n + 1), rename v (cc j) * F ^ j * M ^ (n - j)
      have hΦh : IsMultiHomog Φ (Function.extend κ a 0 + n • aF) := by
        refine homog_sum _ fun j hj => ?_
        have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        have h1 := isMultiHomog_mul' (isMultiHomog_mul' (isMultiHomog_rename' hv (hcc j hj).1) (homog_pow hF j))
          (homog_pow hM (n - j))
        convert h1 using 1
        rw [add_assoc, ← add_nsmul, Nat.add_sub_cancel' hjn]
      have hΦy : aeval y Φ = 0 := by
        have hterm : ∀ j ∈ Finset.range (n + 1), aeval y (rename v (cc j) * F ^ j * M ^ (n - j)) =
            (i H * aeval y M ^ n) * (p.coeff j • α ^ j) := by
          intro j hj
          have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
          rw [map_mul, map_mul, map_pow, map_pow, hren, (hcc j hj).2, mul_assoc,
            GlobalTheory.CompanionTheory.Ar.Rel.pow_mul_pow_sub_eq _ _ hMy hjn, Algebra.smul_def, map_mul]
          show _ = _ * (i (p.coeff j) * α ^ j)
          ring
        simp only [Φ, map_sum]
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hpa, mul_zero]
      have hev := hz.2 Φ (mem_mCoordIdeal_of_aeval_eq_zero y hΦh hΦy)
      simp only [Φ, map_sum, map_mul, map_pow, hFz] at hev
      rw [Finset.sum_eq_single 0 (fun j _ hj => by simp [hj]) (by simp), eval_map_rename'] at hev
      have hMz : eval z (map (Int.castRingHom ℂ) M) ≠ 0 := by
        simp only [M, map_prod, map_pow, map_X, eval_X]
        exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hzc k)
      rw [pow_zero, mul_one] at hev
      exact (mul_eq_zero.1 hev).resolve_right (pow_ne_zero _ hMz)
    · refine ⟨1, 0, isMultiHomog_one', by simp, fun z hz hzc _ => ?_⟩
      exfalso
      apply hc
      intro k h
      apply hzc k
      have hm : (X ⟨k, c k⟩ : MRing J) ∈ mCoordIdeal y := by
        show mConeMap y (X _) = 0
        simp [mConeMap, h]
      simpa using hz.2 _ hm
  choose G b hG hGy hz using key
  refine ⟨∏ c, G c, ∑ c, b c, isMultiHomog_prod' _ fun c _ => hG c, ?_, fun z hzP hFz => ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun c _ => hGy c
  · choose c hc using hzP.1
    rw [map_prod, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ c) (hz c z hzP hc hFz)

theorem birational_of_closure {Ω : Type} [Field Ω] {n : ℕ} (yf : Fin n → Ω)
    (hgen : Subfield.closure (Set.range fun ij : Fin n × Fin n => yf ij.1 / yf ij.2) = ⊤) :
    Birational (ι := fun _ : Unit => Fin n) fun p => yf p.2 := by
  classical
  intro s
  have hs : s ∈ Subfield.closure (Set.range fun ij : Fin n × Fin n => yf ij.1 / yf ij.2) := by
    rw [hgen]; trivial
  induction hs using Subfield.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    by_cases hb : yf b = 0
    · exact ⟨0, 0, 1, homog_zero _, isMultiHomog_one', by simp, by simp [hb]⟩
    · exact ⟨Pi.single () 1, X ⟨(), a⟩, X ⟨(), b⟩, homog_X _ _, homog_X _ _, by simpa using hb, by simp [hb]⟩
  | one => exact ⟨0, 1, 1, isMultiHomog_one', isMultiHomog_one', by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, g, h, hg, hh, h0, he⟩ := hx
    obtain ⟨d', g', h', hg', hh', h0', he'⟩ := hy
    refine ⟨d + d', g * h' + h * g', h * h', homog_add (isMultiHomog_mul' hg hh') (isMultiHomog_mul' hh hg'),
      isMultiHomog_mul' hh hh', by rw [map_mul]; exact mul_ne_zero h0 h0', ?_⟩
    simp only [map_add, map_mul, he, he']
    ring
  | neg x _ hx =>
    obtain ⟨d, g, h, hg, hh, h0, he⟩ := hx
    exact ⟨d, -g, h, homog_neg hg, hh, h0, by rw [map_neg, he]; ring⟩
  | inv x _ hx =>
    obtain ⟨d, g, h, hg, hh, h0, he⟩ := hx
    by_cases hx0 : x = 0
    · exact ⟨0, 0, 1, homog_zero _, isMultiHomog_one', by simp, by simp [hx0]⟩
    · refine ⟨d, h, g, hh, hg, by rw [he]; exact mul_ne_zero hx0 h0, ?_⟩
      rw [he]
      field_simp
  | mul x y _ _ hx hy =>
    obtain ⟨d, g, h, hg, hh, h0, he⟩ := hx
    obtain ⟨d', g', h', hg', hh', h0', he'⟩ := hy
    refine ⟨d + d', g * g', h * h', isMultiHomog_mul' hg hg',
      isMultiHomog_mul' hh hh', by rw [map_mul]; exact mul_ne_zero h0 h0', ?_⟩
    simp only [map_mul, he, he']
    ring

end RootFieldNumerics.Ref.Zeros

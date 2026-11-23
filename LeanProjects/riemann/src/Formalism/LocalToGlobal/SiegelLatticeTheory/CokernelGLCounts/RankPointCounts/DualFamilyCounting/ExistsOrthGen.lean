import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOrthTuple

noncomputable section

namespace Formalism.L2.SG.Pf.G1

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K}

theorem det_mem {h : V →ₗ⋆[K] V →ₗ[K] K} {n : ℕ} (x : Fin n → V) (hx : ∀ i j, h (x i) (x j) ∈ S) :
    (U0.gram h x).det ∈ S := by
  have key := RingHom.map_det S.subtype (Matrix.of fun i j => (⟨h (x i) (x j), hx i j⟩ : S))
  have e : S.subtype.mapMatrix (Matrix.of fun i j => (⟨h (x i) (x j), hx i j⟩ : S)) = U0.gram h x := by
    ext i j
    rfl
  rw [e] at key
  rw [← key]
  exact Subtype.mem _

theorem smul_apply' (h : V →ₗ⋆[K] V →ₗ[K] K) (c : K) (x y : V) : (c • h) x y = c * h x y := by
  simp only [LinearMap.smul_apply, smul_eq_mul]

theorem isSymm_smul {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {c : K} (hc : star c = c) :
    (c • h).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [smul_apply', smul_apply', map_mul, hs.eq x y, starRingEnd_apply, hc]

theorem exists_orth_gen (hS : IsHermSemilocal S) (hπ : IsUnif S π) :
    ∀ (n N : ℕ) (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → ∀ x : Fin n → V, (∀ i j, h (x i) (x j) ∈ S) →
      (U0.gram h x).det * π⁻¹ ^ N ∉ S →
      ∃ y : Fin n → V, (∀ i j, i ≠ j → h (y i) (y j) = 0) ∧ spanS S y = spanS S x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
  intro h hs x hx hdet
  obtain _ | m := n
  · exact ⟨x, fun i => i.elim0, rfl⟩
  have hπ0 : π ≠ 0 := hπ.ne
  by_cases hall : ∀ i j, Dv S π (h (x i) (x j))
  ·
    have hc : star (π⁻¹) = π⁻¹ := by rw [star_inv₀, hπ.fix]
    have hs' : (π⁻¹ • h).IsSymm := isSymm_smul hs hc
    have hx' : ∀ i j, (π⁻¹ • h) (x i) (x j) ∈ S := by
      intro i j
      rw [smul_apply', mul_comm]
      exact hall i j
    have hgram : U0.gram (π⁻¹ • h) x = π⁻¹ • U0.gram h x := by
      ext i j
      simp only [U0.gram, Matrix.of_apply, Matrix.smul_apply, smul_apply', smul_eq_mul]
    have hdet' : (U0.gram (π⁻¹ • h) x).det = π⁻¹ ^ (m + 1) * (U0.gram h x).det := by
      rw [hgram, Matrix.det_smul, Fintype.card_fin]
    have hmem' : (U0.gram (π⁻¹ • h) x).det ∈ S := det_mem x hx'
    have hN : m + 1 ≤ N := by
      by_contra hlt
      push_neg at hlt
      apply hdet
      have hd : (U0.gram h x).det = π ^ (m + 1) * (U0.gram (π⁻¹ • h) x).det := by
        rw [hdet', ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hπ0, one_pow, one_mul]
      have hp : π ^ (m + 1) * π⁻¹ ^ N = π ^ (m + 1 - N) := by
        rw [pow_sub₀ π hπ0 hlt.le, inv_pow]
      rw [hd, mul_comm (π ^ (m + 1)) _, mul_assoc, hp]
      exact S.mul_mem hmem' (S.pow_mem hπ.mem _)
    have hlt : N - (m + 1) < N := by omega
    have hdet2 : (U0.gram (π⁻¹ • h) x).det * π⁻¹ ^ (N - (m + 1)) ∉ S := by
      rwa [hdet', mul_comm (π⁻¹ ^ (m + 1)), mul_assoc, ← pow_add, Nat.add_sub_cancel' hN]
    obtain ⟨y, hyo, hys⟩ := ihN (N - (m + 1)) hlt (π⁻¹ • h) hs' x hx' hdet2
    refine ⟨y, fun i j hij => ?_, hys⟩
    have h0 := hyo i j hij
    rw [smul_apply'] at h0
    exact (mul_eq_zero.mp h0).resolve_left (inv_ne_zero hπ0)
  ·
    push_neg at hall
    obtain ⟨i₀, r, hr, hu⟩ := exists_pivot hS hπ hs x hx hall
    generalize hf : x i₀ + r = f at hu
    obtain ⟨ha0, haS, hainv⟩ := hu
    have hsub : spanS S (x ∘ i₀.succAbove) ≤ spanS S x := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      exact mem_spanS x _
    have hfx : f ∈ spanS S x := by
      rw [← hf]
      exact Submodule.add_mem _ (mem_spanS x i₀) (hsub hr)
    have hint := int_spanS hS hx
    obtain ⟨c, hc⟩ : ∃ c : Fin m → K, ∀ k, c k = (h f f)⁻¹ * h f (x (i₀.succAbove k)) :=
      ⟨_, fun _ => rfl⟩
    have hcS : ∀ k, c k ∈ S := by
      intro k
      rw [hc k]
      exact S.mul_mem hainv (hint f hfx _ (mem_spanS x _))
    obtain ⟨y, hy⟩ : ∃ y : Fin m → V, ∀ k, y k = x (i₀.succAbove k) - c k • f :=
      ⟨_, fun _ => rfl⟩
    have hf0 : ∀ k, h f (y k) = 0 := by
      intro k
      rw [hy k, map_sub, map_smul, smul_eq_mul, hc k, mul_comm (h f f)⁻¹, mul_assoc,
        inv_mul_cancel₀ ha0, mul_one, sub_self]
    have hyx : ∀ k, y k ∈ spanS S x := by
      intro k
      rw [hy k]
      exact Submodule.sub_mem _ (mem_spanS x _) (smul_mem_spanS (hcS k) hfx)
    have hyS : ∀ i j, h (y i) (y j) ∈ S := fun i j => hint _ (hyx i) _ (hyx j)
    have hfP : f ∈ spanS S (Fin.cons f y : Fin (m + 1) → V) := by
      have h1 := mem_spanS (S := S) (Fin.cons f y : Fin (m + 1) → V) 0
      rwa [Fin.cons_zero] at h1
    have hyP : ∀ k, y k ∈ spanS S (Fin.cons f y : Fin (m + 1) → V) := by
      intro k
      have h1 := mem_spanS (S := S) (Fin.cons f y : Fin (m + 1) → V) k.succ
      rwa [Fin.cons_succ] at h1
    have hxP : ∀ k, x (i₀.succAbove k) ∈ spanS S (Fin.cons f y : Fin (m + 1) → V) := by
      intro k
      rw [show x (i₀.succAbove k) = y k + c k • f by rw [hy k, sub_add_cancel]]
      exact Submodule.add_mem _ (hyP k) (smul_mem_spanS (hcS k) hfP)
    have hrP : r ∈ spanS S (Fin.cons f y : Fin (m + 1) → V) := by
      refine (Submodule.span_le.mpr ?_ : spanS S (x ∘ i₀.succAbove) ≤ _) hr
      rintro _ ⟨k, rfl⟩
      exact hxP k
    have hspan : spanS S (Fin.cons f y : Fin (m + 1) → V) = spanS S x := by
      apply le_antisymm
      · refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        induction i using Fin.cases with
        | zero => simpa only [Fin.cons_zero, SetLike.mem_coe] using hfx
        | succ k => simpa only [Fin.cons_succ, SetLike.mem_coe] using hyx k
      · refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        by_cases hi : i = i₀
        · subst hi
          rw [show x i = f - r by rw [← hf, add_sub_cancel_right]]
          exact Submodule.sub_mem _ hfP hrP
        · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
          exact hxP k
    have hdety : (U0.gram h y).det * π⁻¹ ^ N ∉ S := by
      intro hmem
      apply hdet
      obtain ⟨e, heS, he⟩ := gram_det_of_le (h := h) hS (x := x)
        (y := (Fin.cons f y : Fin (m + 1) → V)) (fun i => by rw [hspan]; exact mem_spanS x i)
      rw [he, gram_det_cons hs f y hf0, mul_assoc, mul_assoc]
      exact S.mul_mem heS (S.mul_mem haS hmem)
    obtain ⟨z, hzo, hzs⟩ := ihn m (Nat.lt_succ_self m) N h hs y hyS hdety
    have hfz : ∀ k, h f (z k) = 0 := by
      intro k
      have hzk : z k ∈ spanS S y := by
        rw [← hzs]
        exact mem_spanS z k
      exact spanS_induction (x := y) (p := fun v => h f v = 0) (map_zero _)
        (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
        (fun c _ a ha => by rw [map_smul, ha, smul_zero]) hf0 (z k) hzk
    refine ⟨(Fin.cons f z : Fin (m + 1) → V), ?_, ?_⟩
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ l =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact hfz l
      | succ k =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [← hs.eq f (z k), hfz k, map_zero]
        | succ l =>
          simp only [Fin.cons_succ]
          exact hzo k l (fun hkl => hij (by rw [hkl]))
    · rw [spanS_cons, hzs, ← spanS_cons, hspan]

end Formalism.L2.SG.Pf.G1

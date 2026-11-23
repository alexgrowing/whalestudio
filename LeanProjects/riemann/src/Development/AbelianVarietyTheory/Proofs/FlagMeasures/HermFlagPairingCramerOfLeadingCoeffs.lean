import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfForall
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open Formalism.MainNotions.S.Loc

namespace GlobalTheory.DegCnt.BlockMinor

variable {K : Type} [Field K]

def minor (bs : List (Kˣ × ℕ+)) (m : ℕ) : K := (Matrix.of fun a b : Fin m => ptEntryL bs a b).det

theorem entry_symm (bs : List (Kˣ × ℕ+)) (a b : ℕ) : ptEntryL bs a b = ptEntryL bs b a := by
  induction bs generalizing a b with
  | nil => rfl
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    simp only [ptEntryL, ih (a - s), and_comm, add_comm a b]

theorem det_anti (t : K) (s : ℕ) : ∃ ε : ℤˣ,
    (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0).det = ((ε : ℤ) : K) * t ^ s := by
  refine ⟨Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)), ?_⟩
  have : (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0) =
      (Matrix.diagonal fun _ : Fin s => t).submatrix (Fin.revPerm : Equiv.Perm (Fin s)) id := by
    ext a b
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.diagonal_apply, Fin.revPerm_apply, id, Fin.ext_iff,
      Fin.val_rev]
    have := a.2
    exact if_congr (by omega) rfl rfl
  rw [this, Matrix.det_permute]
  simp

theorem minor_cons (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) (m : ℕ) : ∃ ε : ℤˣ,
    minor ((t, s) :: bs) (s + m) = ((ε : ℤ) : K) * (t : K) ^ (s : ℕ) * minor bs m := by
  obtain ⟨ε, hε⟩ := det_anti (t : K) s
  refine ⟨ε, ?_⟩
  unfold minor
  rw [← hε, ← Matrix.det_fromBlocks_zero₂₁ _ (0 : Matrix (Fin s) (Fin m) K),
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  congr 1
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [ptEntryL]

theorem exists_block (bs : List (Kˣ × ℕ+)) (a : ℕ) (ha : a < (bs.map fun b => (b.2 : ℕ)).sum) :
    ∃ (l s : ℕ) (t : Kˣ) (ε : ℤˣ), l ≤ a ∧ a < l + s ∧ l + s ≤ (bs.map fun b => (b.2 : ℕ)).sum ∧
      (∀ b, ptEntryL bs a b = if a + b + 1 = l + (l + s) then (t : K) else 0) ∧ minor bs l ≠ 0 ∧
      minor bs (l + s) = ((ε : ℤ) : K) * (t : K) ^ s * minor bs l := by
  induction bs generalizing a with
  | nil => simp at ha
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    simp only [List.map_cons, List.sum_cons] at ha ⊢
    by_cases h : a < s
    · obtain ⟨ε, hε⟩ := minor_cons t s bs 0
      refine ⟨0, s, t, ε, by omega, by omega, by omega, fun b => ?_, by simp [minor], ?_⟩
      · simp only [ptEntryL]
        split_ifs <;> first | rfl | omega
      · rw [add_comm, hε]
        simp [minor]
    · obtain ⟨l, s', t', ε, h1, h2, h3, h4, h5, h6⟩ := ih (a - s) (by omega)
      obtain ⟨ε₁, h7⟩ := minor_cons t s bs l
      obtain ⟨ε₂, h8⟩ := minor_cons t s bs (l + s')
      refine ⟨s + l, s', t', ε₂ * ε * ε₁, by omega, by omega, by omega, fun b => ?_, ?_, ?_⟩
      · simp only [ptEntryL, h4]
        split_ifs <;> first | rfl | omega
      · rw [h7]
        refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ t.ne_zero)) h5
        rcases Int.units_eq_one_or ε₁ with h | h <;> simp [h]
      · rw [add_assoc, h8, h7, h6]
        have : ((ε₁ : ℤ) : K) * ((ε₁ : ℤ) : K) = 1 := by
          rw [← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]
        push_cast
        linear_combination (-(((ε₂ : ℤ) : K) * (t : K) ^ (s : ℕ) * (((ε : ℤ) : K) * (t' : K) ^ s' * minor bs l))) * this

theorem minor_full (bs : List (Kˣ × ℕ+)) : minor bs (bs.map fun b => (b.2 : ℕ)).sum ≠ 0 := by
  induction bs with
  | nil =>
    show minor ([] : List (Kˣ × ℕ+)) 0 ≠ 0
    simp [minor]
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    obtain ⟨ε, hε⟩ := minor_cons t s bs (bs.map fun b => (b.2 : ℕ)).sum
    simp only [List.map_cons, List.sum_cons]
    rw [hε]
    refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ t.ne_zero)) ih
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]

theorem exists_entry (bs : List (Kˣ × ℕ+)) (a : ℕ) (ha : a < (bs.map fun b => (b.2 : ℕ)).sum) :
    ∃ b < (bs.map fun b => (b.2 : ℕ)).sum, ptEntryL bs a b ≠ 0 ∧ ∀ a', ptEntryL bs a' b ≠ 0 → a' = a := by
  obtain ⟨l, s, t, ε, h1, h2, h3, h4, -⟩ := exists_block bs a ha
  have hb : l + (l + s) - a - 1 < (bs.map fun b => (b.2 : ℕ)).sum := by omega
  have h5 : ptEntryL bs a (l + (l + s) - a - 1) ≠ 0 := by
    rw [h4, if_pos (by omega)]; exact t.ne_zero
  refine ⟨_, hb, h5, fun a' h6 => ?_⟩
  obtain ⟨l', s', t', ε', -, -, -, h7, -⟩ := exists_block bs _ hb
  rw [entry_symm, h7] at h5 h6
  have h8 := of_not_not (mt (fun h => if_neg h) h5)
  have h9 := of_not_not (mt (fun h => if_neg h) h6)
  omega

end GlobalTheory.DegCnt.BlockMinor

namespace GlobalTheory.DegCnt.FrameCramer

open Matrix

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem exists_coord (F : FlagD H r) {l : ℕ} (hl : l ≤ r) {m : ℕ} (hm : m ≤ l) {x : V} (hx : x ∈ F.Xa m) :
    ∃ c : Fin l → K, (∀ b : Fin l, m ≤ b.val → c b = 0) ∧
      x = ∑ b, c b • F.e (Fin.castLE (hl.trans (Nat.le_succ r)) b) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hb' : b.val < m := hb
    refine ⟨Pi.single ⟨b.val, by omega⟩ 1, fun c hc => Pi.single_eq_of_ne (fun h => ?_) _, ?_⟩
    · rw [h] at hc; simp at hc; omega
    · rw [Finset.sum_eq_single ⟨b.val, by omega⟩]
      · simp; rfl
      · intro c _ hc; simp [Pi.single_eq_of_ne hc]
      · simp
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨c + d, fun b hb => by simp [hc b hb, hd b hb], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul t x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨t • c, fun b hb => by simp [hc b hb], by simp [Finset.smul_sum, smul_smul]⟩

theorem e_mem (F : FlagD H r) {l : ℕ} (hl : l ≤ r) (b : Fin l) :
    F.e (Fin.castLE (hl.trans (Nat.le_succ r)) b) ∈ F.Xa l :=
  Submodule.subset_span ⟨Fin.castLE hl b, b.2, rfl⟩

variable [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_tri (F : FlagD H r) (Λ : Submodule (𝓞 K) V) {l : ℕ} (hl : l ≤ r) (α : Fin l → K)
    (hα : ∀ a, α a ∈ lead F Λ (Fin.castLE hl a).castSucc) :
    ∃ A : Matrix (Fin l) (Fin l) K, A.det = ∏ a, α a ∧
      ∀ a, ∑ b, A a b • F.e (Fin.castLE (hl.trans (Nat.le_succ r)) b) ∈ Λ := by
  have h : ∀ a : Fin l, ∃ c : Fin l → K, (∀ b : Fin l, a.val ≤ b.val → c b = 0) ∧
      α a • F.e (Fin.castLE (hl.trans (Nat.le_succ r)) a) -
        ∑ b, c b • F.e (Fin.castLE (hl.trans (Nat.le_succ r)) b) ∈ Λ := by
    intro a
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hα a)
    obtain ⟨c, hc, rfl⟩ := exists_coord F hl (m := a.val) a.2.le hy
    refine ⟨c, hc, ?_⟩
    convert hx using 1
    rw [sub_eq_iff_eq_add]
    exact hxy.symm
  choose c hc hc' using h
  refine ⟨diagonal α - Matrix.of c, ?_, fun a => ?_⟩
  · rw [Matrix.det_of_lowerTriangular]
    · simp [hc]
    · intro a b hab
      have hab' : a < b := hab
      simp [hab'.ne, hc a b hab'.le]
  · convert hc' a using 1
    simp [sub_smul, Finset.sum_sub_distrib, diagonal_apply, ite_smul]

theorem hermFlag_pairing_cramer_of_leadingCoeffs (F F' : FlagD H r) (Λ : Submodule (𝓞 K) V)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K)) {l : ℕ} (hl : l ≤ r) (α β : Fin l → K)
    (hα : ∀ a, α a ∈ lead F Λ (Fin.castLE hl a).castSucc) (hβ : ∀ a, β a ∈ lead F' Λ (Fin.castLE hl a).castSucc) :
    (∏ a, α a) * (∏ a, star (β a)) * Dl F F' l (hl.trans (Nat.le_succ r)) ∈ (1 : Submodule (𝓞 K) K) ∧
    ∀ x ∈ F.Xa l, (∀ p ∈ Λ, p ∈ F'.Xa l → H.B x p ∈ (1 : Submodule (𝓞 K) K)) →
      ((∏ a, α a) * (∏ a, star (β a)) * Dl F F' l (hl.trans (Nat.le_succ r))) • x ∈ Λ := by
  obtain ⟨A, hA, hA'⟩ := exists_tri F Λ hl α hα
  obtain ⟨B, hB, hB'⟩ := exists_tri F' Λ hl β hβ
  set e : Fin l → V := fun b => F.e (Fin.castLE (hl.trans (Nat.le_succ r)) b) with he
  set e' : Fin l → V := fun b => F'.e (Fin.castLE (hl.trans (Nat.le_succ r)) b) with he'
  set Z : Matrix (Fin l) (Fin l) K := Matrix.of fun a b => H.B (e a) (e' b) with hZ
  have hD : Dl F F' l (hl.trans (Nat.le_succ r)) = Z.det := rfl
  have key : ∀ (ξ : Fin l → K) (b : Fin l), H.B (∑ a, ξ a • e a) (∑ c, B b c • e' c) = (ξ ᵥ* (Z * Bᴴ)) b := by
    intro ξ b
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul,
      vecMul, dotProduct, Matrix.mul_apply, hZ, Matrix.of_apply, conjTranspose_apply, starRingEnd_apply,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hQ : ∀ a b, ∃ q : 𝓞 K, algebraMap (𝓞 K) K q = (A * (Z * Bᴴ)) a b := by
    intro a b
    have := hint _ (hA' a) _ (hB' b)
    rw [key] at this
    exact Submodule.mem_one.1 this
  choose Q hQ using hQ
  have hQ' : (algebraMap (𝓞 K) K).mapMatrix (Matrix.of Q) = A * (Z * Bᴴ) := by
    ext a b; exact hQ a b
  have hdet : (∏ a, α a) * (∏ a, star (β a)) * Dl F F' l (hl.trans (Nat.le_succ r)) = (A * (Z * Bᴴ)).det := by
    rw [det_mul, det_mul, det_conjTranspose, hA, hB, hD, star_prod]; ring
  rw [hdet]
  refine ⟨Submodule.mem_one.2 ⟨(Matrix.of Q).det, by rw [RingHom.map_det, hQ']⟩, fun x hx hp => ?_⟩
  obtain ⟨ξ, -, rfl⟩ := exists_coord F hl le_rfl hx
  have hp' : ∀ b, ∃ q : 𝓞 K, algebraMap (𝓞 K) K q = (ξ ᵥ* (Z * Bᴴ)) b := by
    intro b
    have := hp _ (hB' b) (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (e_mem F' hl c))
    rw [key] at this
    exact Submodule.mem_one.1 this
  choose p hp' using hp'
  have hu : ∀ a, algebraMap (𝓞 K) K ((p ᵥ* (Matrix.of Q).adjugate) a) =
      ((ξ ᵥ* (Z * Bᴴ)) ᵥ* (A * (Z * Bᴴ)).adjugate) a := by
    intro a
    rw [RingHom.map_vecMul, ← hQ', ← RingHom.map_adjugate]
    congr 1
    exact funext hp'
  have hv : ((ξ ᵥ* (Z * Bᴴ)) ᵥ* (A * (Z * Bᴴ)).adjugate) ᵥ* A = (A * (Z * Bᴴ)).det • ξ := by
    rw [adjugate_mul_distrib, vecMul_vecMul, vecMul_vecMul, Matrix.mul_assoc, Matrix.mul_assoc, adjugate_mul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (Z * Bᴴ), ← Matrix.mul_assoc (Z * Bᴴ), mul_adjugate,
      det_mul A]
    simp [vecMul_smul, smul_smul, mul_comm]
  have hs := Λ.sum_mem (t := Finset.univ) fun a _ => Λ.smul_mem ((p ᵥ* (Matrix.of Q).adjugate) a) (hA' a)
  convert hs using 1
  simp only [← algebraMap_smul K ((p ᵥ* (Matrix.of Q).adjugate) _), hu, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  exact (congrFun hv b).symm

open GlobalTheory.DegCnt.IdealPow in

theorem cramer (F F' : FlagD H r) (Λ : Submodule (𝓞 K) V)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K)) {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥)
    (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K))
    (hF : ∀ a : Fin r, lead F Λ a.castSucc = ipow 𝔡 (-((r : ℤ) - a.val)))
    (hF' : ∀ a : Fin r, lead F' Λ a.castSucc = ipow 𝔡 (-((r : ℤ) - a.val))) {l : ℕ} (hl : l ≤ r) {u : K}
    (hu : u ∈ ipow 𝔡 (-(2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)))) :
    u * Dl F F' l (hl.trans (Nat.le_succ r)) ∈ (1 : Submodule (𝓞 K) K) ∧
    ∀ x ∈ F.Xa l, (∀ p ∈ Λ, p ∈ F'.Xa l → H.B x p ∈ (1 : Submodule (𝓞 K) K)) →
      (u * Dl F F' l (hl.trans (Nat.le_succ r))) • x ∈ Λ := by
  let n : Fin l ⊕ Fin l → ℤ := Sum.elim (fun a => -((r : ℤ) - a.val)) (fun a => -((r : ℤ) - a.val))
  have hn : -(2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)) = ∑ i, n i := by
    rw [Fintype.sum_sum_type, Finset.sum_range]
    simp only [n, Sum.elim_inl, Sum.elim_inr, Finset.sum_neg_distrib]
    ring
  rw [hn] at hu
  have key := fun (α : Fin l ⊕ Fin l → K) (hα : ∀ i, α i ∈ ipow 𝔡 (n i)) =>
    hermFlag_pairing_cramer_of_leadingCoeffs F F' Λ hint hl (fun a => α (Sum.inl a)) (fun a => star (α (Sum.inr a)))
      (fun a => by rw [hF]; exact hα (Sum.inl a)) (fun a => by rw [hF']; exact star_mem h hs (hα (Sum.inr a)))
  simp only [star_star, ← Fintype.prod_sum_type] at key
  refine ⟨ipow_sum_le h n ((1 : Submodule (𝓞 K) K).comap
    (LinearMap.mulRight (𝓞 K) (Dl F F' l (hl.trans (Nat.le_succ r))))) (fun α hα => (key α hα).1) hu, fun x hx hp => ?_⟩
  have := ipow_sum_le h n (Λ.comap ((LinearMap.toSpanSingleton K V
    (Dl F F' l (hl.trans (Nat.le_succ r)) • x)).restrictScalars (𝓞 K))) (fun α hα => by
      have := (key α hα).2 x hx hp
      rwa [mul_smul] at this) hu
  rw [mul_smul]
  exact this

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem Dl_swap (F F' : FlagD H r) (l : ℕ) (hl : l ≤ r + 1) : Dl F' F l hl = star (Dl F F' l hl) := by
  unfold Dl
  rw [← det_conjTranspose]
  congr 1
  ext a b
  exact (H.herm _ _).symm

end GlobalTheory.DegCnt.FrameCramer

namespace GlobalTheory.DegCnt.Monomial

open GlobalTheory.DegCnt.IdealPow GlobalTheory.UnimodQuot

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V}

omit [StarRing K] in
theorem mem_line {A : Submodule (𝓞 K) K} {v x : V} : x ∈ line A v ↔ ∃ t ∈ A, t • v = x := Iff.rfl

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem B_smul (a b : K) (x y : V) : H.B (a • x) (b • y) = a * star b * H.B x y := by
  rw [H.B.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul, mul_assoc]
  rfl

theorem monomial {ι : Type} [Fintype ι] (v : ι → V) (n : ι → ℤ) {𝔡 𝔠 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥)
    (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K))
    (h1 : ∀ i k, H.B (v i) (v k) ≠ 0 → ∀ γ ∈ 𝔠,
      (∀ u ∈ ipow 𝔡 (n i + n k), (γ : K) * u * H.B (v i) (v k) ∈ (1 : Submodule (𝓞 K) K)) ∧
      (∀ u ∈ ipow 𝔡 (-(n i + n k)), (γ : K) * u / H.B (v i) (v k) ∈ (1 : Submodule (𝓞 K) K)))
    (h2 : ∀ i, ∃ k, H.B (v i) (v k) ≠ 0 ∧ ∀ i', i' ≠ i → H.B (v i') (v k) = 0)
    (P : Submodule (𝓞 K) V) (hP : P = ⨆ i, line (ipow 𝔡 (n i)) (v i)) :
    𝔠 • dual H P ≤ P ∧ 𝔠 • P ≤ dual H P := by
  have hle : ∀ i, ∀ t ∈ ipow 𝔡 (n i), t • v i ∈ P := fun i t ht => by
    rw [hP]; exact Submodule.mem_iSup_of_mem i ⟨t, ht, rfl⟩
  have hind : ∀ {C : V → Prop}, C 0 → (∀ x y, C x → C y → C (x + y)) → (∀ i, ∀ t ∈ ipow 𝔡 (n i), C (t • v i)) →
      ∀ x ∈ P, C x := by
    intro C h0 ha hm x hx
    rw [hP] at hx
    refine Submodule.iSup_induction _ (motive := C) hx ?_ h0 ha
    rintro i _ ⟨t, ht, rfl⟩
    exact hm i t ht
  constructor
  · rw [Submodule.smul_le]
    intro γ hγ y hy
    rw [mem_dual_iff] at hy
    have hsp : Submodule.span K (P : Set V) ≤ Submodule.span K (Set.range v) := by
      rw [Submodule.span_le]
      intro x hx
      exact hind (C := fun x => x ∈ Submodule.span K (Set.range v)) (zero_mem _) (fun _ _ => add_mem)
        (fun i t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) x hx
    obtain ⟨ξ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hsp hy.1)
    rw [Finset.smul_sum]
    refine P.sum_mem fun i _ => ?_
    rw [← algebraMap_smul K γ, smul_smul]
    apply hle
    obtain ⟨k, hk, hk'⟩ := h2 i
    have h3 : ξ i * H.B (v i) (v k) ∈ ipow 𝔡 (-n k) := by
      refine mem_of_forall h (neg_add_cancel _) fun β hβ => ?_
      have := hy.2 _ (hle k _ (star_mem h hs hβ))
      rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single i (fun b _ hb => by simp [hk' b hb]) (by simp)] at this
      convert this using 1
      rw [B_smul, star_star]; ring
    refine mem_of_forall h (add_neg_cancel _) fun δ hδ => ?_
    have := (h1 i k hk γ hγ).2 _ (mul_mem h (by ring) h3 hδ)
    convert this using 1
    field_simp
  · rw [Submodule.smul_le]
    intro γ hγ y hy
    rw [mem_dual_iff]
    refine ⟨Submodule.subset_span (P.smul_mem γ hy), ?_⟩
    rw [← algebraMap_smul K γ]
    revert y
    refine hind (C := fun y => ∀ x ∈ P, H.B (algebraMap (𝓞 K) K γ • y) x ∈ (1 : Submodule (𝓞 K) K))
      (fun _ _ => by simp) (fun a b ha hb x hx => ?_) (fun i t ht => ?_)
    · rw [smul_add, map_add, LinearMap.add_apply]; exact add_mem (ha x hx) (hb x hx)
    refine hind (by simp) (fun a b ha hb => by rw [map_add]; exact add_mem ha hb) (fun k β hβ => ?_)
    by_cases hk : H.B (v i) (v k) = 0
    · simp [LinearMap.map_smulₛₗ, hk]
    have := (h1 i k hk γ hγ).1 _ (mul_mem h rfl ht (star_mem h hs hβ))
    convert this using 1
    rw [smul_smul, B_smul]
    show (γ : K) * _ * _ * _ = _
    ring

end GlobalTheory.DegCnt.Monomial

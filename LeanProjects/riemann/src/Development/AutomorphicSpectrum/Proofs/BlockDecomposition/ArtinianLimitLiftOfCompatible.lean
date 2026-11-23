import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup

open CrystallineSemistableComparison

namespace GlobalTheory.CompanionTheory.ArtinTower

universe w

theorem coset_chain {W : Type} [CommRing W] {M : Type w} [AddCommGroup M] [Module W M]
    [IsArtinian W M] (K : ℕ → Submodule W M) (hK : ∀ k, K (k + 1) ≤ K k) (c : ℕ → M)
    (hc : ∀ k, c (k + 1) - c k ∈ K k) : ∃ x, ∀ k, x - c k ∈ K k := by
  have hanti : Antitone K := antitone_nat_of_succ_le hK
  obtain ⟨m, hm⟩ := IsArtinian.monotone_stabilizes
    (⟨fun k => OrderDual.toDual (K k), hanti.dual_right⟩ : ℕ →o (Submodule W M)ᵒᵈ)
  have hdiff : ∀ k j, c (k + j) - c k ∈ K k := by
    intro k j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : c (k + j + 1) - c (k + j) ∈ K k := hanti (Nat.le_add_right k j) (hc (k + j))
      have h2 := add_mem h1 ih
      rw [sub_add_sub_cancel] at h2
      exact h2
  refine ⟨c m, fun k => ?_⟩
  rcases le_total k m with hkm | hmk
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
    exact hdiff k j
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmk
    have hKeq : K m = K (m + j) := hm (m + j) (Nat.le_add_right m j)
    rw [← hKeq]
    have h3 := neg_mem (hdiff m j)
    rw [neg_sub] at h3
    exact h3

section
variable {W : Type} [CommRing W] (S : Sys.{w} W) (N : ∀ n, Submodule W (S.M n))
  (y : ∀ n, S.M n)

noncomputable def imgSub : ℕ → ∀ n, Submodule W (S.M n)
  | 0, n => N n
  | k + 1, n => (imgSub k (n + 1)).map (S.r n)

noncomputable def imgPt : ℕ → ∀ n, S.M n
  | 0, n => y n
  | k + 1, n => S.r n (imgPt k (n + 1))

def stable (n : ℕ) : Set (S.M n) := {x | ∀ k, x - imgPt S y k n ∈ imgSub S N k n}

variable {S N y}

theorem imgSub_succ_le (hN : ∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n) :
    ∀ k n, imgSub S N (k + 1) n ≤ imgSub S N k n := by
  intro k
  induction k with
  | zero =>
    intro n
    show Submodule.map (S.r n) (N (n + 1)) ≤ N n
    exact Submodule.map_le_iff_le_comap.mpr (fun u hu => hN n u hu)
  | succ k ih =>
    intro n
    show Submodule.map (S.r n) (imgSub S N (k + 1) (n + 1)) ≤
      Submodule.map (S.r n) (imgSub S N k (n + 1))
    exact Submodule.map_mono (ih (n + 1))

theorem imgPt_step (hy : ∀ n, S.r n (y (n + 1)) - y n ∈ N n) :
    ∀ k n, imgPt S y (k + 1) n - imgPt S y k n ∈ imgSub S N k n := by
  intro k
  induction k with
  | zero => intro n; exact hy n
  | succ k ih =>
    intro n
    show S.r n (imgPt S y (k + 1) (n + 1)) - S.r n (imgPt S y k (n + 1)) ∈
      Submodule.map (S.r n) (imgSub S N k (n + 1))
    rw [← map_sub]
    exact Submodule.mem_map_of_mem (ih (n + 1))

theorem stable_nonempty (hN : ∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n)
    (hy : ∀ n, S.r n (y (n + 1)) - y n ∈ N n) (n : ℕ) [IsArtinian W (S.M n)] :
    ∃ x, x ∈ stable S N y n := by
  obtain ⟨x, hx⟩ := coset_chain (fun k => imgSub S N k n) (fun k => imgSub_succ_le hN k n)
    (fun k => imgPt S y k n) (fun k => imgPt_step hy k n)
  exact ⟨x, hx⟩

theorem stable_surj (hN : ∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n)
    (hy : ∀ n, S.r n (y (n + 1)) - y n ∈ N n) {n : ℕ} [IsArtinian W (S.M (n + 1))]
    {x : S.M n} (hx : x ∈ stable S N y n) :
    ∃ x' ∈ stable S N y (n + 1), S.r n x' = x := by
  have hxk : ∀ k, x - imgPt S y k n ∈ imgSub S N k n := hx
  have hA : ∀ k, ∃ u : S.M (n + 1),
      S.r n u = x ∧ u - imgPt S y k (n + 1) ∈ imgSub S N k (n + 1) := by
    intro k
    have h1 : x - imgPt S y (k + 1) n ∈ Submodule.map (S.r n) (imgSub S N k (n + 1)) :=
      hxk (k + 1)
    obtain ⟨v, hv, hve⟩ := Submodule.mem_map.mp h1
    refine ⟨v + imgPt S y k (n + 1), ?_, ?_⟩
    · rw [map_add, hve]
      show x - S.r n (imgPt S y k (n + 1)) + S.r n (imgPt S y k (n + 1)) = x
      exact sub_add_cancel _ _
    · rw [add_sub_cancel_right]
      exact hv
  choose c hc1 hc2 using hA
  have hKanti : ∀ k, LinearMap.ker (S.r n) ⊓ imgSub S N (k + 1) (n + 1) ≤
      LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1) :=
    fun k => inf_le_inf_left _ (imgSub_succ_le hN k (n + 1))
  have hstep : ∀ k, c (k + 1) - c k ∈ LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1) := by
    intro k
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hc1, hc1, sub_self]
    · have e : c (k + 1) - c k = (c (k + 1) - imgPt S y (k + 1) (n + 1)) +
          (imgPt S y (k + 1) (n + 1) - imgPt S y k (n + 1)) - (c k - imgPt S y k (n + 1)) := by
        abel
      rw [e]
      exact sub_mem (add_mem (imgSub_succ_le hN k (n + 1) (hc2 (k + 1)))
        (imgPt_step hy k (n + 1))) (hc2 k)
  obtain ⟨x', hx'⟩ := coset_chain (fun k => LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1))
    hKanti c hstep
  refine ⟨x', fun k => ?_, ?_⟩
  · have e : x' - imgPt S y k (n + 1) = (x' - c k) + (c k - imgPt S y k (n + 1)) := by abel
    rw [e]
    exact add_mem (Submodule.mem_inf.mp (hx' k)).2 (hc2 k)
  · have h0 := (Submodule.mem_inf.mp (hx' 0)).1
    rw [LinearMap.mem_ker, map_sub, hc1, sub_eq_zero] at h0
    exact h0

end

theorem exists_compatible : ∀ (W : Type) [CommRing W] (S : Sys.{1} W),
    (∀ n, IsArtinian W (S.M n)) → ∀ (N : ∀ n, Submodule W (S.M n)) (y : ∀ n, S.M n),
    (∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n) → (∀ n, S.r n (y (n + 1)) - y n ∈ N n) →
    ∃ z : S.lim, ∀ n, z.1 n - y n ∈ N n := by
  intro W _ S hA N y hN hy
  have h0 : ∃ x, x ∈ stable S N y 0 := by
    haveI := hA 0
    exact stable_nonempty hN hy 0
  have hs : ∀ n (x : S.M n), x ∈ stable S N y n →
      ∃ x' ∈ stable S N y (n + 1), S.r n x' = x := fun n x hx => by
    haveI := hA (n + 1)
    exact stable_surj hN hy hx
  let f : ∀ n, {x : S.M n // x ∈ stable S N y n} := fun n =>
    Nat.rec (motive := fun n => {x : S.M n // x ∈ stable S N y n})
      ⟨h0.choose, h0.choose_spec⟩
      (fun n p => ⟨(hs n p.1 p.2).choose, (hs n p.1 p.2).choose_spec.1⟩) n
  have hf : ∀ n, S.r n (f (n + 1)).1 = (f n).1 := fun n =>
    (hs n (f n).1 (f n).2).choose_spec.2
  refine ⟨⟨fun n => (f n).1, ?_⟩, fun n => (f n).2 0⟩
  unfold CrystallineSemistableComparison.Sys.lim
  exact fun n => hf n

end GlobalTheory.CompanionTheory.ArtinTower

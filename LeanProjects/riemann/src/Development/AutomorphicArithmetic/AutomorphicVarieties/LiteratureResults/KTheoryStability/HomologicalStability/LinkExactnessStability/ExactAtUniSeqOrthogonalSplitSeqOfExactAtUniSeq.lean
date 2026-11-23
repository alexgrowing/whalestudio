import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsGLSplitSeqStandardOfStableRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainExactAtMapIff
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory.SeqCx.LinkCol

variable {R : Type} [CommRing R]

def padZero {m N : ℕ} (v : Fin m → R) : Fin N → R := fun i => if h : (i : ℕ) < m then v ⟨i, h⟩ else 0

def restrFirst {m N : ℕ} (h : m ≤ N) (x : Fin N → R) : Fin m → R := fun i => x (Fin.castLE h i)

lemma dotProduct_padZero {m N : ℕ} (h : m ≤ N) (F : Fin N → R) (v : Fin m → R) :
    F ⬝ᵥ padZero v = restrFirst h F ⬝ᵥ v := by
  unfold dotProduct
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
  · intro i hi
    simp only [padZero]
    rw [dif_neg, mul_zero]
    intro hlt
    exact hi ⟨⟨i, hlt⟩, Fin.ext rfl⟩
  · intro i
    simp [restrFirst, padZero]

lemma restrFirst_padZero {m N : ℕ} (h : m ≤ N) (v : Fin m → R) : restrFirst h (padZero v) = v := by
  ext i
  simp [restrFirst, padZero]

lemma padZero_restrFirst {m N : ℕ} (h : m ≤ N) (x : Fin N → R) (hx : ∀ i : Fin N, m ≤ (i : ℕ) → x i = 0) :
    padZero (restrFirst h x) = x := by
  ext i
  simp only [padZero, restrFirst]
  split_ifs with hi
  · rfl
  · exact (hx i (not_lt.mp hi)).symm

lemma mem_uniSeq_iff {n : ℕ} (l : List (Fin n → R)) :
    l ∈ uniSeq R n ↔ ∃ f : ℕ → Fin n → R, ∀ i j (hi : i < l.length) (hj : j < l.length),
      f i ⬝ᵥ l[j] = if i = j then 1 else 0 := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun i => if h : i < l.length then f ⟨i, h⟩ else 0, fun i j hi hj => ?_⟩
    have := hf ⟨i, hi⟩ ⟨j, hj⟩
    simp only [dif_pos hi]
    simpa [Fin.ext_iff] using this
  · rintro ⟨f, hf⟩
    refine ⟨fun i => f i, fun i j => ?_⟩
    have := hf i j i.2 j.2
    simpa [Fin.ext_iff] using this

lemma map_mem_uniSeq {m N : ℕ} (e : (Fin m → R) → (Fin N → R)) (A : (Fin N → R) → (Fin m → R))
    (B : (Fin m → R) → (Fin N → R)) (hA : ∀ F v, F ⬝ᵥ e v = A F ⬝ᵥ v)
    (hB : ∀ f v, B f ⬝ᵥ e v = f ⬝ᵥ v) (vs : List (Fin m → R)) :
    vs.map e ∈ uniSeq R N ↔ vs ∈ uniSeq R m := by
  rw [mem_uniSeq_iff, mem_uniSeq_iff]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun i => A (f i), fun i j hi hj => ?_⟩
    have := hf i j (by simpa using hi) (by simpa using hj)
    rw [List.getElem_map, hA] at this
    exact this
  · rintro ⟨f, hf⟩
    refine ⟨fun i => B (f i), fun i j hi hj => ?_⟩
    rw [List.getElem_map, hB]
    exact hf i j (by simpa using hi) (by simpa using hj)

end GlobalTheory.SeqCx.LinkCol

open GlobalTheory.SeqCx.LinkCol

theorem GlobalTheory.SeqCx.exactAt_uniSeq_killed_by_split : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s →
    ∀ (N m q : ℕ) (ρ : List ((Fin N → R) × (Fin N → R))), ρ ∈ splitSeq R N → ρ.length + m = N →
    s ≤ m → ExactAt (uniSeq R m) q →
    ExactAt {w | w ∈ uniSeq R N ∧ ∀ y ∈ ρ, ∀ u ∈ w, y.2 ⬝ᵥ u = 0} q := by
  intro R _ s hs N m q ρ hρ hN hsm hex
  have hmN : m ≤ N := by omega
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_GL_splitSeq_standard_of_stableRangeLe R s hs N ρ hρ (by omega) (fun j => ⟨m + j, by omega⟩)
    (by intro a b h; simp [Fin.ext_iff] at h; exact Fin.ext h)
  set G : Matrix (Fin N) (Fin N) R := (g : Matrix (Fin N) (Fin N) R) with hGdef
  set Gi : Matrix (Fin N) (Fin N) R := ((g⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) with hGidef
  have hGGi : G * Gi = 1 := Units.mul_inv g
  have hGiG : Gi * G = 1 := Units.inv_mul g
  let e : (Fin m → R) → (Fin N → R) := fun v => Gi *ᵥ padZero v
  have he : Function.Injective e := by
    intro a b hab
    have h1 : G *ᵥ (Gi *ᵥ padZero a) = G *ᵥ (Gi *ᵥ padZero b) := by
      simp only [e] at hab; rw [hab]
    rw [mulVec_mulVec, mulVec_mulVec, hGGi, one_mulVec, one_mulVec] at h1
    have h2 := congrArg (restrFirst hmN) h1
    rwa [restrFirst_padZero, restrFirst_padZero] at h2
  have hdot : ∀ (u : Fin N → R) (j : Fin ρ.length), (ρ.get j).2 ⬝ᵥ u = (G *ᵥ u) ⟨m + j, by omega⟩ := by
    intro u j
    have h1 : u = Gi *ᵥ (G *ᵥ u) := by rw [mulVec_mulVec, hGiG, one_mulVec]
    conv_lhs => rw [h1]
    rw [dotProduct_mulVec, (hg j).2, single_dotProduct, one_mul]
  have hkey : ∀ u : Fin N → R, (∀ y ∈ ρ, y.2 ⬝ᵥ u = 0) ↔ e (restrFirst hmN (G *ᵥ u)) = u := by
    intro u
    constructor
    · intro h
      have hz : ∀ i : Fin N, m ≤ (i : ℕ) → (G *ᵥ u) i = 0 := by
        intro i hi
        have hi2 := i.2
        have h3 := h (ρ.get ⟨i - m, by omega⟩) (List.get_mem _ _)
        rw [hdot] at h3
        convert h3 using 2
        ext
        simp only
        omega
      simp only [e]
      rw [padZero_restrFirst hmN _ hz, mulVec_mulVec, hGiG, one_mulVec]
    · intro h y hy
      obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hy
      rw [hdot]
      have h1 : G *ᵥ u = padZero (restrFirst hmN (G *ᵥ u)) := by
        conv_lhs => rw [← h]
        simp only [e]
        rw [mulVec_mulVec, hGGi, one_mulVec]
      rw [h1]
      simp [padZero]
  have hA : ∀ F v, F ⬝ᵥ e v = restrFirst hmN (F ᵥ* Gi) ⬝ᵥ v := by
    intro F v
    simp only [e]
    rw [dotProduct_mulVec, dotProduct_padZero hmN]
  have hB : ∀ f v, (padZero f ᵥ* G) ⬝ᵥ e v = f ⬝ᵥ v := by
    intro f v
    simp only [e]
    rw [dotProduct_mulVec, vecMul_vecMul, hGGi, vecMul_one, dotProduct_padZero hmN, restrFirst_padZero]
  have hset : {w | w ∈ uniSeq R N ∧ ∀ y ∈ ρ, ∀ u ∈ w, y.2 ⬝ᵥ u = 0} = List.map e '' uniSeq R m := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hw, h⟩
      have hw' : w.map (fun u => e (restrFirst hmN (G *ᵥ u))) = w := by
        conv_rhs => rw [← List.map_id w]
        apply List.map_congr_left
        intro u hu
        exact (hkey u).mp (fun y hy => h y hy u hu)
      refine ⟨w.map (fun u => restrFirst hmN (G *ᵥ u)), ?_, ?_⟩
      · rw [← map_mem_uniSeq e _ _ hA hB, List.map_map]
        convert hw using 1
        exact hw'
      · rw [List.map_map]
        exact hw'
    · rintro ⟨vs, hvs, rfl⟩
      refine ⟨(map_mem_uniSeq e _ _ hA hB vs).mpr hvs, ?_⟩
      intro y hy u hu
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hu
      have h1 : restrFirst hmN (G *ᵥ e v) = v := by
        simp only [e]
        rw [mulVec_mulVec, hGGi, one_mulVec, restrFirst_padZero]
      exact (hkey (e v)).mpr (by rw [h1]) y hy
  rw [hset]
  exact (GlobalTheory.T.seqChain_exactAt_map_iff _ _ e he _ q).mpr hex

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exactAt_uniSeq_orthogonal_splitSeq_of_exactAt_uniSeq : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (N m q : ℕ) (ρ : List ((Fin N → R) × (Fin N → R))), ρ ∈ splitSeq R N → ρ.length + m = N → s ≤ m → ExactAt (uniSeq R m) q → ExactAt {w | w ∈ uniSeq R N ∧ ∀ y ∈ ρ, ∀ u ∈ w, y.2 ⬝ᵥ u = 0} q := by
  first
  | exact @GlobalTheory.SeqCx.exactAt_uniSeq_killed_by_split
end

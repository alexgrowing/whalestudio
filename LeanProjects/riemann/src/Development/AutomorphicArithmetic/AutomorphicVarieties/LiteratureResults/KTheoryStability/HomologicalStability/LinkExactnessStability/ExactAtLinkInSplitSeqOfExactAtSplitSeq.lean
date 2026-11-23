import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsGLSplitSeqStandardOfStableRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainExactAtMapIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosedSplitSeqAndUniSeqWithMemIff

open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory.SeqCx.LinkSplit

variable {R : Type} [CommRing R]

def pad {m N : ℕ} (v : Fin m → R) : Fin N → R := fun i => if h : (i : ℕ) < m then v ⟨i, h⟩ else 0

def restr {m N : ℕ} (h : m ≤ N) (y : Fin N → R) : Fin m → R := fun i => y ⟨i, lt_of_lt_of_le i.2 h⟩

lemma pad_apply_lt {m N : ℕ} (v : Fin m → R) (i : Fin N) (h : (i : ℕ) < m) :
    pad (N := N) v i = v ⟨i, h⟩ := dif_pos h

lemma pad_apply_ge {m N : ℕ} (v : Fin m → R) (i : Fin N) (h : m ≤ (i : ℕ)) :
    pad (N := N) v i = 0 := dif_neg (by omega)

lemma restr_pad {m N : ℕ} (h : m ≤ N) (v : Fin m → R) : restr h (pad (N := N) v) = v := by
  funext i
  exact pad_apply_lt v _ i.2

lemma pad_restr {m N : ℕ} (h : m ≤ N) (y : Fin N → R) (hy : ∀ i : Fin N, m ≤ (i : ℕ) → y i = 0) :
    pad (restr h y) = y := by
  funext i
  by_cases hi : (i : ℕ) < m
  · rw [pad_apply_lt _ _ hi]; rfl
  · rw [pad_apply_ge _ _ (by omega), hy i (by omega)]

lemma pad_dot {m N : ℕ} (h : m ≤ N) (f v : Fin m → R) :
    pad (N := N) f ⬝ᵥ pad v = f ⬝ᵥ v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : ∀ (u : Fin m → R) (i : Fin m), pad (N := m + k) u (Fin.castAdd k i) = u i :=
    fun u i => pad_apply_lt u _ i.2
  have h2 : ∀ (u : Fin m → R) (i : Fin k), pad (N := m + k) u (Fin.natAdd m i) = 0 :=
    fun u i => pad_apply_ge u _ (by simp)
  simp only [dotProduct, Fin.sum_univ_add, h1, h2, mul_zero, Finset.sum_const_zero, add_zero]

end GlobalTheory.SeqCx.LinkSplit

namespace GlobalTheory.SeqCx

private theorem map_mem_splitSeq_iff_of_pairing_preserved {R : Type} [CommRing R] {a b : ℕ}
    (f : (Fin a → R) × (Fin a → R) → (Fin b → R) × (Fin b → R))
    (hf : ∀ x y, (f y).2 ⬝ᵥ (f x).1 = y.2 ⬝ᵥ x.1) (l : List ((Fin a → R) × (Fin a → R))) :
    List.map f l ∈ splitSeq R b ↔ l ∈ splitSeq R a := by
  rw [(GlobalTheory.T.subClosed_splitSeq_and_uniSeq_with_mem_iff R b).2.2.1, (GlobalTheory.T.subClosed_splitSeq_and_uniSeq_with_mem_iff R a).2.2.1, List.pairwise_map]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, hf]

open LinkSplit in

theorem exactAt_link_splitSeq : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s →
    ∀ (N m p : ℕ) (ρ : List ((Fin N → R) × (Fin N → R))), ρ ∈ splitSeq R N → ρ.length + m = N →
      s ≤ m → ExactAt (splitSeq R m) p → ExactAt (linkIn (splitSeq R N) Set.univ ρ) p := by
  intro R _ s hs N m p ρ hρ hlen hsm hex
  have hmN : m ≤ N := by omega
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_GL_splitSeq_standard_of_stableRangeLe R s hs N ρ hρ (by omega)
    (fun j => (⟨m + (j : ℕ), by omega⟩ : Fin N))
    (by intro a b h; ext; simp only [Fin.mk.injEq] at h; omega)
  let T : (Fin N → R) × (Fin N → R) → (Fin N → R) × (Fin N → R) :=
    fun x => ((↑g : Matrix (Fin N) (Fin N) R) *ᵥ x.1, x.2 ᵥ* (↑g⁻¹ : Matrix (Fin N) (Fin N) R))
  let Ti : (Fin N → R) × (Fin N → R) → (Fin N → R) × (Fin N → R) :=
    fun x => ((↑g⁻¹ : Matrix (Fin N) (Fin N) R) *ᵥ x.1, x.2 ᵥ* (↑g : Matrix (Fin N) (Fin N) R))
  have hTTi : ∀ x, T (Ti x) = x := by
    intro x
    refine Prod.ext ?_ ?_
    · simp only [T, Ti, mulVec_mulVec, Units.mul_inv, one_mulVec]
    · simp only [T, Ti, vecMul_vecMul, Units.mul_inv, vecMul_one]
  have hTiT : ∀ x, Ti (T x) = x := by
    intro x
    refine Prod.ext ?_ ?_
    · simp only [T, Ti, mulVec_mulVec, Units.inv_mul, one_mulVec]
    · simp only [T, Ti, vecMul_vecMul, Units.inv_mul, vecMul_one]
  have hTdot : ∀ x y, (T y).2 ⬝ᵥ (T x).1 = y.2 ⬝ᵥ x.1 := by
    intro x y
    simp only [T]
    rw [dotProduct_mulVec, vecMul_vecMul, Units.inv_mul, vecMul_one]
  let P : (Fin m → R) × (Fin m → R) → (Fin N → R) × (Fin N → R) :=
    fun x => (LinkSplit.pad x.1, LinkSplit.pad x.2)
  have hPdot : ∀ x y, (P y).2 ⬝ᵥ (P x).1 = y.2 ⬝ᵥ x.1 := fun x y => LinkSplit.pad_dot hmN _ _
  have hPinj : Function.Injective P := by
    intro x y h
    have h1 := congrArg (fun z => LinkSplit.restr hmN z.1) h
    have h2 := congrArg (fun z => LinkSplit.restr hmN z.2) h
    simp only [P, LinkSplit.restr_pad] at h1 h2
    exact Prod.ext h1 h2
  have hTiinj : Function.Injective Ti := fun x y h => by rw [← hTTi x, ← hTTi y, h]
  have hmemT := map_mem_splitSeq_iff_of_pairing_preserved T hTdot
  have hmemP := map_mem_splitSeq_iff_of_pairing_preserved P hPdot
  have hchar := (GlobalTheory.T.subClosed_splitSeq_and_uniSeq_with_mem_iff R N).2.2.1
  have hρT : ∀ j : Fin ρ.length, T (ρ.get j) =
      (Pi.single (⟨m + (j : ℕ), by omega⟩ : Fin N) 1, Pi.single (⟨m + (j : ℕ), by omega⟩ : Fin N) 1) :=
    fun j => Prod.ext (hg j).1 (hg j).2
  have key : linkIn (splitSeq R N) Set.univ ρ = List.map Ti '' (List.map P '' splitSeq R m) := by
    ext w
    constructor
    · rintro ⟨-, hw⟩
      have hw' := (hchar _).1 hw
      rw [List.pairwise_append] at hw'
      obtain ⟨hall, -, hpw, hcross⟩ := hw'
      have wsplit : w ∈ splitSeq R N :=
        (hchar w).2 ⟨fun y hy => hall y (List.mem_append_right _ hy), hpw⟩
      have hvan : ∀ x ∈ w, ∀ i : Fin N, m ≤ (i : ℕ) → (T x).1 i = 0 ∧ (T x).2 i = 0 := by
        intro x hx i hi
        let j : Fin ρ.length := ⟨(i : ℕ) - m, by omega⟩
        have hji : (⟨m + (j : ℕ), by omega⟩ : Fin N) = i := Fin.ext (by simp only [j]; omega)
        have hc := hcross (ρ.get j) (List.get_mem _ _) x hx
        have e := hρT j
        rw [hji] at e
        constructor
        · have := hTdot x (ρ.get j)
          rw [e, single_dotProduct, one_mul] at this
          rw [this]
          exact hc.1
        · have := hTdot (ρ.get j) x
          rw [e, dotProduct_single, mul_one] at this
          rw [this]
          exact hc.2
      let l := w.map (fun x => (LinkSplit.restr hmN (T x).1, LinkSplit.restr hmN (T x).2))
      have hPl : List.map P l = List.map T w := by
        simp only [l, List.map_map]
        apply List.map_congr_left
        intro x hx
        refine Prod.ext ?_ ?_
        · exact LinkSplit.pad_restr hmN _ (fun i hi => (hvan x hx i hi).1)
        · exact LinkSplit.pad_restr hmN _ (fun i hi => (hvan x hx i hi).2)
      have lsplit : l ∈ splitSeq R m := (hmemP l).1 (hPl ▸ (hmemT w).2 wsplit)
      refine ⟨List.map P l, ⟨l, lsplit, rfl⟩, ?_⟩
      rw [hPl, List.map_map]
      simp [Function.comp_def, hTiT]
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      refine ⟨fun _ _ => Set.mem_univ _, ?_⟩
      have hback : List.map T (List.map Ti (List.map P l)) = List.map P l := by
        simp [List.map_map, Function.comp_def, hTTi]
      rw [← hmemT, List.map_append, hback]
      have A := (hchar _).1 ((hmemT ρ).2 hρ)
      have B := (hchar _).1 ((hmemP l).2 hl)
      rw [hchar, List.pairwise_append]
      refine ⟨?_, A.2, B.2, ?_⟩
      · intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact A.1 y hy
        · exact B.1 y hy
      · intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
        obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hx
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hb
        rw [hρT j]
        have hk : m ≤ ((⟨m + (j : ℕ), by omega⟩ : Fin N) : ℕ) := Nat.le_add_right _ _
        simp only [P, single_dotProduct, dotProduct_single, LinkSplit.pad_apply_ge _ _ hk,
          mul_zero, zero_mul, and_self]
  rw [key, GlobalTheory.T.seqChain_exactAt_map_iff _ _ Ti hTiinj, GlobalTheory.T.seqChain_exactAt_map_iff _ _ P hPinj]
  exact hex

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exactAt_linkIn_splitSeq_of_exactAt_splitSeq : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (N m p : ℕ) (ρ : List ((Fin N → R) × (Fin N → R))), ρ ∈ splitSeq R N → ρ.length + m = N → s ≤ m → ExactAt (splitSeq R m) p → ExactAt (linkIn (splitSeq R N) Set.univ ρ) p := by
  first
  | exact @GlobalTheory.SeqCx.exactAt_link_splitSeq
end

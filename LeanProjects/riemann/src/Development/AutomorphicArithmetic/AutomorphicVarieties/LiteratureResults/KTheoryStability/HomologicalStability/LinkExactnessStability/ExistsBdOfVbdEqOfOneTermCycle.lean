import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff

noncomputable section

namespace GlobalTheory.SeqCx.OneTermEnd

open GlobalTheory.SeqCx

open Classical

def slicePr (V W : Type) (w : List W) : (List V × List W →₀ ℤ) →ₗ[ℤ] (List V →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun q : List V × List W =>
    if q.2 = w then Finsupp.single q.1 (1 : ℤ) else 0

theorem bd_single_one (V : Type) (u : V) :
    bd V (Finsupp.single [u] 1) = Finsupp.single ([] : List V) 1 := by
  simp [bd, Finsupp.linearCombination_single]

theorem lc_single_one (V : Type) (x : List V →₀ ℤ) :
    Finsupp.linearCombination ℤ (fun l : List V => Finsupp.single l (1:ℤ)) x = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, hf, hg]
  | single l c => rw [Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem slicePr_mapDomain (V W : Type) (w w' : List W) (x : List V →₀ ℤ) :
    slicePr V W w (Finsupp.mapDomain (fun l => (l, w')) x) = if w' = w then x else 0 := by
  unfold slicePr
  rw [Finsupp.linearCombination_mapDomain]
  split_ifs with h
  · simp [Function.comp_def, h, lc_single_one]
  · simp only [Function.comp_def, h, if_false]
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add, hf, hg, add_zero]
    | single l c => simp [Finsupp.linearCombination_single]

theorem slicePr_hbd (V W : Type) (w : List W) :
    (slicePr V W w).comp (hbd V W) = (bd V).comp (slicePr V W w) := by
  apply Finsupp.lhom_ext'
  rintro ⟨l, w'⟩
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [show hbd V W (Finsupp.single (l, w') 1) =
      Finsupp.mapDomain (fun x => (x, w')) (bd V (Finsupp.single l 1)) by
    simp [hbd, Finsupp.linearCombination_single]]
  rw [slicePr_mapDomain]
  simp only [slicePr, Finsupp.linearCombination_single, one_smul]
  split_ifs <;> simp

private theorem slicePr_apply_eq (V W : Type) (w : List W) (z : List V × List W →₀ ℤ)
    (l : List V) : slicePr V W w z l = z (l, w) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single q c =>
    obtain ⟨l', w'⟩ := q
    simp only [slicePr, Finsupp.linearCombination_single]
    by_cases h : w' = w
    · subst h
      simp [Finsupp.single_apply]
    · simp [h, Finsupp.single_apply, Ne.symm h]

theorem slicePr_mem {V W : Type} (D : Set (List V × List W)) (p b : ℕ) (w : List W) :
    ∀ z ∈ chains2 D p b, slicePr V W w z ∈ chains {l | (l, w) ∈ D} p := by
  intro z hz
  rw [chains, Finsupp.mem_supported]
  intro l hl
  rw [Finset.mem_coe, Finsupp.mem_support_iff, slicePr_apply_eq] at hl
  have h := (Finsupp.mem_supported ℤ z).mp hz (Finsupp.mem_support_iff.mpr hl)
  exact ⟨h.1, h.2.1⟩

theorem vbd_eq {V W : Type} (D : Set (List V × List W)) (p : ℕ) :
    ∀ z ∈ chains2 D p 1, vbd V W z =
      Finsupp.mapDomain (fun l => (l, ([] : List W))) (Finsupp.mapDomain Prod.fst z) := by
  intro z hz
  have hs := (Finsupp.mem_supported ℤ z).mp hz
  have e : ∀ y : List V × List W →₀ ℤ,
      Finsupp.mapDomain (fun l => (l, ([] : List W))) (Finsupp.mapDomain Prod.fst y) =
      ((Finsupp.lmapDomain ℤ ℤ (fun l : List V => (l, ([] : List W)))).comp
        (Finsupp.lmapDomain ℤ ℤ (Prod.fst : List V × List W → List V))) y := fun y => rfl
  rw [e]
  conv_lhs => rw [← Finsupp.sum_single z]
  conv_rhs => rw [← Finsupp.sum_single z]
  rw [map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro q hq
  obtain ⟨l, w⟩ := q
  have h := hs hq
  obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp h.2.2
  subst hu
  simp [vbd, Finsupp.linearCombination_single, bd_single_one, Finsupp.mapDomain_single,
    Finsupp.smul_single]

theorem sum_slicePr {V W : Type} (z : List V × List W →₀ ℤ) (U : Finset (List W))
    (hU : ∀ q ∈ z.support, q.2 ∈ U) :
    ∑ w ∈ U, slicePr V W w z = Finsupp.mapDomain Prod.fst z := by
  unfold Finsupp.mapDomain
  conv_lhs => rw [← Finsupp.sum_single z]
  simp only [Finsupp.sum, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  simp [slicePr, Finsupp.linearCombination_single, hU q hq, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finsupp.smul_single]

theorem exists_sum_bd {V : Type} (F : Set (List V)) (p : ℕ) {ι : Type} (S : Finset ι)
    (f : ι → List V →₀ ℤ) (hS : ∀ i ∈ S, ∃ b ∈ chains F (p + 1), bd V b = f i) :
    ∃ b ∈ chains F (p + 1), bd V b = ∑ i ∈ S, f i := by
  choose! g hg1 hg2 using hS
  refine ⟨∑ i ∈ S, g i, Submodule.sum_mem _ (fun i hi => hg1 i hi), ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i hi => hg2 i hi)

theorem bd_of_oneTerm_cycle : ∀ (V W : Type) (D : Set (List V × List W)) (F : Set (List V)) (p : ℕ),
    (∀ u : W, (∃ l, (l, [u]) ∈ D) → ∀ c ∈ chains {l | (l, [u]) ∈ D} p, bd V c = 0 →
      ∃ b ∈ chains F (p + 1), bd V b = c) →
    ∀ z ∈ chains2 D p 1, hbd V W z = 0 → ∀ c : List V →₀ ℤ,
      vbd V W z = Finsupp.mapDomain (fun l => (l, ([] : List W))) c →
      ∃ b ∈ chains F (p + 1), bd V b = c := by
  intro V W D F p hyp z hz hh c hc
  rw [vbd_eq D p z hz] at hc
  have hinj : Function.Injective (fun l : List V => (l, ([] : List W))) :=
    fun a b h => (Prod.ext_iff.mp h).1
  have hc' : c = Finsupp.mapDomain Prod.fst z := (Finsupp.mapDomain_injective hinj hc).symm
  have hs := (Finsupp.mem_supported ℤ z).mp hz
  have hU : ∀ q ∈ z.support, q.2 ∈ z.support.image Prod.snd :=
    fun q hq => Finset.mem_image_of_mem _ hq
  rw [hc', ← sum_slicePr z _ hU]
  apply exists_sum_bd
  intro w hw
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hw
  have h := hs hq
  obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp h.2.2
  have hmem := slicePr_mem D p 1 q.2 z hz
  have hbd0 : bd V (slicePr V W q.2 z) = 0 := by
    have key := LinearMap.congr_fun (slicePr_hbd V W q.2) z
    simp only [LinearMap.comp_apply] at key
    rw [← key, hh, map_zero]
  have hD : (q.1, [u]) ∈ D := by
    rw [← hu]
    exact h.1
  rw [hu] at hmem hbd0
  rw [hu]
  exact hyp u ⟨q.1, hD⟩ _ hmem hbd0

end GlobalTheory.SeqCx.OneTermEnd

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.exists_bd_of_vbd_eq_of_oneTerm_cycle : ∀ (V W : Type) (D : Set (List V × List W)) (F : Set (List V)) (p : ℕ), (∀ u : W, (∃ l, (l, [u]) ∈ D) → ∀ c ∈ chains {l | (l, [u]) ∈ D} p, bd V c = 0 → ∃ b ∈ chains F (p + 1), bd V b = c) → ∀ z ∈ chains2 D p 1, hbd V W z = 0 → ∀ c : List V →₀ ℤ, vbd V W z = Finsupp.mapDomain (fun l => (l, ([] : List W))) c → ∃ b ∈ chains F (p + 1), bd V b = c := by
  first
  | exact @GlobalTheory.SeqCx.OneTermEnd.bd_of_oneTerm_cycle
  | exact @GlobalTheory.SeqCx.OneTermEnd.exists_sum_bd
  | exact @GlobalTheory.SeqCx.OneTermEnd.sum_slicePr
  | exact @GlobalTheory.SeqCx.OneTermEnd.vbd_eq
  | exact @GlobalTheory.SeqCx.OneTermEnd.slicePr_mem
  | exact @GlobalTheory.SeqCx.OneTermEnd.slicePr_hbd
  | exact @GlobalTheory.SeqCx.OneTermEnd.slicePr_mapDomain
  | exact @GlobalTheory.SeqCx.OneTermEnd.lc_single_one
  | exact @GlobalTheory.SeqCx.OneTermEnd.bd_single_one
end

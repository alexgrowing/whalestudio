import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassSteps
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmAExpand
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace FlagHeightMultilinear

theorem exists_perm_toList {α : Type} [DecidableEq α] {d : ℕ} (r : Fin d → α) :
    ∃ σ : Equiv.Perm (Fin d), ∀ (k : Fin d) (h : (k : ℕ) < (Multiset.map r Finset.univ.val).toList.length),
      (Multiset.map r Finset.univ.val).toList.get ⟨k, h⟩ = r (σ k) := by
  set l := (Multiset.map r Finset.univ.val).toList with hl
  have hlen : l.length = d := by simp [hl, Multiset.length_toList]
  let r' : Fin d → α := fun k => l.get ⟨k, by rw [hlen]; exact k.2⟩
  have hmap : Multiset.map r' Finset.univ.val = Multiset.map r Finset.univ.val := by
    rw [Fin.univ_val_map]
    have hof : List.ofFn r' = l := List.ext_get (by simp [hlen]) (fun k h1 h2 => by simp [r'])
    rw [hof, hl, Multiset.coe_toList]
  have hcard : ∀ a, Fintype.card {k // r' k = a} = Fintype.card {k // r k = a} := by
    intro a
    have h := congrArg (Multiset.count a) hmap
    rw [Multiset.count_map, Multiset.count_map] at h
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [Finset.card, Finset.filter_val]
    convert h using 3 <;> exact eq_comm
  refine ⟨Equiv.ofFiberEquiv (fun a => Fintype.equivOfCardEq (hcard a)), fun k h => ?_⟩
  exact (Equiv.ofFiberEquiv_map (fun a => Fintype.equivOfCardEq (hcard a)) k).symm

section FS

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isSmoothHerm_fsHerm (a : K → ℤ) : IsSmoothHerm (fsHerm ι a) := by
  have h := Inter.isSmoothHerm_ofMetrics_fs (ι := ι) a
  unfold IsSmoothHerm at h ⊢
  refine h.congr fun z _ => ?_
  rw [fsHerm_h, Inter.ofMetrics_fs_h]
  unfold refNorm
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← sq_rpow_half (Real.sqrt_nonneg _) (a k),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

theorem refNorm_mul {a b : K → ℤ} {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    refNorm a z * refNorm b z = refNorm (a + b) z := by
  unfold refNorm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  obtain ⟨i, hi⟩ := hz k
  have hpos : 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 :=
    Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
  rw [← Real.rpow_add hpos]
  congr 1
  simp only [Pi.add_apply, Int.cast_add]
  ring

variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}

theorem I_snoc_congr (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) (L : Fin n → HermLine ι)
    (hL : ∀ j, IsSmoothHerm (L j)) {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (ha : A.a = B.a) (hh : ∀ z ∈ mcPts P, A.h z = B.h z) :
    I P (n + 1) (Fin.snoc L A) = I P (n + 1) (Fin.snoc L B) := by
  have hBi := Inter.isSmoothHerm_hermZpow hB (-1)
  have h0 := Inter.DiagRAux.I_snoc_triv hI hP hL (Inter.isSmoothHerm_tensor hA hBi)
    (by
      show A.a + (Inter.hermZpow B (-1)).a = 0
      rw [Inter.DiagRAux.hermZpow_neg_one_a, ha, add_neg_cancel])
    (fun z hz => by
      show A.h z * (Inter.hermZpow B (-1)).h z = 1
      rw [Inter.DiagRAux.hermZpow_neg_one_h, hh z hz, mul_inv_cancel₀ (B.pos z hz.1).ne'])
  have h1 := hI.2.1 P n L A (Inter.hermZpow B (-1)) hP hL hA hBi
  have h2 := Inter.fam_snoc_zpow hI hP L hL hB (-1)
  rw [h0, h2] at h1
  push_cast at h1
  linarith

theorem I_snoc_fsHerm_add (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) (L : Fin n → HermLine ι)
    (hL : ∀ j, IsSmoothHerm (L j)) (a b : K → ℤ) :
    I P (n + 1) (Fin.snoc L (fsHerm ι (a + b))) =
      I P (n + 1) (Fin.snoc L (fsHerm ι a)) + I P (n + 1) (Fin.snoc L (fsHerm ι b)) := by
  rw [← hI.2.1 P n L _ _ hP hL (isSmoothHerm_fsHerm a) (isSmoothHerm_fsHerm b)]
  exact I_snoc_congr hI hP L hL (isSmoothHerm_fsHerm _)
    (Inter.isSmoothHerm_tensor (isSmoothHerm_fsHerm a) (isSmoothHerm_fsHerm b)) rfl
    (fun z hz => (refNorm_mul hz.1).symm)

theorem I_update_fsHerm_add (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (v : Fin (n + 1) → K → ℤ) (j : Fin (n + 1)) (a b : K → ℤ) :
    I P (n + 1) (fun i => fsHerm ι (Function.update v j (a + b) i)) =
      I P (n + 1) (fun i => fsHerm ι (Function.update v j a i)) +
        I P (n + 1) (fun i => fsHerm ι (Function.update v j b i)) := by
  have hL : ∀ i, IsSmoothHerm (fsHerm ι (v i)) := fun i => isSmoothHerm_fsHerm _
  have e : ∀ c : K → ℤ, (fun i => fsHerm ι (Function.update v j c i)) =
      Function.update (fun i => fsHerm ι (v i)) j (fsHerm ι c) := by
    intro c
    funext i
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [Function.update_of_ne h]
  rw [e, e, e, Inter.fam_update_eq_snoc hI hP _ hL j (isSmoothHerm_fsHerm _),
    Inter.fam_update_eq_snoc hI hP _ hL j (isSmoothHerm_fsHerm _),
    Inter.fam_update_eq_snoc hI hP _ hL j (isSmoothHerm_fsHerm _)]
  exact I_snoc_fsHerm_add hI hP _ (fun i => hL _) a b

def fsMultilin (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) :
    MultilinearMap ℤ (fun _ : Fin (n + 1) => K → ℤ) ℝ where
  toFun v := I P (n + 1) (fun i => fsHerm ι (v i))
  map_update_add' := by
    intro inst v j a b
    have e : inst = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
    subst e
    exact I_update_fsHerm_add hI hP v j a b
  map_update_smul' := by
    intro inst v j c a
    have e : inst = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
    subst e
    let g : (K → ℤ) →+ ℝ := AddMonoidHom.mk' (fun a => I P (n + 1) (fun i => fsHerm ι (Function.update v j a i)))
      (fun a b => I_update_fsHerm_add hI hP v j a b)
    exact map_zsmul g c a

theorem fsMultilin_apply (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) (v : Fin (n + 1) → K → ℤ) :
    fsMultilin hI hP v = I P (n + 1) (fun i => fsHerm ι (v i)) := rfl

theorem I_fsHerm_sum (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {α : Type} [Fintype α]
    (ℓ : Fin (n + 1) → α → ℤ) (x : α → K → ℤ) :
    I P (n + 1) (fun i => fsHerm ι (∑ p, ℓ i p • x p)) =
      ∑ r : Fin (n + 1) → α, (∏ i, (ℓ i (r i) : ℝ)) * I P (n + 1) (fun i => fsHerm ι (x (r i))) := by
  rw [← fsMultilin_apply hI hP, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ (fsMultilin hI hP) (fun i => ℓ i (r i)) (fun i => x (r i)),
    fsMultilin_apply, zsmul_eq_mul, Int.cast_prod]

end FS

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

theorem hFl_sum_monomial (II : IntersectionSystem) {β : Type} (s : Finset β) (m : β → (Ψ × Fin N) →₀ ℕ)
    (a : β → ℚ) :
    hFl Ψ N II (∑ b ∈ s, monomial (m b) (a b)) = ∑ b ∈ s, (a b : ℝ) * hFlMono Ψ N II (m b) := by
  classical
  have hsub : ∀ (F : RootPoly Ψ N) (S : Finset ((Ψ × Fin N) →₀ ℕ)), F.support ⊆ S →
      hFl Ψ N II F = ∑ m ∈ S, ((coeff m F : ℚ) : ℝ) * hFlMono Ψ N II m := by
    intro F S hS
    unfold hFl
    exact Finset.sum_subset hS fun m _ hm => by rw [notMem_support_iff.mp hm]; simp
  have hadd : ∀ F G : RootPoly Ψ N, hFl Ψ N II (F + G) = hFl Ψ N II F + hFl Ψ N II G := by
    intro F G
    rw [hsub (F + G) (F.support ∪ G.support) support_add,
      hsub F (F.support ∪ G.support) Finset.subset_union_left,
      hsub G (F.support ∪ G.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_add]
    push_cast
    ring
  have hmono : ∀ (m : (Ψ × Fin N) →₀ ℕ) (a : ℚ), hFl Ψ N II (monomial m a) = (a : ℝ) * hFlMono Ψ N II m := by
    intro m a
    rw [hsub _ {m} support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]
  induction s using Finset.induction_on with
  | empty => simp [hsub 0 ∅ (by simp)]
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, hadd, hmono, ih]

omit [DecidableEq Ψ] in

theorem C_mul_prod_linForm (c : ℚ) {d : ℕ} (ℓ : Fin d → Ψ × Fin N → ℤ) :
    (C c * ∏ i, linForm Ψ N (ℓ i) : RootPoly Ψ N) =
      ∑ r : Fin d → Ψ × Fin N, monomial (∑ i, Finsupp.single (r i) 1) (c * ∏ i, (ℓ i (r i) : ℚ)) := by
  unfold linForm
  rw [Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← C_mul_monomial]
  congr 1
  rw [show (∏ i, (ℓ i (r i) : ℚ)) = (∏ i, (ℓ i (r i) : ℚ)) * 1 from (mul_one _).symm, ← C_mul_monomial,
    monomial_sum_one]
  simp only [smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]
  rfl

theorem hFlMono_sum_single (II : IntersectionSystem) (hII : IsIntersectionSystem II)
    (hP : IsArithVar (PFl Ψ N) (dimFl Ψ N + 1)) (r : Fin (dimFl Ψ N + 1) → Ψ × Fin N) :
    hFlMono Ψ N II (∑ i, Finsupp.single (r i) 1) =
      II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (dimFl Ψ N + 1) (fun i => xLine Ψ N (r i)) := by
  have hdeg : (∑ i, Finsupp.single (r i) (1 : ℕ)).degree = dimFl Ψ N + 1 := by
    rw [map_sum]
    simp [Finsupp.degree_single]
  have hm : Finsupp.toMultiset (∑ i, Finsupp.single (r i) (1 : ℕ)) = Multiset.map r Finset.univ.val := by
    rw [Finsupp.toMultiset_sum]
    simp only [Finsupp.toMultiset_single, one_smul]
    rw [Finset.sum_eq_multiset_sum]
    have e : (fun i => ({r i} : Multiset (Ψ × Fin N))) = (fun p => {p}) ∘ r := rfl
    rw [e, ← Multiset.map_map, Multiset.sum_map_singleton]
  obtain ⟨σ, hσ⟩ := exists_perm_toList r
  have hML : monoLines Ψ N (∑ i, Finsupp.single (r i) 1) (dimFl Ψ N + 1) = (fun i => xLine Ψ N (r i)) ∘ σ := by
    funext k
    have hk : (k : ℕ) < (Multiset.map r Finset.univ.val).toList.length := by
      have := k.2
      simp [Multiset.length_toList]
      omega
    unfold monoLines
    rw [hm, dif_pos hk, hσ k hk]
    rfl
  unfold hFlMono
  rw [if_pos hdeg, hML]
  exact (hII (FlBlock Ψ N) (FlIdx Ψ N)).1 _ _ _ σ hP fun j => isSmoothHerm_fsHerm _

end FlagHeightMultilinear

open FlagHeightMultilinear in

theorem HFlProdLinear.proof (hA : FlagArithVar.Statement) : HFlProdLinear.Statement := by
  intro II Ψ _ _ _ N d c ℓ hII hN hd
  subst hd
  have hP := hA Ψ N hN
  have hI := hII (FlBlock Ψ N) (FlIdx Ψ N)
  rw [C_mul_prod_linForm, hFl_sum_monomial]
  have hlin : (fun i => linLine Ψ N (ℓ i)) =
      fun i => fsHerm (FlIdx Ψ N) (∑ p, ℓ i p • xDeg Ψ N p) := by
    funext i
    unfold linLine linDeg
    congr 1
    funext q
    simp [Finset.sum_apply]
  rw [hlin, I_fsHerm_sum hI hP, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hFlMono_sum_single Ψ N II hII hP r]
  simp only [xLine]
  push_cast
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree

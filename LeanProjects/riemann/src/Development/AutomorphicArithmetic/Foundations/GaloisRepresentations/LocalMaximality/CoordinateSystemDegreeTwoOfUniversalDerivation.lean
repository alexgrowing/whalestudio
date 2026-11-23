import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem wd_single' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (f : Finset ι → E) (i : ι) : wd w f {i} = w i (f ∅) := by
  have s1 : GlobalTheory.cubeSign ({i} : Finset ι) i = 1 := GlobalTheory.cubeSign_singleton i
  simp [wd, s1]

private theorem wd_pair' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (f : Finset ι → E) {i i' : ι} (h : i < i') :
    wd w f {i, i'} = w i (f {i'}) - w i' (f {i}) := by
  have hne : i ≠ i' := ne_of_lt h
  have s1 : GlobalTheory.cubeSign {i, i'} i = 1 := by
    apply GlobalTheory.cubeSign_eq_one_of_forall_le
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact le_rfl
    · rw [Finset.mem_singleton.mp hj]; exact le_of_lt h
  have s2 : GlobalTheory.cubeSign {i, i'} i' = -1 := by
    have : ({x ∈ ({i, i'} : Finset _) | x < i'}) = {i} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · rfl
        · exact absurd hx (lt_irrefl _)
      · rintro rfl; exact ⟨Or.inl rfl, h⟩
    simp [GlobalTheory.cubeSign, this]
  have e1 : ({i, i'} : Finset _).erase i = {i'} := by
    rw [Finset.erase_insert (by simpa using hne)]
  have e2 : ({i, i'} : Finset _).erase i' = {i} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl⟩
      · rfl
      · exact absurd rfl hx
    · rintro rfl; exact ⟨hne, Or.inl rfl⟩
  simp only [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  rw [Finset.sum_pair hne, s1, s2, e1, e2, one_smul, neg_one_smul, sub_eq_add_neg]

private theorem pair_lt' {ι : Type} [LinearOrder ι] {s : Finset ι} (h : s.card = 2) :
    ∃ x y, x < y ∧ s = {x, y} := by
  obtain ⟨x, y, hne, rfl⟩ := Finset.card_eq_two.1 h
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact ⟨x, y, h', rfl⟩
  · exact ⟨y, x, h', Finset.pair_comm _ _⟩

theorem UpperTheory.Gal.productCup_of_system.coordinateSystem_degree_two_of_universalDerivation :
    L2 → SysOk → WdUni → CechKoszulSystemCocycleGluing := by
  intro hL2 hOk h d S E _ _ _ _ T κ _ _ n z hG hAd hKE c0 hZ hB1 hB2
  obtain ⟨hW, -, -⟩ := hOk d S E T κ n z hG hAd
  have lu1 : ∀ (b : Finset (Two d)) (L : Finset κ), lft (uni b L) = b :=
    fun b L => (h (Two d) κ ℂ 0 0 b L).2.1
  have ru1 : ∀ (b : Finset (Two d)) (L : Finset κ), rgt (uni b L) = L :=
    fun b L => (h (Two d) κ ℂ 0 0 b L).2.2.1
  have lu2 : ∀ (I J : Finset (Fin (d + 1))), lft (uni I J) = I :=
    fun I J => (h (Fin (d + 1)) (Fin (d + 1)) ℂ 0 0 I J).2.1
  have ru2 : ∀ (I J : Finset (Fin (d + 1))), rgt (uni I J) = J :=
    fun I J => (h (Fin (d + 1)) (Fin (d + 1)) ℂ 0 0 I J).2.2.1
  have cu2 : ∀ (I J : Finset (Fin (d + 1))), (uni I J).card = I.card + J.card :=
    fun I J => (h (Fin (d + 1)) (Fin (d + 1)) ℂ 0 0 I J).2.2.2.1
  have ul2 : ∀ (s : Finset (Two d)), uni (lft s) (rgt s) = s :=
    fun s => (h (Fin (d + 1)) (Fin (d + 1)) ℂ 0 0 ∅ ∅).2.2.2.2 s
  set A : Finset (Two d ⊕ₗ κ) → Submodule ℂ E := fun s ↦ mixF (fun I J ↦
    Submodule.map (T.act ↑(∏ l ∈ rgt s, T.u n (pk I) (pk J) l)) (T.M I J)) (lft s) with hAdef
  have hcol : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty →
      colA A (T.wt z) (uni I J) = T.colCx n z I J := by
    intro I J hI hJ
    simp only [colA, Sys.colCx, kosT]
    congr 1
    funext L
    simp only [A, mixF, lu1, ru1, lu2, ru2, hI, hJ, and_self, if_true]
  have hbot : ∀ b : Finset (Two d), ¬ ((lft b).Nonempty ∧ (rgt b).Nonempty) → ∀ L,
      A (uni b L) = ⊥ := by
    intro b hb L
    simp only [A, mixF, lu1, ru1]
    rw [if_neg hb]
  set c0' : Finset (Two d) → Finset κ → E := fun b =>
    if (lft b).card = 1 ∧ (rgt b).card = 1 then c0 (pk (lft b)) (pk (rgt b)) else 0 with hc0'
  have pk1 : ∀ i : Fin (d + 1), pk ({i} : Finset (Fin (d + 1))) = i := by
    intro i; simp [pk]
  have c0ij : ∀ i j : Fin (d + 1), c0' (uni {i} {j}) = c0 i j := by
    intro i j; simp [c0', lu2, ru2, pk1]
  have cv : ∀ I' J' : Finset (Fin (d + 1)), c0' (uni I' J') =
      if I'.card = 1 ∧ J'.card = 1 then c0 (pk I') (pk J') else 0 := by
    intro I' J'; simp only [hc0', lu2, ru2]
  have hKEA : ∀ b : Finset (Two d), KE (colA A (T.wt z) b) d := by
    intro b
    by_cases hb : (lft b).Nonempty ∧ (rgt b).Nonempty
    · rw [← ul2 b, hcol _ _ hb.1 hb.2]
      exact hKE _ _ hb.1 hb.2
    · intro m _ x hx
      have hx0 : x = 0 := by
        funext L
        have h1 := (Submodule.mem_inf.mp hx).1
        have h2 := (Submodule.mem_pi.mp h1) L (Set.mem_univ _)
        simpa [hbot b hb L] using h2
      rw [hx0]
      exact zero_mem _
  have hZA : ∀ b : Finset (Two d), (b.card : ℤ) = (d : ℤ) + 2 - d →
      c0' b ∈ (colA A (T.wt z) b).Z d := by
    intro b hbc
    by_cases h11 : (lft b).card = 1 ∧ (rgt b).card = 1
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h11.1
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h11.2
      have hb' : b = uni {i} {j} := by rw [← hi, ← hj, ul2]
      subst hb'
      rw [c0ij, hcol _ _ (Finset.singleton_nonempty i) (Finset.singleton_nonempty j)]
      exact hZ i j
    · have h0 : c0' b = 0 := by simp only [hc0', h11, if_false]
      rw [h0]
      exact zero_mem _
  have hw : (fun i : Two d => T.wt z (inlE i : Two d ⊕ₗ κ)) = fun _ => 1 := by
    funext i; simp [Sys.wt, inlE]
  have hBA : ∀ b : Finset (Two d), (b.card : ℤ) = (d : ℤ) + 2 - d + 1 →
      (fun L => (wd fun i => T.wt z (inlE i)) (fun b' => c0' b' L) b) ∈ (colA A (T.wt z) b).B d := by
    intro b hbc
    have hb3 : b.card = 3 := by omega
    rw [hw]
    obtain ⟨I, J, rfl⟩ : ∃ I J, b = uni I J := ⟨lft b, rgt b, (ul2 b).symm⟩
    have hIJ : I.card + J.card = 3 := by rw [← cu2]; exact hb3
    have dec : ∀ L, (wd fun _ : Two d => (1 : Module.End ℂ E)) (fun b' => c0' b' L) (uni I J) =
        (wd fun _ => 1) (fun I' => c0' (uni I' J) L) I +
          (-1) ^ I.card • (wd fun _ => 1) (fun J' => c0' (uni I J') L) J :=
      fun L => (h (Fin (d + 1)) (Fin (d + 1)) E (fun _ => 1) (fun b' => c0' b' L) I J).1
    have hcases : I.card = 0 ∨ I.card = 1 ∨ I.card = 2 ∨ I.card = 3 := by omega
    rcases hcases with hI | hI | hI | hI
    · have hI0 : I = ∅ := Finset.card_eq_zero.mp hI
      subst hI0
      have hf : (fun L => (wd fun _ : Two d => (1 : Module.End ℂ E)) (fun b' => c0' b' L) (uni ∅ J)) = 0 := by
        funext L
        rw [dec]
        have z1 : (fun J' => c0' (uni ∅ J') L) = 0 := by
          funext J'; simp [cv]
        rw [z1, map_zero]
        simp [wd]
      rw [hf]
      exact zero_mem _
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hI
      have hJ2 : J.card = 2 := by simp at hIJ; omega
      obtain ⟨j, j', hjj, rfl⟩ := pair_lt' hJ2
      have hf : (fun L => (wd fun _ : Two d => (1 : Module.End ℂ E)) (fun b' => c0' b' L) (uni {i} {j, j'})) =
          c0 i j - c0 i j' := by
        funext L
        rw [dec, wd_single', wd_pair' _ _ hjj]
        simp [cv, pk1]
      rw [hf, hcol _ _ (Finset.singleton_nonempty i) (Finset.insert_nonempty _ _)]
      exact hB2 i j j'
    · obtain ⟨i, i', hii, rfl⟩ := pair_lt' hI
      have hJ1 : J.card = 1 := by omega
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hJ1
      have hf : (fun L => (wd fun _ : Two d => (1 : Module.End ℂ E)) (fun b' => c0' b' L) (uni {i, i'} {j})) =
          -(c0 i j - c0 i' j) := by
        funext L
        rw [dec, wd_single', wd_pair' _ _ hii]
        simp [cv, pk1, Finset.card_pair (ne_of_lt hii)]
      rw [hf, hcol _ _ (Finset.insert_nonempty _ _) (Finset.singleton_nonempty j)]
      exact neg_mem (hB1 i i' j)
    · have hJ0 : J = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hJ0
      have hf : (fun L => (wd fun _ : Two d => (1 : Module.End ℂ E)) (fun b' => c0' b' L) (uni I ∅)) = 0 := by
        funext L
        rw [dec]
        have z1 : (fun I' => c0' (uni I' ∅) L) = 0 := by
          funext I'; simp [cv]
        rw [z1, map_zero]
        simp [wd]
      rw [hf]
      exact zero_mem _
  obtain ⟨c, hc, hcb, -⟩ := hL2 (Two d) κ E A (T.wt z) d (d + 2) hW hKEA c0' hZA hBA
  refine ⟨c, hc, fun i j => ?_⟩
  have := hcb (uni {i} {j}) (by rw [cu2]; simp)
  rw [this, c0ij]

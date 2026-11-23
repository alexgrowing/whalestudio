import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharacterLabelUniqueGLnStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvariStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspidalListHarishChandraPairingNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterPairingHarishChandraCuspidalMackeyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentralStatement

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.Label

theorem ip_add_left {G : Type} [Group G] [Fintype G] (a b c : G → ℂ) : ip (a + b) c = ip a c + ip b c := by
  unfold ip
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem ip_add_right {G : Type} [Group G] [Fintype G] (a b c : G → ℂ) : ip a (b + c) = ip a b + ip a c := by
  unfold ip
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ip_irr_sum {G : Type} [Group G] [Fintype G] (χ : G → ℂ) (hχ : IsIrr χ) (B : List (G → ℂ))
    (hB : ∀ ρ ∈ B, IsIrr ρ) : ∃ m : ℕ, ip χ B.sum = m ∧ (m ≠ 0 ↔ χ ∈ B) := by
  induction B with
  | nil => exact ⟨0, by unfold ip; simp, by simp⟩
  | cons ρ B ih =>
    obtain ⟨m, hm, hmB⟩ := ih (fun r hr => hB r (by simp [hr]))
    have hρ : IsIrr ρ := hB ρ (by simp)
    refine ⟨(if χ = ρ then 1 else 0) + m, ?_, ?_⟩
    · rw [List.sum_cons, ip_add_right, (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G χ ρ hχ hρ).2.2, hm]
      split_ifs <;> push_cast <;> ring
    · rw [List.mem_cons, ← hmB]
      by_cases h : χ = ρ
      · simp [h]
      · simp [h]

theorem ip_sum_sum {G : Type} [Group G] [Fintype G] (A B : List (G → ℂ)) (hA : ∀ ρ ∈ A, IsIrr ρ)
    (hB : ∀ ρ ∈ B, IsIrr ρ) : ∃ m : ℕ, ip A.sum B.sum = m ∧ (∀ χ ∈ A, χ ∈ B → m ≠ 0) := by
  induction A with
  | nil => exact ⟨0, by unfold ip; simp, by simp⟩
  | cons ρ A ih =>
    obtain ⟨m, hm, hmA⟩ := ih (fun r hr => hA r (by simp [hr]))
    obtain ⟨k, hk, hkB⟩ := ip_irr_sum ρ (hA ρ (by simp)) B hB
    refine ⟨k + m, ?_, ?_⟩
    · rw [List.sum_cons, ip_add_left, hk, hm]
      push_cast
      ring
    · intro χ hχ hχB
      rcases List.mem_cons.1 hχ with rfl | h
      · have := hkB.2 hχB
        omega
      · have := hmA χ h hχB
        omega

theorem ip_ne_zero_of_common {G : Type} [Group G] [Fintype G] (χ α β : G → ℂ) (hχ : IsIrr χ)
    (hα : IsChar α) (hβ : IsChar β) (h1 : ip χ α ≠ 0) (h2 : ip χ β ≠ 0) : ip α β ≠ 0 := by
  obtain ⟨A, hA, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G α).1 hα
  obtain ⟨B, hB, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G β).1 hβ
  obtain ⟨m1, h1m, h1A⟩ := ip_irr_sum χ hχ A hA
  obtain ⟨m2, h2m, h2B⟩ := ip_irr_sum χ hχ B hB
  obtain ⟨m, hm, hmm⟩ := ip_sum_sum A B hA hB
  have hχA : χ ∈ A := h1A.1 (fun h0 => h1 (by rw [h1m, h0]; simp))
  have hχB : χ ∈ B := h2B.1 (fun h0 => h2 (by rw [h2m, h0]; simp))
  rw [hm]
  exact_mod_cast hmm χ hχA hχB

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

variable {g : ℕ} [Fact g.Prime]

noncomputable def lab (L : LabelDatum g) (c : Pc g) : (ZMod g)[X] :=
  if h : ∃ P, IsCuspOf L P c.2 then h.choose else 0

theorem lab_eq (L : LabelDatum g) (hg : 5 ≤ g) (c : Pc g) (P : (ZMod g)[X]) (h : IsCuspOf L P c.2) :
    lab L c = P := by
  have hex : ∃ P, IsCuspOf L P c.2 := ⟨P, h⟩
  unfold lab
  rw [dif_pos hex]
  exact ((GlobalTheory.T.cuspidalCharacter_label_unique_GLn g L hg c.1 P _ c.2 c.2 h).1 hex.choose_spec).symm

theorem map_fst_eq (L : LabelDatum g) (hg : 5 ≤ g) (Q : List ((ZMod g)[X] × Pc g))
    (hQ : ∀ p ∈ Q, IsCuspOf L p.1 p.2.2) : Q.map Prod.fst = (Q.map Prod.snd).map (lab L) := by
  rw [List.map_map]
  exact List.map_congr_left (fun p hp => (lab_eq L hg p.2 p.1 (hQ p hp)).symm)

theorem cusp_snd (L : LabelDatum g) (Q : List ((ZMod g)[X] × Pc g))
    (hQ : ∀ p ∈ Q, IsCuspOf L p.1 p.2.2) : ∀ c ∈ Q.map Prod.snd, IsCusp c.2 := by
  intro c hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  exact (hQ p hp).2.1

theorem char_snd (L : LabelDatum g) (Q : List ((ZMod g)[X] × Pc g))
    (hQ : ∀ p ∈ Q, IsCuspOf L p.1 p.2.2) : ∀ c ∈ Q.map Prod.snd, IsChar c.2 := by
  intro c hc
  exact isChar_of_isIrr (cusp_snd L Q hQ c hc).2.1

theorem prod_props (L : LabelDatum g) (Q : List ((ZMod g)[X] × Pc g))
    (hQ : ∀ p ∈ Q, IsCuspOf L p.1 p.2.2) : (Q.map Prod.fst).prod.Monic ∧
      (Q.map Prod.fst).prod.natDegree = degL (Q.map Prod.snd) ∧ (Q.map Prod.fst).prod.coeff 0 ≠ 0 := by
  induction Q with
  | nil => simp [degL]
  | cons p Q ih =>
    obtain ⟨⟨hm, -, h0, hd⟩, -, -⟩ := hQ p (by simp)
    obtain ⟨ihm, ihd, ih0⟩ := ih (fun q hq => hQ q (by simp [hq]))
    simp only [List.map_cons, List.prod_cons]
    refine ⟨hm.mul ihm, ?_, ?_⟩
    · rw [hm.natDegree_mul ihm, ihd, hd]
      simp [degL]
    · rw [Polynomial.mul_coeff_zero]
      exact mul_ne_zero h0 ih0

theorem factors_prod (L : LabelDatum g) (Q : List ((ZMod g)[X] × Pc g))
    (hQ : ∀ p ∈ Q, IsCuspOf L p.1 p.2.2) :
    ((Q.map Prod.fst : List _) : Multiset _) =
      UniqueFactorizationMonoid.normalizedFactors (Q.map Prod.fst).prod := by
  have hirr : ∀ a ∈ ((Q.map Prod.fst : List (ZMod g)[X]) : Multiset (ZMod g)[X]), Irreducible a ∧ a.Monic := by
    intro a ha
    rw [Multiset.mem_coe, List.mem_map] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    exact ⟨(hQ p hp).1.2.1, (hQ p hp).1.1⟩
  rw [← Multiset.prod_coe, UniqueFactorizationMonoid.normalizedFactors_prod_eq _ (fun a ha => (hirr a ha).1)]
  conv_lhs => rw [← Multiset.map_id' ((Q.map Prod.fst : List (ZMod g)[X]) : Multiset (ZMod g)[X])]
  exact Multiset.map_congr rfl (fun a ha => ((hirr a ha).2.normalize_eq_self).symm)

theorem label_unique (L : LabelDatum g) (hg : 5 ≤ g) {n : ℕ} (χ : Gn g n → ℂ) (hχ : IsIrr χ)
    (f f' : (ZMod g)[X]) (h : HasLabel L χ f) (h' : HasLabel L χ f') : f = f' := by
  obtain ⟨Q, hQ, hdQ, rfl, hχQ⟩ := h
  obtain ⟨Q', hQ', hdQ', rfl, hχQ'⟩ := h'
  have hc := GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g (Q.map Prod.snd) (Q.map Prod.snd) n hdQ.symm (char_snd L Q hQ)
  have hc' := GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g (Q'.map Prod.snd) (Q'.map Prod.snd) n hdQ'.symm (char_snd L Q' hQ')
  have hne := ip_ne_zero_of_common χ _ _ hχ hc.1 hc'.1 hχQ hχQ'
  have hperm : (Q.map Prod.snd).Perm (Q'.map Prod.snd) := by
    by_contra hp
    exact hne ((GlobalTheory.T.characterPairing_harishChandra_cuspidal_mackey g _ _ n hdQ hdQ' (cusp_snd L Q hQ) (cusp_snd L Q' hQ')).1 hp)
  rw [map_fst_eq L hg Q hQ, map_fst_eq L hg Q' hQ']
  exact (hperm.map (lab L)).prod_eq

theorem label_exists (L : LabelDatum g) (hg : 5 ≤ g) (hG : Green) {n : ℕ} (χ : Gn g n → ℂ)
    (hχ : IsIrr χ) : ∃ f, HasLabel L χ f := by
  obtain ⟨C, hC, hdC, hip⟩ := GlobalTheory.T.exists_cuspidal_list_harishChandra_pairing_ne_zero g n χ hχ
  have hex : ∀ c ∈ C, ∃ P, IsCuspOf L P c.2 := by
    intro c hc
    obtain ⟨τ, hτ, -, hall⟩ := hG g L c.1 (hC c hc).1
    obtain ⟨P, hP, he⟩ := hall c.2 (hC c hc)
    refine ⟨P, ?_⟩
    rw [he]
    exact (hτ P hP).1
  have hmap : (C.map fun c => (lab L c, c)).map Prod.snd = C := by
    rw [List.map_map]
    exact List.map_id'' (fun _ => rfl) C
  refine ⟨((C.map fun c => (lab L c, c)).map Prod.fst).prod, C.map fun c => (lab L c, c), ?_, ?_, rfl, ?_⟩
  · intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
    have hc' := hex c hc
    show IsCuspOf L (lab L c) c.2
    unfold lab
    rw [dif_pos hc']
    exact hc'.choose_spec
  · rw [hmap]
    exact hdC
  · rw [hmap]
    exact hip

theorem exists_section (L : LabelDatum g) (hG : Green) : ∃ t : (P : (ZMod g)[X]) → Gn g P.natDegree → ℂ,
    ∀ P, IsPrimeLab P.natDegree P →
      IsCuspOf L P (t P) ∧ t P 1 = ∏ i ∈ Finset.Ico 1 P.natDegree, ((g : ℂ) ^ i - 1) := by
  refine ⟨fun P => if h : 0 < P.natDegree then (hG g L P.natDegree h).choose P else 0, ?_⟩
  intro P hP
  have hpos : 0 < P.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible hP.2.1)
  simp only [dif_pos hpos]
  exact (hG g L P.natDegree hpos).choose_spec.1 P hP

theorem squarefree_series (L : LabelDatum g) (hg : 5 ≤ g) (hG : Green) (n : ℕ) (f : (ZMod g)[X])
    (hm : f.Monic) (hn : f.natDegree = n) (h0 : f.coeff 0 ≠ 0) (hs : Squarefree f) :
    ∃ Q : List ((ZMod g)[X] × Pc g),
      (∀ p ∈ Q, IsCuspOf L p.1 p.2.2 ∧ p.2.2 1 = ∏ i ∈ Finset.Ico 1 p.2.1, ((g : ℂ) ^ i - 1)) ∧
      ((Q.map Prod.fst : List _) : Multiset _) = UniqueFactorizationMonoid.normalizedFactors f ∧
      degL (Q.map Prod.snd) = n ∧
      {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f} = {hcL (Q.map Prod.snd) n} := by
  obtain ⟨t, ht⟩ := exists_section L hG
  have hf0 : f ≠ 0 := hm.ne_zero
  set l := (UniqueFactorizationMonoid.normalizedFactors f).toList with hl
  have hmem : ∀ P ∈ l, IsPrimeLab P.natDegree P := by
    intro P hP
    rw [hl, Multiset.mem_toList] at hP
    have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP
    have hnorm := UniqueFactorizationMonoid.normalize_normalized_factor P hP
    obtain ⟨q, hq⟩ := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
    refine ⟨?_, hirr, ?_, rfl⟩
    · rw [← hnorm]
      exact Polynomial.monic_normalize hirr.ne_zero
    · intro hP0
      apply h0
      rw [hq, Polynomial.mul_coeff_zero, hP0, zero_mul]
  let s : (ZMod g)[X] → Pc g := fun P => ⟨P.natDegree, t P⟩
  set Q : List ((ZMod g)[X] × Pc g) := l.map fun P => (P, s P) with hQdef
  have hQ : ∀ p ∈ Q, IsCuspOf L p.1 p.2.2 ∧ p.2.2 1 = ∏ i ∈ Finset.Ico 1 p.2.1, ((g : ℂ) ^ i - 1) := by
    intro p hp
    obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hp
    exact ht P (hmem P hP)
  have hQc : ∀ p ∈ Q, IsCuspOf L p.1 p.2.2 := fun p hp => (hQ p hp).1
  have hQfst : Q.map Prod.fst = l := by
    rw [hQdef, List.map_map]
    exact List.map_id'' (fun _ => rfl) l
  have hQsnd : Q.map Prod.snd = (Q.map Prod.fst).map s := by
    simp only [hQdef, List.map_map]
    rfl
  have hcoe : ((Q.map Prod.fst : List _) : Multiset _) = UniqueFactorizationMonoid.normalizedFactors f := by
    rw [hQfst, hl, Multiset.coe_toList]
  obtain ⟨hpm, hpd, -⟩ := prod_props L Q hQc
  have hprod : (Q.map Prod.fst).prod = f := by
    have hassoc := UniqueFactorizationMonoid.prod_normalizedFactors hf0
    rw [← hcoe, Multiset.prod_coe] at hassoc
    exact Polynomial.eq_of_monic_of_associated hpm hm hassoc
  have hdeg : degL (Q.map Prod.snd) = n := by
    rw [← hpd, hprod, hn]
  have hlnd : l.Nodup := by
    have : (l : Multiset (ZMod g)[X]).Nodup := by
      rw [hl, Multiset.coe_toList]
      exact (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hf0).1 hs
    exact Multiset.coe_nodup.1 this
  have hnd : (Q.map Prod.snd).Nodup := by
    rw [hQsnd, hQfst]
    refine List.Nodup.map_on ?_ hlnd
    intro P hP P' hP' he
    have e1 := lab_eq L hg (s P) P (ht P (hmem P hP)).1
    have e2 := lab_eq L hg (s P') P' (ht P' (hmem P' hP')).1
    rw [← e1, ← e2, he]
  have hcusps := cusp_snd L Q hQc
  have hchar := (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g (Q.map Prod.snd) (Q.map Prod.snd) n hdeg.symm (char_snd L Q hQc)).1
  have hnorm1 := (GlobalTheory.T.characterPairing_harishChandra_cuspidal_mackey g _ _ n hdeg hdeg hcusps hcusps).2 hnd
  have hirr : IsIrr (hcL (Q.map Prod.snd) n) := (GlobalTheory.T.character_decomposition_and_classFunction_expansion _ _).2.2.2.1 hchar hnorm1
  refine ⟨Q, hQ, hcoe, hdeg, ?_⟩
  ext χ
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hχ, Q', hQ', hd', hf', hip'⟩
    have key : ∀ p ∈ Q', p.2 = s p.1 := by
      rintro ⟨P, d, χ'⟩ hp
      have hc := hQ' _ hp
      have hd : P.natDegree = d := hc.1.2.2.2
      subst hd
      have e := (GlobalTheory.T.cuspidalCharacter_label_unique_GLn g L hg P.natDegree P P (t P) χ' (ht P hc.1).1).2 hG hc
      show (⟨P.natDegree, χ'⟩ : Pc g) = ⟨P.natDegree, t P⟩
      rw [e]
    have hsnd' : Q'.map Prod.snd = (Q'.map Prod.fst).map s := by
      rw [List.map_map]
      exact List.map_congr_left key
    have hperm : (Q'.map Prod.fst).Perm (Q.map Prod.fst) := by
      apply Multiset.coe_eq_coe.1
      rw [factors_prod L Q' hQ', ← hf', hcoe]
    have hperm2 : (Q'.map Prod.snd).Perm (Q.map Prod.snd) := by
      rw [hsnd', hQsnd]
      exact hperm.map s
    have hhc := (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g (Q'.map Prod.snd) (Q.map Prod.snd) n hd'.symm
      (char_snd L Q' hQ')).2 hperm2
    rw [hhc] at hip'
    by_contra hne
    rw [(GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ χ _ hχ hirr).2.2, if_neg hne] at hip'
    exact hip' rfl
  · rintro rfl
    refine ⟨hirr, Q, hQc, hdeg, hprod.symm, ?_⟩
    rw [hnorm1]
    exact one_ne_zero

theorem label_main : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (n : ℕ), (∀ χ : Gn g n → ℂ, IsIrr χ → ∃! f, HasLabel L χ f) ∧ (∀ (χ : Gn g n → ℂ) f, HasLabel L χ f → f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0) ∧ ∀ f : (ZMod g)[X], f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → Squarefree f → ∃ Q : List ((ZMod g)[X] × Pc g), (∀ p ∈ Q, IsCuspOf L p.1 p.2.2 ∧ p.2.2 1 = ∏ i ∈ Finset.Ico 1 p.2.1, ((g : ℂ) ^ i - 1)) ∧ ((Q.map Prod.fst : List _) : Multiset _) = UniqueFactorizationMonoid.normalizedFactors f ∧ degL (Q.map Prod.snd) = n ∧ {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f} = {hcL (Q.map Prod.snd) n} := by
  intro g _ L hg hG n
  refine ⟨fun χ hχ => ?_, fun χ f hf => ?_, fun f hm hn h0 hs => squarefree_series L hg hG n f hm hn h0 hs⟩
  · obtain ⟨f, hf⟩ := label_exists L hg hG χ hχ
    exact ⟨f, hf, fun f' hf' => label_unique L hg χ hχ f' f hf' hf⟩
  · obtain ⟨Q, hQ, hd, rfl, -⟩ := hf
    obtain ⟨h1, h2, h3⟩ := prod_props L Q hQ
    exact ⟨h1, h2.trans hd, h3⟩

end GlobalTheory.GLq.Label

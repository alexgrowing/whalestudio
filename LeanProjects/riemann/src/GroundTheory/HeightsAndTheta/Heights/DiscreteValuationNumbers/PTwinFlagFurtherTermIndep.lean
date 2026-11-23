import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisFurther
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreMore
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.FullFlag
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPlainPolyPairNum
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSymmRelabel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace flagFurtherTerm_independent

open plainPairNumber (term rename_divDiff_eq_sum)

theorem term_head {N r : ℕ} (l : Fin r) (α : Fin N →₀ ℕ) (β : Fin r →₀ ℕ) (ν : Fin (N + r) →₀ ℕ)
    (hc : ∀ j, ν (Fin.castAdd r j) = α j) (hn : ∀ j, ν (Fin.natAdd N j) = β j) :
    term (Fin.natAdd N l) ν =
      (∏ j : Fin N, X (Sum.inr (Fin.castAdd r j)) ^ α j) *
        rename (Sum.map (Fin.natAdd N) (Fin.natAdd N)) (term l β) := by
  have hlt : ∀ j : Fin N, Fin.castAdd r j < Fin.natAdd N l := by
    intro j
    rw [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]
    omega
  have hgt : ∀ j : Fin N, ¬ Fin.natAdd N l < Fin.castAdd r j := by
    intro j h
    rw [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at h
    omega
  have hnn : ∀ j k : Fin r, (Fin.natAdd N j < Fin.natAdd N k ↔ j < k) := by
    intro j k
    simp only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left]
  have h1 : (∏ j ∈ Finset.univ.filter (fun j => j < Fin.natAdd N l),
      (X (Sum.inr j) : MvPolynomial (Fin (N + r) ⊕ Fin (N + r)) ℤ) ^ ν j) =
      (∏ j : Fin N, X (Sum.inr (Fin.castAdd r j)) ^ α j) *
        ∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr (Fin.natAdd N j)) ^ β j := by
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_add]
    simp only [hlt, if_true, hnn, hc, hn]
  have h3 : (∏ j ∈ Finset.univ.filter (fun j => Fin.natAdd N l < j),
      (X (Sum.inl j) : MvPolynomial (Fin (N + r) ⊕ Fin (N + r)) ℤ) ^ ν j) =
      ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl (Fin.natAdd N j)) ^ β j := by
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_add]
    simp only [hgt, if_false, Finset.prod_const_one, one_mul, hnn, hn]
  unfold term
  rw [h1, h3, hn l]
  simp only [map_mul, map_prod, map_pow, map_sum, rename_X, Sum.map_inl, Sum.map_inr]
  ring

theorem rename_monomial_head {N r : ℕ} (α : Fin N →₀ ℕ) (c : ℤ) :
    rename (fun i : Fin N => (Sum.inr (Fin.castAdd r i) : Fin (N + r) ⊕ Fin (N + r))) (monomial α c) =
      C c * ∏ j : Fin N, X (Sum.inr (Fin.castAdd r j)) ^ α j := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [map_mul, map_prod, map_pow, rename_X, rename_C]

theorem rename_divDiff_natAdd_monomial {N r : ℕ} (l : Fin r) (α : Fin N →₀ ℕ) (c : ℤ)
    (Q : MvPolynomial (Fin r) ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.natAdd N l)
        (rename (Fin.castAdd r) (monomial α c) * rename (Fin.natAdd N) Q)) =
      rename (fun i : Fin N => (Sum.inr (Fin.castAdd r i) : Fin (N + r) ⊕ Fin (N + r))) (monomial α c) *
        rename (Sum.map (Fin.natAdd N) (Fin.natAdd N))
          (rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l Q)) := by
  classical
  set A : Fin (N + r) →₀ ℕ := α.mapDomain (Fin.castAdd r) with hA
  have hinj : Function.Injective
      (fun μ : Fin r →₀ ℕ => A + Finsupp.mapDomain (Fin.natAdd N) μ) :=
    fun a b h => Finsupp.mapDomain_injective (Fin.natAdd_injective _ _) (add_left_cancel h)
  have hsub : (monomial A c * rename (Fin.natAdd N) Q).support ⊆
      Q.support.image (fun μ => A + Finsupp.mapDomain (Fin.natAdd N) μ) := by
    intro ν hν
    rw [mem_support_iff, coeff_monomial_mul'] at hν
    split_ifs at hν with hle
    · have hmem : ν - A ∈ (rename (Fin.natAdd N) Q).support :=
        mem_support_iff.mpr (right_ne_zero_of_mul hν)
      rw [support_rename_of_injective (Fin.natAdd_injective _ _), Finset.mem_image] at hmem
      obtain ⟨μ, hμ, he⟩ := hmem
      exact Finset.mem_image.mpr ⟨μ, hμ, by rw [he, add_tsub_cancel_of_le hle]⟩
    · exact absurd rfl hν
  rw [rename_monomial, ← hA, rename_divDiff_eq_sum (Fin.natAdd N l) _ hsub,
    Finset.sum_image fun a _ b _ h => hinj h, rename_divDiff_eq_sum l Q subset_rfl, map_sum,
    Finset.mul_sum, rename_monomial_head]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hc : ∀ j, (A + Finsupp.mapDomain (Fin.natAdd N) μ) (Fin.castAdd r j) = α j := by
    intro j
    have hj : Fin.castAdd r j ∉ Set.range (Fin.natAdd N : Fin r → Fin (N + r)) := by
      rintro ⟨k, hk⟩
      have := congrArg Fin.val hk
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    rw [Finsupp.add_apply, hA, Finsupp.mapDomain_apply (Fin.castAdd_injective _ _),
      Finsupp.mapDomain_of_notMem_range _ _ hj, add_zero]
  have hn : ∀ j, (A + Finsupp.mapDomain (Fin.natAdd N) μ) (Fin.natAdd N j) = μ j := by
    intro j
    have hj : Fin.natAdd N j ∉ Set.range (Fin.castAdd r : Fin N → Fin (N + r)) := by
      rintro ⟨k, hk⟩
      have := congrArg Fin.val hk
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    rw [Finsupp.add_apply, hA, Finsupp.mapDomain_of_notMem_range _ _ hj,
      Finsupp.mapDomain_apply (Fin.natAdd_injective _ _), zero_add]
  rw [coeff_monomial_mul', if_pos le_self_add, add_tsub_cancel_left,
    coeff_rename_mapDomain _ (Fin.natAdd_injective _ _), term_head l α μ _ hc hn, C_mul]
  simp only [map_mul, rename_C]
  ring

theorem rename_divDiff_natAdd_mul {N r : ℕ} (l : Fin r) (G : MvPolynomial (Fin N) ℤ)
    (Q : MvPolynomial (Fin r) ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.natAdd N l)
        (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)) =
      rename (fun i : Fin N => (Sum.inr (Fin.castAdd r i) : Fin (N + r) ⊕ Fin (N + r))) G *
        rename (Sum.map (Fin.natAdd N) (Fin.natAdd N))
          (rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l Q)) := by
  induction G using MvPolynomial.induction_on' with
  | monomial α c => exact rename_divDiff_natAdd_monomial l α c Q
  | add A B hA hB =>
    rw [map_add, add_mul, plainPolynomialPairNumber.rename_divDiff_add, hA, hB, map_add, add_mul]

def emb (N r : ℕ) : Fin (N + (r + r)) → Fin ((N + r) + (N + r)) :=
  Fin.append (fun i : Fin N => Fin.natAdd (N + r) (Fin.castAdd r i))
    (Fin.append (fun j : Fin r => Fin.castAdd (N + r) (Fin.natAdd N j))
      (fun j : Fin r => Fin.natAdd (N + r) (Fin.natAdd N j)))

theorem val_emb {N r : ℕ} (s : Fin (N + (r + r))) :
    ((emb N r s : Fin ((N + r) + (N + r))) : ℕ) =
      if (s : ℕ) < N then s + N + r else if (s : ℕ) < N + r then s else s + N := by
  induction s using Fin.addCases with
  | left i =>
    simp only [emb, Fin.append_left, Fin.val_natAdd, Fin.val_castAdd, i.isLt, if_true]
    omega
  | right j =>
    induction j using Fin.addCases with
    | left j =>
      simp only [emb, Fin.append_right, Fin.append_left, Fin.val_natAdd, Fin.val_castAdd]
      rw [if_neg (by omega), if_pos (by omega)]
    | right j =>
      simp only [emb, Fin.append_right, Fin.val_natAdd]
      rw [if_neg (by omega), if_neg (by omega)]
      omega

theorem emb_injective (N r : ℕ) : Function.Injective (emb N r) := by
  intro a b h
  have h' := congrArg Fin.val h
  rw [val_emb, val_emb] at h'
  apply Fin.ext
  split_ifs at h' <;> omega

theorem divDiff_natAdd_mul {N r : ℕ} (l : Fin r) (G : MvPolynomial (Fin N) ℤ)
    (Q : MvPolynomial (Fin r) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.natAdd N l) (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) =
      rename (emb N r) (rename (Fin.castAdd (r + r)) G *
        rename (Fin.natAdd N) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l Q)) := by
  apply rename_injective _ finSumFinEquiv.symm.injective
  have h1 : (⇑finSumFinEquiv.symm ∘ emb N r) ∘ Fin.castAdd (r + r) =
      fun i : Fin N => (Sum.inr (Fin.castAdd r i) : Fin (N + r) ⊕ Fin (N + r)) := by
    funext i
    simp only [Function.comp_apply, emb, Fin.append_left, finSumFinEquiv_symm_apply_natAdd]
  have h2 : (⇑finSumFinEquiv.symm ∘ emb N r) ∘ Fin.natAdd N =
      Sum.map (Fin.natAdd N) (Fin.natAdd N) ∘ ⇑finSumFinEquiv.symm := by
    funext j
    induction j using Fin.addCases with
    | left j =>
      simp only [Function.comp_apply, emb, Fin.append_left, Fin.append_right,
        finSumFinEquiv_symm_apply_castAdd, Sum.map_inl]
    | right j =>
      simp only [Function.comp_apply, emb, Fin.append_right, finSumFinEquiv_symm_apply_natAdd, Sum.map_inr]
  simp only [rename_divDiff_natAdd_mul, map_mul, rename_rename]
  exact congrArg₂ (· * ·) (congrArg (fun φ => rename φ G) h1.symm)
    (congrArg (fun φ => rename φ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l Q)) h2.symm)

theorem coe_monoList {r : ℕ} {A : Type*} (deg : Fin r → A) (μ : Fin r →₀ ℕ) :
    ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg μ : List A) : Multiset A) =
      (Finsupp.toMultiset μ).map deg := by
  classical
  have h : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg μ =
      ((List.finRange r).flatMap fun s => List.replicate (μ s) s).map deg := by
    simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList, List.map_flatMap, List.map_replicate]
  have h2 : (((List.finRange r).flatMap fun s => List.replicate (μ s) s : List (Fin r)) : Multiset (Fin r)) =
      Finsupp.toMultiset μ := by
    ext a
    rw [Multiset.coe_count, Finsupp.count_toMultiset]
    simp only [List.count_flatMap]
    rw [← Fin.sum_univ_def]
    simp [List.count_replicate]
  rw [h, ← Multiset.map_coe, h2]

theorem monoList_mapDomain_perm {m r : ℕ} {A : Type*} (deg : Fin r → A) (e : Fin m → Fin r)
    (ν : Fin m →₀ ℕ) :
    (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg (Finsupp.mapDomain e ν)).Perm
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList (deg ∘ e) ν) := by
  classical
  rw [← Multiset.coe_eq_coe, coe_monoList, coe_monoList, ← Finsupp.toMultiset_map, Multiset.map_map]

theorem exists_equiv_of_perm {A : Type*} {l₁ l₂ : List A} (h : l₁.Perm l₂) :
    ∃ σ : Fin l₁.length ≃ Fin l₂.length, ∀ i, l₁.get i = l₂.get (σ i) := by
  induction h with
  | nil => exact ⟨Equiv.refl _, fun i => rfl⟩
  | cons a _ ih =>
    obtain ⟨σ, hσ⟩ := ih
    refine ⟨(finSuccEquiv _).trans ((Equiv.optionCongr σ).trans (finSuccEquiv _).symm), fun i => ?_⟩
    induction i using Fin.cases with
    | zero => simp
    | succ i => simpa using hσ i
  | swap a b l =>
    refine ⟨Equiv.swap 0 1, fun i => ?_⟩
    induction i using Fin.cases with
    | zero => simp
    | succ i =>
      induction i using Fin.cases with
      | zero => simp
      | succ i =>
        rw [Equiv.swap_apply_def, if_neg (Fin.succ_ne_zero _),
          if_neg (fun h => by have := congrArg Fin.val h; simp at this)]
        simp
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨σ, hσ⟩ := ih₁
    obtain ⟨τ, hτ⟩ := ih₂
    exact ⟨σ.trans τ, fun i => (hσ i).trans (hτ (σ i))⟩

theorem polyNum_rename_perm {F : Type*} [Field F] {K : Type} [Fintype K] {κ : K → Type} [∀ k, Fintype (κ k)]
    (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F κ) (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F κ)) (n : ℕ)
    {m r : ℕ} (deg : Fin r → K → ℤ) (e : Fin m → Fin r) (he : Function.Injective e)
    (hsym : ∀ (L : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)), I W n (L ∘ σ) = I W n L)
    (P : MvPolynomial (Fin m) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W n deg (rename e P) =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W n (deg ∘ e) P := by
  classical
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  rw [support_rename_of_injective he,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective he h]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [coeff_rename_mapDomain e he]
  congr 1
  have hp := monoList_mapDomain_perm deg e ν
  obtain ⟨σ, hσ⟩ := exists_equiv_of_perm hp
  have hlen := hp.length_eq
  by_cases h₂ : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList (deg ∘ e) ν).length = n
  · have h₁ : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg (Finsupp.mapDomain e ν)).length = n := hlen.trans h₂
    rw [dif_pos h₁, dif_pos h₂]
    have key := hsym (fun j => (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList (deg ∘ e) ν).get (Fin.cast h₂.symm j))
      ((finCongr h₁.symm).trans (σ.trans (finCongr h₂)))
    rw [← key]
    congr 1
    funext j
    simp only [Function.comp_apply, Equiv.trans_apply, finCongr_apply, Fin.cast_cast]
    rw [hσ]
    rfl
  · rw [dif_neg (fun h => h₂ (hlen.symm.trans h)), dif_neg h₂]

end flagFurtherTerm_independent

open flagFurtherTerm_independent in

theorem flagFurtherTerm_independent.proof (hFib : VerticalDivisorFibreVariety.Statement)
    (hInd : FullFlagVerticalSymmetric.Statement) : flagFurtherTerm_independent.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hM _ φ₁ φ₂ I hI G hG r y y' f g hv c Q _ _ _ l
  have key : ∀ φ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E',
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
                                (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d
                                  (Fin.append (Fin.append φ.deg y) (Fin.append φ.deg' y'))
                                  (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.natAdd N l)
                                    (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)))
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (f l) (g l)) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
          (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d
            (Fin.append (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair.fullFlag' O φ).deg (Fin.append y y'))
            (rename (Fin.castAdd (r + r)) G * rename (Fin.natAdd N) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l Q)))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (f l) (g l)) := by
    intro φ
    simp only [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval, Finsupp.sum]
    refine Finset.sum_congr rfl fun W hW => congrArg (_ * ·) ?_
    have hW' := hFib O K ι _ d hM _ (f l) (g l) (hv l) W hW
    rw [divDiff_natAdd_mul, polyNum_rename_perm I _ d _ (emb N r) (emb_injective N r)
      (fun L σ => Targets.SymmStatement.full (IsLocalRing.ResidueField O) ι I hI _ d L σ hW')]
    congr 1
    funext s
    induction s using Fin.addCases with
    | left i =>
      simp only [Function.comp_apply, emb, Fin.append_left, Fin.append_right]
      rfl
    | right j =>
      induction j using Fin.addCases with
      | left j => simp only [Function.comp_apply, emb, Fin.append_left, Fin.append_right]
      | right j => simp only [Function.comp_apply, emb, Fin.append_right]
  rw [key φ₁, key φ₂]
  exact hInd O Ω K ι x d N V E' hM _ _ I hI G hG (r + r) (Fin.append y y')
    (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l Q) _ (f l) (g l) (hv l)

end GroundTheory.Heights₂.Heights.NumbersDVR

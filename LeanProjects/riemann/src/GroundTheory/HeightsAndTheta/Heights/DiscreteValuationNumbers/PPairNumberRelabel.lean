import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairNumberRelabel
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.IntNumRelabel
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameMultiHomog
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameMultiProjPrime
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PExistsUniqueRelabel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace PairNumberRelabel

section Ring

variable {K₁ K₂ : Type} {ι₁ : K₁ → Type} {ι₂ : K₂ → Type} {R : Type} [CommRing R]
  (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k))

abbrev ren : MRing ι₁ R ≃+* MRing ι₂ R := (renameEquiv R σ).toRingEquiv

theorem ren_apply (f : MRing ι₁ R) : ren (R := R) σ f = rename σ f := rfl

theorem map_rename_eq (I : Ideal (MRing ι₁ R)) :
    I.map (rename σ) = I.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R) := rfl

theorem map_renameEquiv_eq (I : Ideal (MRing ι₁ R)) :
    I.map (renameEquiv R σ) = I.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R) := rfl

theorem rename_mem_map_iff (I : Ideal (MRing ι₁ R)) (x : MRing ι₁ R) :
    rename σ x ∈ I.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R) ↔ x ∈ I :=
  GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel.mem_map_iff (ren σ) I x

def idealEquiv : Ideal (MRing ι₁ R) ≃ Ideal (MRing ι₂ R) where
  toFun W := W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R)
  invFun W := W.map ((ren (R := R) σ).symm : MRing ι₂ R →+* MRing ι₁ R)
  left_inv W := Ideal.map_of_equiv (I := W) (ren (R := R) σ)
  right_inv W := by
    have := Ideal.map_of_equiv (I := W) (ren (R := R) σ).symm
    rwa [RingEquiv.symm_symm] at this

theorem idealEquiv_apply (W : Ideal (MRing ι₁ R)) :
    idealEquiv (R := R) σ W = W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R) := rfl

theorem isRelevant_iff' {K : Type} {ι : K → Type} (W : Ideal (MRing ι R)) :
    IsRelevant W ↔ ∀ k, ∃ p : Σ k, ι k, p.1 = k ∧ (X p : MRing ι R) ∉ W := by
  refine ⟨fun h k => ?_, fun h k => ?_⟩
  · obtain ⟨i, hi⟩ := h k
    exact ⟨⟨k, i⟩, rfl, hi⟩
  · obtain ⟨⟨a, b⟩, rfl, hp⟩ := h k
    exact ⟨b, hp⟩

variable (e : K₁ ≃ K₂)

theorem isRelevant_map_iff (hσ : ∀ v, (σ v).1 = e v.1) (W : Ideal (MRing ι₁ R)) :
    IsRelevant (W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R)) ↔ IsRelevant W := by
  have hX : ∀ q : Σ k, ι₂ k, (X q : MRing ι₂ R) = rename σ (X (σ.symm q)) := fun q => by
    rw [rename_X, Equiv.apply_symm_apply]
  rw [isRelevant_iff', isRelevant_iff']
  constructor
  · intro h k
    obtain ⟨q, hq, hX'⟩ := h (e k)
    refine ⟨σ.symm q, e.injective ?_, ?_⟩
    · rw [← hσ, Equiv.apply_symm_apply, hq]
    · rwa [hX, rename_mem_map_iff] at hX'
  · intro h k
    obtain ⟨p, hp, hX'⟩ := h (e.symm k)
    refine ⟨σ p, by rw [hσ, hp, Equiv.apply_symm_apply], ?_⟩
    rwa [← rename_X, rename_mem_map_iff]

theorem divCycle_map (hσ : ∀ v, (σ v).1 = e v.1) (P W : Ideal (MRing ι₁ R)) (f : MRing ι₁ R) :
    divCycle (P.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R)) (rename σ f)
        (W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R)) = divCycle P f W := by
  have hsup : P.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R) ⊔ Ideal.span {rename σ f} =
      (P ⊔ Ideal.span {f}).map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    rfl
  have hiff : (W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R) ∈
        (P.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R) ⊔ Ideal.span {rename σ f}).minimalPrimes ∧
        IsRelevant (W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R))) ↔
      (W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W) := by
    rw [hsup]
    exact and_congr (GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel.map_mem_minimalPrimes_iff _)
      (isRelevant_map_iff σ e hσ W)
  unfold divCycle
  by_cases h : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W
  · rw [dif_pos h, dif_pos (hiff.2 h)]
    have : W.IsPrime := h.1.1.1
    have : (W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R)).IsPrime := (hiff.2 h).1.1.1
    have hl := GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel.length_map (ren (R := R) σ) P W
      (le_sup_left.trans h.1.1.2) f
    unfold multAt
    exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) hl
  · rw [dif_neg h, dif_neg (mt hiff.1 h)]

theorem ratDiv_map (hσ : ∀ v, (σ v).1 = e v.1) (P W : Ideal (MRing ι₁ R)) (f g : MRing ι₁ R) :
    ratDiv (P.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R)) (rename σ f) (rename σ g)
        (W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R)) = ratDiv P f g W := by
  unfold ratDiv
  rw [divCycle_map σ e hσ, divCycle_map σ e hσ]

end Ring

section Numbers

variable {K : Type*} [DecidableEq K] {ι : K → Type*}

omit [DecidableEq K] in

theorem diffStep_comm (a b : K → ℤ) (h : (K → ℤ) → ℤ) :
    diffStep a (diffStep b h) = diffStep b (diffStep a h) := by
  funext m
  simp only [diffStep, sub_right_comm m a b]
  ring

omit [DecidableEq K] in

theorem foldr_diffStep_perm {l₁ l₂ : List (K → ℤ)} (p : l₁.Perm l₂) (h : (K → ℤ) → ℤ) :
    l₁.foldr diffStep h = l₂.foldr diffStep h := by
  induction p with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr_cons, ih]
  | swap x y l => simp only [List.foldr_cons]; exact diffStep_comm y x _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem intNum_get_eq {F : Type*} [Field F] (I : Ideal (MRing ι F)) (l : List (K → ℤ)) :
    intNum F I l.get = eventualValue (l.foldr diffStep (hilbFn I)) := by
  unfold intNum mixedDiff
  rw [List.ofFn_get]

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem vNumL_perm (W : Ideal (MRing ι O)) {l₁ l₂ : List (K → ℤ)} (p : l₁.Perm l₂) :
    vNumL W l₁ = vNumL W l₂ := by
  unfold vNumL vNum
  rw [intNum_get_eq, intNum_get_eq, foldr_diffStep_perm p]

end Numbers

section DVR

variable {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k))

omit [DecidableEq K₁] [DecidableEq K₂] in

theorem specialIdeal_map (W : Ideal (MRing ι₁ O)) :
    specialIdeal (W.map (ren (R := O) σ : MRing ι₁ O →+* MRing ι₂ O)) =
      (specialIdeal W).map (renameEquiv (IsLocalRing.ResidueField O) σ) := by
  rw [map_renameEquiv_eq]
  unfold specialIdeal
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, ren_apply, map_rename]

theorem vNumL_map (hσ : ∀ v, (σ v).1 = e v.1) (W : Ideal (MRing ι₁ O)) (l : List (K₂ → ℤ)) :
    vNumL (W.map (ren (R := O) σ : MRing ι₁ O →+* MRing ι₂ O)) l = vNumL W (l.map (· ∘ e)) := by
  unfold vNumL vNum
  rw [specialIdeal_map, GroundTheory.Heights₂.Heights.FieldNumbers.Relabel.intNum_map_rename e σ hσ,
    intNum_get_eq]
  unfold intNum mixedDiff
  have hl : List.ofFn (fun i => l.get i ∘ e) = l.map (· ∘ e) := by
    conv_rhs => rw [← List.ofFn_get l]
    rw [List.map_ofFn]
    rfl
  rw [hl]

theorem classNum_map (hσ : ∀ v, (σ v).1 = e v.1) {S : Type*} (cls : S → K₂ → ℤ)
    (H : MvPolynomial S ℤ) (Q : List (K₂ → ℤ)) (W : Ideal (MRing ι₁ O)) :
    classNum cls H Q (W.map (ren (R := O) σ : MRing ι₁ O →+* MRing ι₂ O)) =
      classNum (fun s => cls s ∘ e) H (Q.map (· ∘ e)) W := by
  unfold classNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [vNumL_map e σ hσ]
  congr 1
  apply vNumL_perm
  rw [List.map_append]
  refine List.Perm.append_right _ ?_
  rw [← Multiset.coe_eq_coe]
  unfold classList
  rw [← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList, Multiset.map_map]
  rfl

omit [IsDomain O] [IsDiscreteValuationRing O] in

theorem isMultiHomog_rename (hσ : ∀ v, (σ v).1 = e v.1) {f : MRing ι₁ O} {a : K₁ → ℕ}
    (h : IsMultiHomog f a) : IsMultiHomog (rename σ f) (a ∘ e.symm) := by
  have h' := GroundTheory.Heights₂.Heights.FieldNumbers.RenameMultiHomog.proof O K₁ K₂ e.toEmbedding ι₁ ι₂ σ
    (fun v => hσ v) f a h
  have hext : Function.extend e.toEmbedding a 0 = a ∘ e.symm := by
    funext k
    obtain ⟨k₁, rfl⟩ := e.surjective k
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact e.injective.extend_apply a 0 k₁
  rwa [hext] at h'

omit [IsDomain O] [IsDiscreteValuationRing O] in

theorem isModelOver_map [Fintype K₁] [Fintype K₂] (hσ : ∀ v, (σ v).1 = e v.1)
    (P : Ideal (MRing ι₁ O)) (d : ℕ) (h : IsModelOver P d) :
    IsModelOver (P.map (ren (R := O) σ : MRing ι₁ O →+* MRing ι₂ O)) d := by
  obtain ⟨hmp, hnt, hdim⟩ := h
  have hσ' : ∀ v, (σ.symm v).1 = e.symm v.1 := by
    intro v
    have := hσ (σ.symm v)
    rw [Equiv.apply_symm_apply] at this
    rw [this, Equiv.symm_apply_apply]
  refine ⟨?_, ?_, ?_⟩
  · have := GroundTheory.Heights₂.Heights.FieldNumbers.RenameMultiProjPrime.proof O K₂ K₁ ι₂ ι₁ e.symm σ.symm
      hσ' P hmp
    rw [Ideal.map_comap_of_equiv]
    exact this
  · rw [← hnt]
    ext c
    simp only [Ideal.mem_comap]
    rw [← rename_mem_map_iff σ P (C c), rename_C]
  · rw [GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel.ringKrullDim_quot_map, hdim,
      Fintype.card_congr e]

omit [IsDomain O] [IsDiscreteValuationRing O] in

theorem isVerticalDivisor_map (hσ : ∀ v, (σ v).1 = e v.1) (P : Ideal (MRing ι₁ O)) (ϖ : O)
    (b : K₂ → ℤ) (f g : MRing ι₁ O) (h : IsVerticalDivisor P ϖ (b ∘ e) f g) :
    IsVerticalDivisor (P.map (ren (R := O) σ : MRing ι₁ O →+* MRing ι₂ O)) ϖ b (rename σ f)
      (rename σ g) := by
  obtain ⟨⟨bf, bg, hf, hg, hb⟩, hfP, hgP, hv, hu⟩ := h
  refine ⟨⟨bf ∘ e.symm, bg ∘ e.symm, isMultiHomog_rename e σ hσ hf, isMultiHomog_rename e σ hσ hg,
    ?_⟩, fun h => hfP ((rename_mem_map_iff σ P f).1 h),
    fun h => hgP ((rename_mem_map_iff σ P g).1 h), ?_, ?_⟩
  · funext k
    have := congrFun hb (e.symm k)
    simpa using this
  · intro W' hW'
    obtain ⟨W, rfl⟩ := (idealEquiv (R := O) σ).surjective W'
    rw [idealEquiv_apply] at hW' ⊢
    rw [ratDiv_map σ e hσ] at hW'
    rw [← rename_C σ ϖ]
    exact Ideal.mem_map_of_mem _ (hv W hW')
  · intro W' hW'p hPW' hrel hϖ
    set W := W'.comap (ren (R := O) σ : MRing ι₁ O →+* MRing ι₂ O) with hWdef
    have hWW' : W.map (ren (R := O) σ : MRing ι₁ O →+* MRing ι₂ O) = W' :=
      Ideal.map_comap_of_surjective _ (ren (R := O) σ).surjective W'
    have hWp : W.IsPrime := Ideal.comap_isPrime _ _
    have hPW : P ≤ W := Ideal.map_le_iff_le_comap.1 hPW'
    have hWrel : IsRelevant W := by
      rw [← isRelevant_map_iff σ e hσ W, hWW']
      exact hrel
    have hϖW : (C ϖ : MRing ι₁ O) ∉ W := by
      intro hm
      apply hϖ
      rw [← hWW', ← rename_C σ ϖ]
      exact Ideal.mem_map_of_mem _ hm
    obtain ⟨u, v, hu', hv', huv⟩ := hu W hWp hPW hWrel hϖW
    refine ⟨rename σ u, rename σ v, fun hm => hu' ?_, fun hm => hv' ?_, ?_⟩
    · rw [← hWW'] at hm
      exact (rename_mem_map_iff σ W u).1 hm
    · rw [← hWW'] at hm
      exact (rename_mem_map_iff σ W v).1 hm
    · have := Ideal.mem_map_of_mem (ren (R := O) σ : MRing ι₁ O →+* MRing ι₂ O) huv
      simpa only [map_sub, map_mul, RingEquiv.coe_toRingHom, ren_apply] using this

theorem pairNum_map (hσ : ∀ v, (σ v).1 = e v.1) (P : Ideal (MRing ι₁ O)) {n : ℕ}
    (x x' : Fin n → K₂ → ℤ) (f g : Fin n → MRing ι₁ O)
    (Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ) (Q : List (K₂ → ℤ)) :
    pairNum (P.map (ren (R := O) σ : MRing ι₁ O →+* MRing ι₂ O)) x x' (fun i => rename σ (f i))
        (fun i => rename σ (g i)) Gs Q =
      pairNum P (fun i => x i ∘ e) (fun i => x' i ∘ e) f g Gs (Q.map (· ∘ e)) := by
  have hcls : (fun s => Sum.elim x x' s ∘ e) =
      Sum.elim (fun i => x i ∘ e) (fun i => x' i ∘ e) := by
    funext s
    cases s <;> rfl
  unfold pairNum
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold cycEval
  rw [← finsum_comp_equiv (idealEquiv (R := O) σ)]
  refine finsum_congr fun W => ?_
  rw [idealEquiv_apply, ratDiv_map σ e hσ]
  beta_reduce
  rw [classNum_map e σ hσ, hcls]

end DVR

end PairNumberRelabel

theorem PairNumberRelabel.proof : PairNumberRelabel.Statement := by
  intro O _ _ _ ϖ K₁ _ _ ι₁ _ K₂ _ _ ι₂ _ e σ hσ P
  rw [PairNumberRelabel.map_rename_eq σ P]
  exact ⟨fun d h => PairNumberRelabel.isModelOver_map e σ hσ P d h,
    fun b f g h => PairNumberRelabel.isVerticalDivisor_map e σ hσ P ϖ b f g h,
    fun n x x' f g Gs Q => PairNumberRelabel.pairNum_map e σ hσ P x x' f g Gs Q⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR

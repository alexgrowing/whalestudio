import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.GlOperatorsFormRepresentation
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LiePolarizationDerEqZeroOfDisjoint
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.FormalSeriesConditionsB1ToB4

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints Formalism.MainNotions.LemmaBAlt

section proj

variable {K : Type*} [Field K] {ι : Type*} {r : ℕ}

theorem coeff_multidegreeProj_of_multidegree_eq (d : ι → ℕ) (H : MvPolynomial (ι × Fin r) K) (m : ι × Fin r →₀ ℕ)
    (h : ∀ i, multideg m i = d i) : coeff m (polProj K d H) = coeff m H := by
  classical
  conv_lhs => rw [H.as_sum]
  rw [map_sum, MvPolynomial.coeff_sum]
  simp only [polProj_monomial]
  rw [Finset.sum_eq_single m]
  · rw [if_pos h]
    erw [MvPolynomial.coeff_monomial, if_pos rfl]
  · intro b _ hbm
    split_ifs
    · erw [MvPolynomial.coeff_monomial, if_neg hbm]
    · exact MvPolynomial.coeff_zero m
  · intro hm
    rw [MvPolynomial.mem_support_iff, not_not] at hm
    rw [if_pos h, hm]
    erw [MvPolynomial.coeff_monomial, if_pos rfl]

theorem eq_zero_of_multidegreeProj_eq_zero (H : MvPolynomial (ι × Fin r) K) (h : ∀ d, polProj K d H = 0) : H = 0 := by
  ext m
  rw [← coeff_multidegreeProj_of_multidegree_eq (fun i => multideg m i) H m (fun i => rfl), h, coeff_zero]

theorem multidegreeProj_eq_zero_of_ne (d d' : ι → ℕ) (hne : d' ≠ d) (H : MvPolynomial (ι × Fin r) K) (hH : H ∈ Pol K r d') :
    polProj K d H = 0 := by
  ext m
  rw [coeff_zero]
  by_cases hm : ∀ i, multideg m i = d i
  · rw [coeff_multidegreeProj_of_multidegree_eq d H m hm]
    by_contra hc
    have hmem : m ∈ H.support := MvPolynomial.mem_support_iff.2 hc
    have := ((MvPolynomial.mem_restrictSupport_iff _).1 hH) hmem
    apply hne
    funext i
    rw [← hm i]
    exact (this i).symm
  · by_contra hc
    have hmem : m ∈ (polProj K d H).support := MvPolynomial.mem_support_iff.2 hc
    exact hm (((MvPolynomial.mem_restrictSupport_iff _).1 (polProj_mem d H)) hmem)

end proj

section main

variable (D : Formalism.BasicNotions.D7) (F : Type) [Field F] [CharZero F] {N m : ℕ} (LL : Letters (Fin N)) (i : Fin (N + 1))
  (pi : Set (Fin m → ℤ))

abbrev isotypicSumInitialLetters : Submodule F (MvPolynomial (Fin N × Fin m) F) :=
  ⨆ a ∈ pi, isoSub (glOps F m LL {l | l.val < i.val}) a

def standardWordsWeightOutside : Submodule F (MvPolynomial (Fin N × Fin m) F) :=
  Submodule.span F {H | ∃ (b : Fin N → ℕ) (P : PPath m N LL b) (I : ℤ → Finset (Fin m)),
    IsSt P.mu I ∧ P.mu i ∉ pi ∧ H = Psi F P.mu I}

include D in
theorem standardWord_mem_isotypicSumInitialLetters (hpi : DomLowerSet pi) {b : Fin N → ℕ} (P : PPath m N LL b) (I : ℤ → Finset (Fin m))
    (hI : IsSt P.mu I) (hp : P.mu i ∈ pi) : Psi F P.mu I ∈ isotypicSumInitialLetters F LL i pi := by
  have h := lower_set_types_span D F N m LL b i pi hpi
  have h1 : Psi F P.mu I ∈ Submodule.span F {H | ∃ P : PPath m N LL b, ∃ I : ℤ → Finset (Fin m),
      IsSt P.mu I ∧ P.mu i ∈ pi ∧ H = Psi F P.mu I} := Submodule.subset_span ⟨P, I, hI, hp, rfl⟩
  rw [← h] at h1
  exact h1.2

theorem isotypicSumInitialLetters_multidegreeProj (b : Fin N → ℕ) (x : MvPolynomial (Fin N × Fin m) F) (hx : x ∈ isotypicSumInitialLetters F LL i pi) :
    polProj F b x ∈ isotypicSumInitialLetters F LL i pi := by
  have hle : isotypicSumInitialLetters F LL i pi ≤ Submodule.comap (polProj F b) (isotypicSumInitialLetters F LL i pi) := by
    refine iSup₂_le fun a ha x hx => ?_
    exact (le_iSup₂ (f := fun a (_ : a ∈ pi) => isoSub (glOps F m LL {l | l.val < i.val}) a) a ha)
      (isoSub_map_of_comm _ (polProj F b) (fun c d x => polProj_glAct b LL _ c d x) a x hx)
  exact hle hx

theorem standardWordsWeightOutside_multidegreeProj (b : Fin N → ℕ) (x : MvPolynomial (Fin N × Fin m) F) (hx : x ∈ standardWordsWeightOutside F LL i pi) :
    polProj F b x ∈ Submodule.span F {H | ∃ P : PPath m N LL b, ∃ I : ℤ → Finset (Fin m),
      IsSt P.mu I ∧ P.mu i ∉ pi ∧ H = Psi F P.mu I} := by
  unfold standardWordsWeightOutside at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b', P, I, hI, hp, rfl⟩ := hy
    by_cases hb : b' = b
    · subst hb
      rw [polProj_of_mem _ _ (standardWord_mem_multihomogeneous F P I hI)]
      exact Submodule.subset_span ⟨P, I, hI, hp, rfl⟩
    · rw [multidegreeProj_eq_zero_of_ne b b' hb _ (standardWord_mem_multihomogeneous F P I hI)]
      exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem span_standardWords_eq_span_image (b : Fin N → ℕ) (cond : PPath m N LL b → Prop) :
    Submodule.span F {G | ∃ P : PPath m N LL b, ∃ I : ℤ → Finset (Fin m), IsSt P.mu I ∧ cond P ∧ G = Psi F P.mu I} =
      Submodule.span F ((fun x : WI m N LL b => Psi F x.1.1.mu x.1.2) '' {x | cond x.1.1}) := by
  congr 1
  ext G
  constructor
  · rintro ⟨P, I, hI, hp, rfl⟩
    exact ⟨⟨(P, I), hI⟩, hp, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1.1, x.1.2, x.2, hx, rfl⟩

include D in
theorem isotypicSum_inf_standardWordsOutside_eq_bot (hpi : DomLowerSet pi) (x : MvPolynomial (Fin N × Fin m) F) (hU : x ∈ standardWordsWeightOutside F LL i pi)
    (hT : x ∈ isotypicSumInitialLetters F LL i pi) : x = 0 := by
  apply eq_zero_of_multidegreeProj_eq_zero
  intro b
  have h1 := standardWordsWeightOutside_multidegreeProj F LL i pi b x hU
  have h2 : polProj F b x ∈ Pol F m b ⊓ (⨆ a ∈ pi, isoSub (glOps F m LL {l | l.val < i.val}) a) :=
    ⟨polProj_mem b x, isotypicSumInitialLetters_multidegreeProj F LL i pi b x hT⟩
  rw [lower_set_types_span D F N m LL b i pi hpi, span_standardWords_eq_span_image F LL b (fun P => P.mu i ∈ pi)] at h2
  rw [span_standardWords_eq_span_image F LL b (fun P => P.mu i ∉ pi)] at h1
  have hd := (standardPath_basis_any_ring F N m LL b).1.disjoint_span_image
    (s := {x : WI m N LL b | x.1.1.mu i ∉ pi}) (t := {x : WI m N LL b | x.1.1.mu i ∈ pi})
    (Set.disjoint_left.2 fun x h1 h2 => h1 h2)
  exact (Submodule.disjoint_def.1 hd) _ h1 h2

include D in

theorem linearIndependent_standardWords_by_weight (hE4 : TypeSumsByEvaluation) {k : ℕ} (e : Fin m → Fin k) (dcd : Fin k → Option (Fin m))
    (hd1 : ∀ a, dcd (e a) = some a) (hd2 : ∀ c a, dcd c = some a → c = e a) (hpi : DomLowerSet pi)
    {X : Type} (v : X → MvPolynomial (Fin N × Fin k) F) (lab : X → Fin (N + 1) → Fin m → ℤ)
    (J : X → ℤ → Finset (Fin m)) (hpath : ∀ x, ∃ b, ∃ P : PPath m N LL b, P.mu = lab x)
    (hst : ∀ x, IsSt (lab x) (J x))
    (hev : ∀ x y, ∃ t : F, Tev dcd y (v x) = t • Psi F (lab x) (J x)) :
    Submodule.span F (Set.range v) ⊓ (⨆ a ∈ pi, isoSub (glOpsE F LL {j | j.val < i.val} e) a) =
      Submodule.span F (v '' {x | lab x i ∈ pi}) := by
  have hin : Submodule.span F (v '' {x | lab x i ∈ pi}) ≤
      ⨆ a ∈ pi, isoSub (glOpsE F LL {j | j.val < i.val} e) a := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, hE4 F N m k LL _ e dcd hd1 hd2 pi]
    intro y
    obtain ⟨t, ht⟩ := hev x y
    obtain ⟨b, P, hP⟩ := hpath x
    rw [ht]
    refine Submodule.smul_mem _ _ ?_
    have := standardWord_mem_isotypicSumInitialLetters D F LL i pi hpi P (J x) (by rw [hP]; exact hst x) (by rw [hP]; exact hx)
    rw [hP] at this
    exact this
  apply le_antisymm
  · rintro G ⟨hG, hGT⟩
    have hsplit : Set.range v = v '' {x | lab x i ∈ pi} ∪ v '' {x | lab x i ∉ pi} := by
      rw [← Set.image_union, ← Set.image_univ]
      congr 1
      ext x
      simp [em]
    rw [SetLike.mem_coe, hsplit, Submodule.span_union] at hG
    obtain ⟨G1, h1, G2, h2, rfl⟩ := Submodule.mem_sup.1 hG
    have hG2T : G2 ∈ ⨆ a ∈ pi, isoSub (glOpsE F LL {j | j.val < i.val} e) a := by
      have := Submodule.sub_mem _ hGT (hin h1)
      simpa using this
    have hz : G2 = 0 := by
      by_contra hne
      have : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
      obtain ⟨y, hy⟩ := exists_Tev_ne e dcd hd2 G2 hne
      apply hy
      apply isotypicSum_inf_standardWordsOutside_eq_bot D F LL i pi hpi
      · have hle : Submodule.span F (v '' {x | lab x i ∉ pi}) ≤
            Submodule.comap (Tev dcd y).toLinearMap (standardWordsWeightOutside F LL i pi) := by
          rw [Submodule.span_le]
          rintro _ ⟨x, hx, rfl⟩
          obtain ⟨t, ht⟩ := hev x y
          obtain ⟨b, P, hP⟩ := hpath x
          show Tev dcd y (v x) ∈ standardWordsWeightOutside F LL i pi
          rw [ht]
          exact Submodule.smul_mem _ _ (Submodule.subset_span
            ⟨b, P, J x, by rw [hP]; exact hst x, by rw [hP]; exact hx, by rw [hP]⟩)
        exact hle h2
      · exact (hE4 F N m k LL _ e dcd hd1 hd2 pi G2).1 hG2T y
    rw [hz, add_zero]
    exact h1
  · exact le_inf (Submodule.span_mono (Set.image_subset_range _ _)) hin

end main

section ev

variable {F : Type} [Field F] {N m m' k : ℕ}

theorem evalSpec_rename_embedding_eq_self (e : Fin m → Fin k) (dcd : Fin k → Option (Fin m)) (hd1 : ∀ a, dcd (e a) = some a)
    (y : Fin N × Fin k → F) (f : MvPolynomial (Fin N × Fin m) F) :
    Tev dcd y (rename (fun v : Fin N × Fin m => (v.1, e v.2)) f) = f := by
  unfold Tev
  rw [aeval_rename]
  have : ((fun v : Fin N × Fin k => (dcd v.2).elim (C (y v)) (fun a => X (v.1, a))) ∘
      (fun v : Fin N × Fin m => (v.1, e v.2))) = X := by
    funext v; simp [hd1]
  rw [this, aeval_X_left_apply]

theorem evalSpec_rename_complement_eq_const (e' : Fin m' → Fin k) (dcd : Fin k → Option (Fin m)) (hn : ∀ a, dcd (e' a) = none)
    (y : Fin N × Fin k → F) (g : MvPolynomial (Fin N × Fin m') F) :
    Tev dcd y (rename (fun v : Fin N × Fin m' => (v.1, e' v.2)) g) =
      C (eval (fun v : Fin N × Fin m' => y (v.1, e' v.2)) g) := by
  unfold Tev
  rw [aeval_rename]
  have : ((fun v : Fin N × Fin k => (dcd v.2).elim (C (y v)) (fun a => X (v.1, a))) ∘
      (fun v : Fin N × Fin m' => (v.1, e' v.2))) = fun v => C (y (v.1, e' v.2)) := by
    funext v; simp [hn]
  rw [this]
  induction g using MvPolynomial.induction_on
  · simp [MvPolynomial.algebraMap_eq]
  · simp_all
  · simp_all

theorem planeDecode_natAdd_eq_none (r K : ℕ) (a : Fin K) : dcdPl r K (Fin.natAdd r a) = none := by
  unfold dcdPl
  simp

theorem tangentDecode_castAdd_eq_none (r K : ℕ) (a : Fin r) : dcdTan r K (Fin.castAdd K a) = none := by
  unfold dcdTan
  simp

end ev

theorem restLowPl_of (D : Formalism.BasicNotions.D7) (hE4 : TypeSumsByEvaluation) (hP : ExternalProductBasis) : RestLowPl := by
  intro F _ _ N r K LL B i pi hpi
  rw [← (hP F N r K LL B).2]
  refine linearIndependent_standardWords_by_weight D F LL i pi hE4 (Fin.castAdd K) (dcdPl r K) (dcdPl_1 r K) (dcdPl_2 r K) hpi (pvec F r K LL B)
    (fun x => x.1.1.1) (fun x => x.1.1.2) (fun x => ?_) (fun x => x.2.2.1) (fun x y => ?_)
  · obtain ⟨b', _, _, h1, _⟩ := x.2.1
    exact ⟨b', h1⟩
  · refine ⟨eval (fun v : Fin N × Fin K => y (v.1, Fin.natAdd r v.2)) (Psi F x.1.2.1 x.1.2.2), ?_⟩
    show Tev (dcdPl r K) y (rename (fun v : Fin N × Fin r => (v.1, Fin.castAdd K v.2)) (Psi F x.1.1.1 x.1.1.2) *
      rename (fun v : Fin N × Fin K => (v.1, Fin.natAdd r v.2)) (Psi F x.1.2.1 x.1.2.2)) = _
    rw [map_mul, evalSpec_rename_embedding_eq_self _ _ (dcdPl_1 r K), evalSpec_rename_complement_eq_const _ _ (planeDecode_natAdd_eq_none r K), mul_comm,
      ← MvPolynomial.smul_eq_C_mul]

theorem restLowTan_of (D : Formalism.BasicNotions.D7) (hE4 : TypeSumsByEvaluation) (hP : ExternalProductBasis) : RestLowTan := by
  intro F _ _ N r K LL B i pi hpi
  rw [← (hP F N r K LL B).2]
  refine linearIndependent_standardWords_by_weight D F LL i pi hE4 (Fin.natAdd r) (dcdTan r K) (dcdTan_1 r K) (dcdTan_2 r K) hpi (pvec F r K LL B)
    (fun x => x.1.2.1) (fun x => x.1.2.2) (fun x => ?_) (fun x => x.2.2.2) (fun x y => ?_)
  · obtain ⟨_, b'', _, _, h2⟩ := x.2.1
    exact ⟨b'', h2⟩
  · refine ⟨eval (fun v : Fin N × Fin r => y (v.1, Fin.castAdd K v.2)) (Psi F x.1.1.1 x.1.1.2), ?_⟩
    show Tev (dcdTan r K) y (rename (fun v : Fin N × Fin r => (v.1, Fin.castAdd K v.2)) (Psi F x.1.1.1 x.1.1.2) *
      rename (fun v : Fin N × Fin K => (v.1, Fin.natAdd r v.2)) (Psi F x.1.2.1 x.1.2.2)) = _
    rw [map_mul, evalSpec_rename_embedding_eq_self _ _ (dcdTan_1 r K), evalSpec_rename_complement_eq_const _ _ (tangentDecode_castAdd_eq_none r K),
      ← MvPolynomial.smul_eq_C_mul]

end Formalism.MainNotions.G.ColumnFamilies

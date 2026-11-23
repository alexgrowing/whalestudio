import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.GlOperatorsFormRepresentation
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LiePolarizationDerEqZeroOfDisjoint
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.SubProjectorProductMemStrict

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints Formalism.MainNotions.LemmaBAlt

section der

variable {F : Type} [Field F] {N m m' k : ℕ} (LL : Letters (Fin N)) (S T : Set (Fin N)) (e : Fin m → Fin k)
  (e' : Fin m' → Fin k)

def glOperatorDerivation (F : Type) [Field F] {N m k : ℕ} (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k)
    (a b : Fin m) : Derivation F (MvPolynomial (Fin N × Fin k) F) (MvPolynomial (Fin N × Fin k) F) :=
  Derivation.mk' (glOpsE F LL S e a b) (fun f g => by rw [glOpsE_mul]; rfl)

theorem glOperatorDerivation_apply (a b : Fin m) (f : MvPolynomial (Fin N × Fin k) F) :
    glOperatorDerivation F LL S e a b f = glOpsE F LL S e a b f := rfl

theorem glOperatorDerivation_lie_relation (he : Function.Injective e) (a b c d : Fin m) :
    ⁅glOperatorDerivation F LL S e a b, glOperatorDerivation F LL S e c d⁆ =
      (if b = c then glOperatorDerivation F LL S e a d else 0) - (if d = a then glOperatorDerivation F LL S e c b else 0) := by
  classical
  apply MvPolynomial.derivation_ext
  rintro ⟨l, x⟩
  rw [Derivation.commutator_apply, Derivation.sub_apply]
  have e1 : (if b = c then glOperatorDerivation F LL S e a d else 0) (X (l, x)) =
      if b = c then glOperatorDerivation F LL S e a d (X (l, x)) else 0 := by split_ifs <;> simp
  have e2 : (if d = a then glOperatorDerivation F LL S e c b else 0) (X (l, x)) =
      if d = a then glOperatorDerivation F LL S e c b (X (l, x)) else 0 := by split_ifs <;> simp
  rw [e1, e2]
  simp only [glOperatorDerivation_apply]
  by_cases hl : l ∈ S
  · by_cases hv : LL.vec l = true
    · simp only [glOpsE_X, hl, hv, if_true, eq_comm (a := b) (b := c), eq_comm (a := d) (b := a)]
      by_cases h1 : x = e d <;> by_cases h2 : x = e b <;> by_cases h3 : c = b <;> by_cases h4 : a = d <;>
        simp_all [glOpsE_X, he.eq_iff]
    · simp only [glOpsE_X, hl, hv, if_true, if_false, Bool.false_eq_true]
      by_cases h1 : x = e c <;> by_cases h2 : x = e a <;> by_cases h3 : b = c <;> by_cases h4 : d = a <;>
        simp_all [glOpsE_X, he.eq_iff]
  · simp [glOpsE_X, hl]

theorem glOperatorsEmbedded_commutator_relation (he : Function.Injective e) (a b c d : Fin m) :
    glOpsE F LL S e a b * glOpsE F LL S e c d - glOpsE F LL S e c d * glOpsE F LL S e a b =
      (if b = c then glOpsE F LL S e a d else 0) - (if d = a then glOpsE F LL S e c b else 0) := by
  apply LinearMap.ext
  intro G
  have h := congrArg (fun D : Derivation F (MvPolynomial (Fin N × Fin k) F) (MvPolynomial (Fin N × Fin k) F) => D G)
    (glOperatorDerivation_lie_relation (F := F) LL S e he a b c d)
  simp only [Derivation.commutator_apply, Derivation.sub_apply, glOperatorDerivation_apply] at h
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, h, LinearMap.sub_apply]
  congr 1
  · split_ifs
    · rfl
    · simp
  · split_ifs
    · rfl
    · simp

theorem glOperatorDerivation_lie_eq_zero_of_disjoint (hd : (∀ l, l ∈ S → l ∉ T) ∨ (∀ a a', e a ≠ e' a')) (a b : Fin m) (c d : Fin m') :
    ⁅glOperatorDerivation F LL S e a b, glOperatorDerivation F LL T e' c d⁆ = 0 := by
  classical
  apply MvPolynomial.derivation_ext
  rintro ⟨l, x⟩
  rw [Derivation.commutator_apply]
  simp only [glOperatorDerivation_apply, Derivation.coe_zero, Pi.zero_apply]
  rcases hd with hd | hd
  · by_cases hS : l ∈ S
    · have hT := hd l hS
      simp only [glOpsE_X, hS, hT, if_true, if_false, map_zero]
      split_ifs <;> simp [glOpsE_X, hT]
    · simp only [glOpsE_X, hS, if_false, map_zero]
      split_ifs <;> simp [glOpsE_X, hS]
  · have hd' : ∀ a a', e' a' ≠ e a := fun a a' h => hd a a' h.symm
    simp only [glOpsE_X]
    split_ifs <;> simp_all [glOpsE_X]

theorem glOperatorsEmbedded_commute_of_disjoint (hd : (∀ l, l ∈ S → l ∉ T) ∨ (∀ a a', e a ≠ e' a')) (a b : Fin m) (c d : Fin m')
    (G : MvPolynomial (Fin N × Fin k) F) :
    glOpsE F LL S e a b (glOpsE F LL T e' c d G) = glOpsE F LL T e' c d (glOpsE F LL S e a b G) := by
  have h := congrArg (fun D : Derivation F (MvPolynomial (Fin N × Fin k) F) (MvPolynomial (Fin N × Fin k) F) => D G)
    (glOperatorDerivation_lie_eq_zero_of_disjoint (F := F) LL S T e e' hd a b c d)
  simp only [Derivation.commutator_apply, glOperatorDerivation_apply, Derivation.coe_zero, Pi.zero_apply] at h
  exact sub_eq_zero.1 h

open Classical in
theorem glOperatorsEmbedded_apply (a b : Fin m) (G : MvPolynomial (Fin N × Fin k) F) :
    glOpsE F LL S e a b G =
      ∑ l : Fin N, if l ∈ S then (if LL.vec l then X (l, e a) * pderiv (l, e b) G
        else -(X (l, e b) * pderiv (l, e a) G)) else 0 := by
  unfold glOpsE
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

theorem glOperatorsEmbedded_union_split (h : S ⊆ T) (a b : Fin m) (G : MvPolynomial (Fin N × Fin k) F) :
    glOpsE F LL T e a b G = glOpsE F LL S e a b G + glOpsE F LL (T \ S) e a b G := by
  classical
  rw [glOperatorsEmbedded_apply, glOperatorsEmbedded_apply, glOperatorsEmbedded_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h1 : l ∈ S
  · have h2 : l ∈ T := h h1
    simp [h1, h2]
  · by_cases h2 : l ∈ T
    · simp [h1, h2]
    · simp [h1, h2]

theorem multidegreeProj_glOperatorsEmbedded_comm (d : Fin N → ℕ) (a b : Fin m) (G : MvPolynomial (Fin N × Fin k) F) :
    polProj F d (glOpsE F LL S e a b G) = glOpsE F LL S e a b (polProj F d G) := by
  classical
  induction G using MvPolynomial.induction_on' with
  | monomial mm c =>
    rw [polProj_monomial, glOperatorsEmbedded_apply, map_sum]
    by_cases h : ∀ i, multideg mm i = d i
    · rw [if_pos h, glOperatorsEmbedded_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs
      · rw [polProj_step, if_pos h]
      · rw [map_neg, polProj_step, if_pos h]
      · rw [map_zero]
    · rw [if_neg h, map_zero]
      refine Finset.sum_eq_zero fun l _ => ?_
      split_ifs
      · rw [polProj_step, if_neg h]
      · rw [map_neg, polProj_step, if_neg h, neg_zero]
      · rw [map_zero]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]

theorem glOperatorsEmbedded_mem_multidegree (d : Fin N → ℕ) (a b : Fin m) (G : MvPolynomial (Fin N × Fin k) F) (hG : G ∈ Pol F k d) :
    glOpsE F LL S e a b G ∈ Pol F k d := by
  have h := multidegreeProj_glOperatorsEmbedded_comm LL S e d a b G
  rw [polProj_of_mem d G hG] at h
  rw [← h]
  exact polProj_mem d _

theorem monomial_mem_weightSpace_glOperators (mm : Fin N × Fin k →₀ ℕ) (c : F) :
    (monomial mm c : MvPolynomial (Fin N × Fin k) F) ∈ weightSp (glOpsE F LL S e) (wtA LL S e mm) := by
  classical
  unfold weightSp
  rw [Submodule.mem_iInf]
  intro a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
  ext m2
  rw [coeff_Eaa, coeff_smul, smul_eq_mul, coeff_monomial]
  split_ifs with h
  · rw [h]
  · simp

theorem glOperatorsEmbedded_iSup_weightSpace_eq_top : (⨆ mu : Fin m → ℤ, weightSp (glOpsE F LL S e) mu) = ⊤ := by
  rw [eq_top_iff]
  intro G _
  induction G using MvPolynomial.induction_on' with
  | monomial mm c => exact Submodule.mem_iSup_of_mem _ (monomial_mem_weightSpace_glOperators LL S e mm c)
  | add p q hp hq => exact Submodule.add_mem _ (hp trivial) (hq trivial)

theorem glOperatorsEmbedded_locallyFinite (x : MvPolynomial (Fin N × Fin k) F) :
    ∃ W : Submodule F (MvPolynomial (Fin N × Fin k) F), FiniteDimensional F W ∧ x ∈ W ∧
      ∀ a b, ∀ y ∈ W, glOpsE F LL S e a b y ∈ W := by
  refine ⟨x.support.sup fun mm => Pol F k (multideg mm), Submodule.finiteDimensional_finset_sup _ _, ?_, ?_⟩
  · have h : ∑ mm ∈ x.support, monomial mm (x.coeff mm) ∈ x.support.sup fun mm => Pol F k (multideg mm) := by
      refine Submodule.sum_mem _ fun mm hm => ?_
      have hle : Pol F k (multideg mm) ≤ x.support.sup fun mm => Pol F k (multideg mm) :=
        Finset.le_sup (f := fun mm => Pol F k (multideg mm)) hm
      exact hle (monomial_mem_Pol _ mm _ fun _ => rfl)
    rwa [support_sum_monomial_coeff] at h
  · intro a b
    have hle : (x.support.sup fun mm => Pol F k (multideg mm)) ≤
        (x.support.sup fun mm => Pol F k (multideg mm)).comap (glOpsE F LL S e a b) := by
      refine Finset.sup_le fun mm hm y hy => ?_
      have hle : Pol F k (multideg mm) ≤ x.support.sup fun mm => Pol F k (multideg mm) :=
        Finset.le_sup (f := fun mm => Pol F k (multideg mm)) hm
      exact hle (glOperatorsEmbedded_mem_multidegree LL S e _ a b y hy)
    exact fun y hy => hle hy

theorem glOperatorsEmbedded_isGLRep (he : Function.Injective e) : IsGLRep (glOpsE F LL S e) :=
  ⟨glOperatorsEmbedded_commutator_relation LL S e he, glOperatorsEmbedded_locallyFinite LL S e, glOperatorsEmbedded_iSup_weightSpace_eq_top LL S e⟩

end der

theorem determinant_divisibility : GlOperatorsFormRepresentation := fun _ _ _ _ _ _ LL S e he => glOperatorsEmbedded_isGLRep LL S e he

theorem projectors_preserve_multidegree : ProjectorsPreserveMultidegree := by
  intro F _ _ N m k LL S e _ pr sys B a x hx
  have h := sys.comm_of_preserve (polProj F B)
    (fun nu => isoSub_map_of_comm (glOpsE F LL S e) (polProj F B) (fun a b x => multidegreeProj_glOperatorsEmbedded_comm LL S e B a b x) nu) a x
  rw [polProj_of_mem B x hx] at h
  rw [← h]
  exact polProj_mem B _

open Classical in

def partialInverseOfEmbedding {m k : ℕ} (e : Fin m → Fin k) : Fin k → Option (Fin m) :=
  fun c => if h : ∃ a, e a = c then some (Classical.choose h) else none

theorem partialInverseOfEmbedding_apply_self {m k : ℕ} (e : Fin m → Fin k) (he : Function.Injective e) (a : Fin m) :
    partialInverseOfEmbedding e (e a) = some a := by
  classical
  unfold partialInverseOfEmbedding
  have h : ∃ a', e a' = e a := ⟨a, rfl⟩
  rw [dif_pos h]
  exact congrArg some (he (Classical.choose_spec h))

theorem eq_of_partialInverseOfEmbedding_eq_some {m k : ℕ} (e : Fin m → Fin k) (c : Fin k) (a : Fin m) (h : partialInverseOfEmbedding e c = some a) : c = e a := by
  classical
  unfold partialInverseOfEmbedding at h
  by_cases h1 : ∃ a, e a = c
  · rw [dif_pos h1] at h
    rw [← Option.some.inj h]
    exact (Classical.choose_spec h1).symm
  · rw [dif_neg h1] at h
    exact absurd h (by simp)

section types

variable {F : Type} [Field F] [CharZero F] {N m k : ℕ} (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k)

theorem evalSpec_glOperators_intertwine (dcd : Fin k → Option (Fin m)) (hd1 : ∀ a, dcd (e a) = some a)
    (hd2 : ∀ c a, dcd c = some a → c = e a) (y : Fin N × Fin k → F) (a b : Fin m)
    (x : MvPolynomial (Fin N × Fin k) F) :
    (Tev dcd y).toLinearMap (glOpsE F LL S e a b x) = glOps F m LL S a b ((Tev dcd y).toLinearMap x) :=
  Tev_inter LL e dcd hd1 hd2 S y a b x

theorem dominant_of_isHighestWeightVector_polynomial (D : Formalism.BasicNotions.D7) (he : Function.Injective e) (a : Fin m → ℤ)
    (v : MvPolynomial (Fin N × Fin k) F) (hv : IsHWV (glOpsE F LL S e) a v) : Dominant a := by
  obtain ⟨y, hy⟩ := exists_Tev_ne e (partialInverseOfEmbedding e) (eq_of_partialInverseOfEmbedding_eq_some e) v hv.1
  have hT := evalSpec_glOperators_intertwine LL S e (partialInverseOfEmbedding e) (partialInverseOfEmbedding_apply_self e he) (eq_of_partialInverseOfEmbedding_eq_some e) y
  refine dominant_of_isHighestWeightVector LL S D a ((Tev (partialInverseOfEmbedding e) y).toLinearMap v) ⟨hy, ?_, ?_⟩
  · have h2 := hv.2.1
    simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply] at h2 ⊢
    intro c
    rw [← hT, ← map_smul, ← map_sub, h2 c, map_zero]
  · intro c d hcd
    rw [← hT, hv.2.2 c d hcd, map_zero]

end types

theorem polynomialHighestWeight_dominant (D : Formalism.BasicNotions.D7) : IsotypicZeroOfNonDominant := by
  intro F _ _ N m k LL S e he a ha
  rw [isoSub, Submodule.span_eq_bot]
  rintro x ⟨u, _, v, hv, rfl⟩
  exact absurd (dominant_of_isHighestWeightVector_polynomial LL S e D he a v hv) ha

theorem polynomialTypeSums_by_evaluation (D : Formalism.BasicNotions.D7) : TypeSumsByEvaluation := by
  intro F _ _ N m k LL S e dcd hd1 hd2 pi x
  have he : Function.Injective e := fun a b h => by
    have := hd1 a
    rw [h, hd1] at this
    exact (Option.some.inj this).symm
  obtain ⟨prE, sysE⟩ := isoDecomp (glOpsE F LL S e) D (weight_condition_from_integral_form D) (glOperatorsEmbedded_isGLRep LL S e he)
  obtain ⟨prm, sysm⟩ := isoDecomp (glOps F m LL S) D (weight_condition_from_integral_form D) (isGLRep_glOps F (Fin N) LL m S)
  have hiso : ∀ y c z, z ∈ isoSub (glOpsE F LL S e) c →
      (Tev dcd y).toLinearMap z ∈ isoSub (glOps F m LL S) c :=
    fun y c z hz => inter_iso (glOpsE F LL S e) (glOps F m LL S) (Tev dcd y).toLinearMap
      (evalSpec_glOperators_intertwine LL S e dcd hd1 hd2 y) c z hz
  constructor
  · intro hx y
    have hle : (⨆ a ∈ pi, isoSub (glOpsE F LL S e) a) ≤
        (⨆ a ∈ pi, isoSub (glOps F m LL S) a).comap (Tev dcd y).toLinearMap :=
      iSup₂_le fun a ha z hz =>
        (le_iSup₂ (f := fun a (_ : a ∈ pi) => isoSub (glOps F m LL S) a) a ha) (hiso y a z hz)
    exact hle hx
  · intro h
    refine (mem_iSup_components_iff sysE pi x).2 fun a ha => ?_
    by_contra hne
    obtain ⟨y, hy⟩ := exists_Tev_ne e dcd hd2 _ hne
    apply hy
    have key : (Tev dcd y).toLinearMap (prE a x) = prm a ((Tev dcd y).toLinearMap x) := by
      obtain ⟨T, hTx⟩ := sysE.cover x
      have h2 : prm a ((Tev dcd y).toLinearMap x) =
          ∑ c ∈ T, prm a ((Tev dcd y).toLinearMap (prE c x)) := by
        conv_lhs => rw [hTx]
        rw [map_sum, map_sum]
      rw [h2]
      by_cases haT : a ∈ T
      · rw [Finset.sum_eq_single_of_mem a haT fun c _ hc => sysm.zero_on a c hc _ (hiso y c _ (sysE.mem c x))]
        exact (sysm.id_on a _ (hiso y a _ (sysE.mem a x))).symm
      · rw [sysE.zero_of_not_mem hTx haT, map_zero]
        exact (Finset.sum_eq_zero fun c hc =>
          sysm.zero_on a c (fun hh : c = a => haT (hh ▸ hc)) _ (hiso y c _ (sysE.mem c x))).symm
    have key' : Tev dcd y (prE a x) = prm a (Tev dcd y x) := key
    rw [key']
    exact (mem_iSup_components_iff sysm pi _).1 (h y) a ha

theorem glOperatorsEmbedded_commute_decomposition {F : Type} [Field F] {N m m' k : ℕ} (LL : Letters (Fin N)) (S S' : Set (Fin N))
    (e : Fin m → Fin k) (e' : Fin m' → Fin k)
    (pr : (Fin m → ℤ) → Module.End F (MvPolynomial (Fin N × Fin k) F))
    (pr' : (Fin m' → ℤ) → Module.End F (MvPolynomial (Fin N × Fin k) F))
    (sys : DecSys (isoSub (glOpsE F LL S e)) pr) (sys' : DecSys (isoSub (glOpsE F LL S' e')) pr')
    (hpres : ∀ c d mu, ∀ x ∈ isoSub (glOpsE F LL S e) mu, glOpsE F LL S' e' c d x ∈ isoSub (glOpsE F LL S e) mu)
    (a : Fin m → ℤ) (b : Fin m' → ℤ) : pr a * pr' b = pr' b * pr a := by
  have h1 : ∀ c d x, pr a (glOpsE F LL S' e' c d x) = glOpsE F LL S' e' c d (pr a x) :=
    fun c d x => (sys.comm_of_preserve (glOpsE F LL S' e' c d) (hpres c d) a x).symm
  have h3 := isoSub_map_of_comm (glOpsE F LL S' e') (pr a) h1
  exact LinearMap.ext fun x => sys'.comm_of_preserve (pr a) h3 b x

theorem glOperatorsEmbedded_preserves_isotypic_of_subset {F : Type} [Field F] {N m k : ℕ} (LL : Letters (Fin N)) (S S' : Set (Fin N)) (h : S ⊆ S')
    (e : Fin m → Fin k) (c d : Fin m) (mu : Fin m → ℤ) (x : MvPolynomial (Fin N × Fin k) F)
    (hx : x ∈ isoSub (glOpsE F LL S e) mu) : glOpsE F LL S' e c d x ∈ isoSub (glOpsE F LL S e) mu := by
  rw [glOperatorsEmbedded_union_split LL S S' e h c d x]
  refine Submodule.add_mem _ (isoSub_stab _ mu c d x hx) ?_
  exact isoSub_map_of_comm _ (glOpsE F LL (S' \ S) e c d)
    (fun a b y => glOperatorsEmbedded_commute_of_disjoint LL (S' \ S) S e e (Or.inl fun l hl => hl.2) c d a b y) mu x hx

theorem polynomialProjectors_commute_nested : ProjectorsCommuteNested := by
  intro F _ _ N m k LL S S' e _ hSS pr pr' sys sys' a b
  rcases hSS with h | h
  · exact glOperatorsEmbedded_commute_decomposition LL S S' e e pr pr' sys sys' (fun c d mu x hx => glOperatorsEmbedded_preserves_isotypic_of_subset LL S S' h e c d mu x hx) a b
  · exact (glOperatorsEmbedded_commute_decomposition LL S' S e e pr' pr sys' sys (fun c d mu x hx => glOperatorsEmbedded_preserves_isotypic_of_subset LL S' S h e c d mu x hx) b a).symm

theorem polynomialProjectors_commute_disjoint : ProjectorsCommuteDisjoint := by
  intro F _ _ N m m' k LL S S' e e' _ _ hdis pr pr' sys sys' a b
  refine glOperatorsEmbedded_commute_decomposition LL S S' e e' pr pr' sys sys' (fun c d mu x hx => ?_) a b
  exact isoSub_map_of_comm _ (glOpsE F LL S' e' c d)
    (fun a b y => glOperatorsEmbedded_commute_of_disjoint LL S' S e' e (Or.inr fun a' a h => hdis a a' h.symm) c d a b y) mu x hx

end Formalism.MainNotions.G.ColumnFamilies

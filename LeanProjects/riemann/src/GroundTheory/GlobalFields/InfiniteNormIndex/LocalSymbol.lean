import Mathlib
import GroundTheory.GlobalFields.HerbrandQuotients.Cyclic
import GroundTheory.ProfiniteCohomology.GaloisModules.CoeGalRootsOfUnityHomApply
import GroundTheory.GlobalFields.SemilocalAlgebras.Infinite

noncomputable section

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion GroundTheory.ProfCoh
  GroundTheory.GroupCoh
open scoped NumberField.LiesOver ComplexConjugate

theorem natCard_kerModRange_eq_one {A : Type*} [AddCommGroup A] {f g : A →+ A}
    (h : ∀ x ∈ f.ker, x ∈ g.range) : Nat.card (KerModRange f g) = 1 := by
  have : Subsingleton (KerModRange f g) := ⟨fun p q => by
    induction p using QuotientAddGroup.induction_on with | H x =>
    induction q using QuotientAddGroup.induction_on with | H y =>
    rw [KerModRange.mk_eq_mk_iff]
    exact h _ (sub_mem x.2 y.2)⟩
  exact Nat.card_of_subsingleton (0 : KerModRange f g)

namespace InfinitePlace

def realSignHom {G : Type*} [Group G] (c : G) (hc : c * c = 1) : ℝˣ →* G where
  toFun x := if (x : ℝ) < 0 then c else 1
  map_one' := by simp
  map_mul' x y := by
    simp only [Units.val_mul]
    rcases lt_or_gt_of_ne x.ne_zero with hx | hx <;>
      rcases lt_or_gt_of_ne y.ne_zero with hy | hy
    · simp [hx, hy, not_lt.2 (mul_pos_of_neg_of_neg hx hy).le, hc]
    · simp [hx, not_lt.2 hy.le, mul_neg_of_neg_of_pos hx hy]
    · simp [not_lt.2 hx.le, hy, mul_neg_of_pos_of_neg hx hy]
    · simp [not_lt.2 hx.le, not_lt.2 hy.le, not_lt.2 (mul_pos hx hy).le]

theorem realSignHom_apply {G : Type*} [Group G] (c : G) (hc : c * c = 1) (x : ℝˣ) :
    realSignHom c hc x = if (x : ℝ) < 0 then c else 1 :=
  rfl

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K}
  (w : InfinitePlace L) [w.LiesOver v]

section Degree

theorem finrank_completion_eq_two_iff :
    Module.finrank v.Completion w.Completion = 2 ↔ v.IsReal ∧ w.IsComplex := by
  have hc : w.comap (algebraMap K L) = v := NumberField.InfinitePlace.LiesOver.comap_eq w v
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [h.finrank_eq_one v]
    refine ⟨fun h' => absurd h' (by norm_num), fun ⟨hv, hw⟩ => absurd h ?_⟩
    exact isRamified_iff.2 ⟨hw, hc ▸ hv⟩
  · rw [h.finrank_eq_two v]
    exact ⟨fun _ => ⟨hc ▸ h.isReal, h.isComplex⟩, fun _ => rfl⟩

theorem finrank_completion_eq_one_iff :
    Module.finrank v.Completion w.Completion = 1 ↔ ¬ (v.IsReal ∧ w.IsComplex) := by
  rw [← finrank_completion_eq_two_iff w]
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [h.finrank_eq_one v]; norm_num
  · rw [h.finrank_eq_two v]; norm_num

end Degree

section Conj

variable {w}

theorem extensionEmbedding_algebraMap (hv : v.IsReal) (x : v.Completion) :
    extensionEmbedding w (algebraMap v.Completion w.Completion x) =
      (extensionEmbeddingOfIsReal hv x : ℂ) := by
  have := NumberField.InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w hv
  rw [extensionEmbeddingOfIsReal_apply]
  exact Completion.liesOver_extensionEmbedding_apply w v

open scoped Classical in

def completionConj (hv : v.IsReal) : Gal(w.Completion/v.Completion) :=
  if hw : w.IsComplex then
    AlgEquiv.ofRingEquiv (f := ((ringEquivComplexOfIsComplex hw).trans
      (starRingAut : RingAut ℂ)).trans (ringEquivComplexOfIsComplex hw).symm) (fun x => by
        apply (ringEquivComplexOfIsComplex hw).injective
        simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply, ringEquivComplexOfIsComplex_apply,
          extensionEmbedding_algebraMap hv, starRingAut_apply]
        exact Complex.conj_ofReal _)
  else 1

theorem extensionEmbedding_completionConj (hv : v.IsReal) (x : w.Completion) :
    extensionEmbedding w (completionConj hv x) = conj (extensionEmbedding w x) := by
  by_cases hw : w.IsComplex
  · rw [← ringEquivComplexOfIsComplex_apply hw]
    simp [completionConj, dif_pos hw]
  · rw [completionConj, dif_neg hw, AlgEquiv.one_apply,
      ← extensionEmbeddingOfIsReal_apply (not_isComplex_iff_isReal.1 hw), Complex.conj_ofReal]

theorem completionConj_mul_self (hv : v.IsReal) :
    completionConj (w := w) hv * completionConj hv = 1 := by
  refine AlgEquiv.ext fun x => ?_
  apply (extensionEmbedding w).injective
  simp [AlgEquiv.mul_apply, extensionEmbedding_completionConj]

theorem completionConj_ne_one (hv : v.IsReal) (hw : w.IsComplex) :
    completionConj (w := w) hv ≠ 1 := by
  intro h
  obtain ⟨z, hz⟩ := surjective_extensionEmbedding_of_isComplex hw Complex.I
  have := extensionEmbedding_completionConj (w := w) hv z
  rw [h, AlgEquiv.one_apply, hz, Complex.conj_I] at this
  have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination this
  simp at h2

open scoped Classical in

theorem eq_one_or_eq_completionConj (hv : v.IsReal) (hw : w.IsComplex)
    (σ : Gal(w.Completion/v.Completion)) : σ = 1 ∨ σ = completionConj hv := by
  by_contra h
  push Not at h
  have hcard := AlgEquiv.card_le (F := v.Completion) (K := w.Completion)
  rw [(finrank_completion_eq_two_iff w).2 ⟨hv, hw⟩] at hcard
  have h3 : ({1, completionConj hv, σ} : Finset Gal(w.Completion/v.Completion)).card = 3 :=
    Finset.card_eq_three.2 ⟨1, completionConj hv, σ, (completionConj_ne_one hv hw).symm,
      h.1.symm, h.2.symm, rfl⟩
  have := Finset.card_le_univ ({1, completionConj hv, σ} : Finset Gal(w.Completion/v.Completion))
  omega

open scoped Classical in

theorem univ_eq_one_completionConj (hv : v.IsReal) (hw : w.IsComplex) :
    (Finset.univ : Finset Gal(w.Completion/v.Completion)) = {1, completionConj hv} := by
  ext σ
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact eq_one_or_eq_completionConj hv hw σ

theorem card_gal_eq_two (hv : v.IsReal) (hw : w.IsComplex) :
    Fintype.card Gal(w.Completion/v.Completion) = 2 := by
  classical
  rw [← Finset.card_univ, univ_eq_one_completionConj hv hw]
  exact Finset.card_pair (completionConj_ne_one hv hw).symm

variable (w) in

theorem subsingleton_gal (h : ¬ (v.IsReal ∧ w.IsComplex)) :
    Subsingleton Gal(w.Completion/v.Completion) := by
  have hcard := AlgEquiv.card_le (F := v.Completion) (K := w.Completion)
  rw [(finrank_completion_eq_one_iff w).2 h] at hcard
  exact Fintype.card_le_one_iff_subsingleton.1 hcard

variable (w) in

theorem natCard_gal_completion :
    Nat.card Gal(w.Completion/v.Completion) = Module.finrank v.Completion w.Completion := by
  rw [Nat.card_eq_fintype_card]
  by_cases h2 : v.IsReal ∧ w.IsComplex
  · rw [card_gal_eq_two h2.1 h2.2, (finrank_completion_eq_two_iff w).2 h2]
  · rw [(finrank_completion_eq_one_iff w).2 h2]
    have := subsingleton_gal w h2
    exact Fintype.card_eq_one_iff.2 ⟨1, fun _ => Subsingleton.elim _ _⟩

instance isGalois_completion : IsGalois v.Completion w.Completion :=
  IsGalois.of_card_aut_eq_finrank (h := natCard_gal_completion w)

end Conj

section Norm

variable {w}

theorem algebraMap_norm_completion (hv : v.IsReal) (hw : w.IsComplex) (y : w.Completion) :
    algebraMap v.Completion w.Completion (Algebra.norm v.Completion y) =
      y * completionConj (w := w) hv y := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms, univ_eq_one_completionConj hv hw,
    Finset.prod_pair (completionConj_ne_one hv hw).symm, AlgEquiv.one_apply]

theorem extensionEmbeddingOfIsReal_norm (hv : v.IsReal) (hw : w.IsComplex) (y : w.Completion) :
    extensionEmbeddingOfIsReal hv (Algebra.norm v.Completion y) =
      Complex.normSq (extensionEmbedding w y) := by
  apply Complex.ofReal_injective
  rw [← extensionEmbedding_algebraMap (w := w) hv, algebraMap_norm_completion hv hw, map_mul,
    extensionEmbedding_completionConj, Complex.mul_conj]

variable (v w) in

def normSubgroup : Subgroup v.Completionˣ :=
  (Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion)).range

theorem mem_normSubgroup_iff (hv : v.IsReal) (hw : w.IsComplex) (x : v.Completionˣ) :
    x ∈ normSubgroup v w ↔ 0 < extensionEmbeddingOfIsReal hv x := by
  rw [normSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rw [Units.coe_map, extensionEmbeddingOfIsReal_norm hv hw]
    exact Complex.normSq_pos.2 ((map_ne_zero _).2 y.ne_zero)
  · intro hx
    obtain ⟨a, ha⟩ := surjective_extensionEmbeddingOfIsReal hv
      (Real.sqrt (extensionEmbeddingOfIsReal hv x))
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero, eq_comm, Real.sqrt_eq_zero hx.le] at ha
      exact hx.ne' ha
    refine ⟨Units.mk0 (algebraMap v.Completion w.Completion a) ((map_ne_zero _).2 ha0), ?_⟩
    apply Units.ext
    rw [Units.coe_map, Units.val_mk0, Algebra.norm_algebraMap,
      (finrank_completion_eq_two_iff w).2 ⟨hv, hw⟩]
    apply (extensionEmbeddingOfIsReal hv).injective
    rw [map_pow, ha, Real.sq_sqrt hx.le]

variable (w) in

theorem normSubgroup_eq_top (h : ¬ (v.IsReal ∧ w.IsComplex)) : normSubgroup v w = ⊤ := by
  rw [eq_top_iff]
  intro x _
  refine ⟨Units.map (algebraMap v.Completion w.Completion : v.Completion →* w.Completion) x, ?_⟩
  apply Units.ext
  rw [Units.coe_map, Units.coe_map, MonoidHom.coe_coe, Algebra.norm_algebraMap,
    (finrank_completion_eq_one_iff w).2 h, pow_one]

end Norm

section LocalSymbol

variable (v)

open scoped Classical in

def localSymbol : v.Completionˣ →* Gal(w.Completion/v.Completion) :=
  if hv : v.IsReal then
    (realSignHom (completionConj (w := w) hv) (completionConj_mul_self hv)).comp
      (Units.map (extensionEmbeddingOfIsReal hv).toMonoidHom)
  else 1

theorem localSymbol_apply (hv : v.IsReal) (x : v.Completionˣ) :
    localSymbol v w x =
      if extensionEmbeddingOfIsReal hv x < 0 then completionConj hv else 1 := by
  simp only [localSymbol, dif_pos hv, MonoidHom.comp_apply, realSignHom_apply, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact if_congr Iff.rfl rfl rfl

theorem localSymbol_of_not_isReal (hv : ¬ v.IsReal) : localSymbol v w = 1 := by
  rw [localSymbol, dif_neg hv]

theorem ker_localSymbol : (localSymbol v w).ker = normSubgroup v w := by
  by_cases h2 : v.IsReal ∧ w.IsComplex
  · obtain ⟨hv, hw⟩ := h2
    ext x
    rw [MonoidHom.mem_ker, localSymbol_apply v w hv, mem_normSubgroup_iff hv hw]
    have hx0 : extensionEmbeddingOfIsReal hv x ≠ 0 := (map_ne_zero _).2 x.ne_zero
    constructor
    · intro h
      by_contra hneg
      have hlt : extensionEmbeddingOfIsReal hv x < 0 := lt_of_le_of_ne (not_lt.1 hneg) hx0
      rw [if_pos hlt] at h
      exact completionConj_ne_one hv hw h
    · intro h
      rw [if_neg (not_lt.2 h.le)]
  · rw [normSubgroup_eq_top w h2, eq_top_iff]
    intro x _
    rw [MonoidHom.mem_ker]
    by_cases hv : v.IsReal
    · have hw : ¬ w.IsComplex := fun hw => h2 ⟨hv, hw⟩
      rw [localSymbol_apply v w hv, completionConj, dif_neg hw, ite_self]
    · rw [localSymbol_of_not_isReal v w hv, MonoidHom.one_apply]

theorem localSymbol_surjective : Function.Surjective (localSymbol v w) := by
  intro σ
  by_cases h2 : v.IsReal ∧ w.IsComplex
  · obtain ⟨hv, hw⟩ := h2
    rcases eq_one_or_eq_completionConj hv hw σ with rfl | rfl
    · exact ⟨1, map_one _⟩
    · refine ⟨-1, ?_⟩
      rw [localSymbol_apply v w hv, if_pos]
      simp
  · have := subsingleton_gal w h2
    exact ⟨1, Subsingleton.elim _ _⟩

def normQuotientEquivGal : v.Completionˣ ⧸ normSubgroup v w ≃* Gal(w.Completion/v.Completion) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_localSymbol v w).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (localSymbol_surjective v w))

theorem natCard_quotient_normSubgroup :
    Nat.card (v.Completionˣ ⧸ normSubgroup v w) = Module.finrank v.Completion w.Completion := by
  rw [Nat.card_congr (normQuotientEquivGal v w).toEquiv, natCard_gal_completion w]

end LocalSymbol

section Herbrand

variable (v)

abbrev unitsRep : Representation ℤ Gal(w.Completion/v.Completion) (Additive w.Completionˣ) :=
  zRepOfMonoidEnd (galUnitsHom v.Completion w.Completion)

theorem unitsRep_toMul (σ : Gal(w.Completion/v.Completion)) (x : Additive w.Completionˣ) :
    ((unitsRep v w σ x).toMul : w.Completion) = σ (x.toMul : w.Completion) :=
  rfl

theorem cycSub_unitsRep_toMul (σ : Gal(w.Completion/v.Completion)) (x : Additive w.Completionˣ) :
    ((cycSub (unitsRep v w) σ x).toMul : w.Completion) =
      σ (x.toMul : w.Completion) / (x.toMul : w.Completion) := by
  rw [cycSub_apply, toMul_sub, Units.val_div_eq_div_val, unitsRep_toMul]

variable {v w}

theorem normHom_unitsRep_toMul (hv : v.IsReal) (hw : w.IsComplex) (x : Additive w.Completionˣ) :
    ((normHom (unitsRep v w) x).toMul : w.Completion) =
      (x.toMul : w.Completion) * completionConj (w := w) hv (x.toMul : w.Completion) := by
  classical
  rw [normHom_apply, univ_eq_one_completionConj hv hw,
    Finset.sum_pair (completionConj_ne_one hv hw).symm, toMul_add, Units.val_mul, unitsRep_toMul,
    unitsRep_toMul, AlgEquiv.one_apply]

theorem re_pos_of_mem_range_normHom (hv : v.IsReal) (hw : w.IsComplex)
    {x : Additive w.Completionˣ} (hx : x ∈ (normHom (unitsRep v w)).range) :
    0 < (extensionEmbedding w (x.toMul : w.Completion)).re := by
  obtain ⟨y, rfl⟩ := hx
  rw [normHom_unitsRep_toMul hv hw, map_mul, extensionEmbedding_completionConj, Complex.mul_conj,
    Complex.ofReal_re]
  exact Complex.normSq_pos.2 ((map_ne_zero _).2 (Units.ne_zero _))

theorem mem_range_normHom (hv : v.IsReal) (hw : w.IsComplex) (x : Additive w.Completionˣ)
    (hx : completionConj (w := w) hv (x.toMul : w.Completion) = x.toMul)
    (hpos : 0 < (extensionEmbedding w (x.toMul : w.Completion)).re) :
    x ∈ (normHom (unitsRep v w)).range := by
  have hreal : extensionEmbedding w (x.toMul : w.Completion) =
      ((extensionEmbedding w (x.toMul : w.Completion)).re : ℂ) := by
    have h := extensionEmbedding_completionConj (w := w) hv (x.toMul : w.Completion)
    rw [hx] at h
    exact (Complex.conj_eq_iff_re.1 h.symm).symm
  set r := (extensionEmbedding w (x.toMul : w.Completion)).re
  obtain ⟨a, ha⟩ := surjective_extensionEmbedding_of_isComplex hw (Real.sqrt r : ℂ)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, Complex.ofReal_eq_zero, Real.sqrt_eq_zero hpos.le] at ha
    exact hpos.ne' ha
  refine ⟨Additive.ofMul (Units.mk0 a ha0), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  apply (extensionEmbedding w).injective
  rw [normHom_unitsRep_toMul hv hw, toMul_ofMul, Units.val_mk0, map_mul,
    extensionEmbedding_completionConj, ha, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hpos.le, ← hreal]

theorem exists_conj_eq_mul {z : ℂ} (hz : z * conj z = 1) : ∃ u : ℂ, u ≠ 0 ∧ conj u = z * u := by
  by_cases h : 1 + conj z = 0
  · refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
    have h1 : conj z = -1 := by linear_combination h
    have h2 : z = -1 := by simpa using congrArg conj h1
    rw [h2, Complex.conj_I]
    ring
  · refine ⟨1 + conj z, h, ?_⟩
    rw [map_add, map_one, Complex.conj_conj]
    linear_combination -hz

variable (v w)

theorem natCard_kerModRange_cycSub_normHom (hv : v.IsReal) (hw : w.IsComplex) :
    Nat.card (KerModRange (cycSub (unitsRep v w) (completionConj hv))
      (normHom (unitsRep v w))) = 2 := by
  set c := completionConj (w := w) hv
  have hker : ∀ x : Additive w.Completionˣ,
      x ∈ (cycSub (unitsRep v w) c).ker ↔ c (x.toMul : w.Completion) = x.toMul := by
    intro x
    rw [AddMonoidHom.mem_ker, ← toMul_eq_one, ← Units.val_eq_one, cycSub_unitsRep_toMul,
      div_eq_one_iff_eq (Units.ne_zero _)]
  set m : Additive w.Completionˣ := Additive.ofMul (-1)
  have hm : m ∈ (cycSub (unitsRep v w) c).ker := by
    rw [hker]
    simp [m]
  have hme : extensionEmbedding w (m.toMul : w.Completion) = -1 := by simp [m]
  rw [Nat.card_eq_two_iff]
  refine ⟨QuotientAddGroup.mk ⟨0, zero_mem _⟩, QuotientAddGroup.mk ⟨m, hm⟩, ?_, ?_⟩
  · rw [Ne, KerModRange.mk_eq_mk_iff]
    intro h
    have := re_pos_of_mem_range_normHom hv hw h
    rw [AddSubgroup.coe_mk, zero_sub, toMul_neg, Units.val_inv_eq_inv_val, map_inv₀, hme] at this
    norm_num at this
  · rw [Set.eq_univ_iff_forall]
    intro q
    induction q using QuotientAddGroup.induction_on with | H z =>
    obtain ⟨x, hx⟩ := z
    have hc := (hker x).1 hx
    have hreal : extensionEmbedding w (x.toMul : w.Completion) =
        ((extensionEmbedding w (x.toMul : w.Completion)).re : ℂ) := by
      have h := extensionEmbedding_completionConj (w := w) hv (x.toMul : w.Completion)
      rw [hc] at h
      exact (Complex.conj_eq_iff_re.1 h.symm).symm
    have hne : (extensionEmbedding w (x.toMul : w.Completion)).re ≠ 0 := by
      intro h0
      rw [h0, Complex.ofReal_zero, map_eq_zero] at hreal
      exact Units.ne_zero _ hreal
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · right
      rw [KerModRange.mk_eq_mk_iff]
      apply mem_range_normHom hv hw
      · rw [AddSubgroup.coe_mk, AddSubgroup.coe_mk, toMul_sub, Units.val_div_eq_div_val, map_div₀, hc,
          (hker m).1 hm]
      · rw [AddSubgroup.coe_mk, AddSubgroup.coe_mk, toMul_sub, Units.val_div_eq_div_val, map_div₀,
          hme, div_neg, div_one, Complex.neg_re]
        linarith
    · left
      rw [KerModRange.mk_eq_mk_iff, AddSubgroup.coe_mk, AddSubgroup.coe_mk, sub_zero]
      exact mem_range_normHom hv hw x hc hpos

theorem natCard_kerModRange_normHom_cycSub (hv : v.IsReal) (hw : w.IsComplex) :
    Nat.card (KerModRange (normHom (unitsRep v w))
      (cycSub (unitsRep v w) (completionConj hv))) = 1 := by
  apply natCard_kerModRange_eq_one
  intro x hx
  rw [AddMonoidHom.mem_ker, ← toMul_eq_one, ← Units.val_eq_one, normHom_unitsRep_toMul hv hw] at hx
  have hz : extensionEmbedding w (x.toMul : w.Completion) *
      conj (extensionEmbedding w (x.toMul : w.Completion)) = 1 := by
    rw [← extensionEmbedding_completionConj hv, ← map_mul, hx, map_one]
  obtain ⟨u, hu0, hu⟩ := exists_conj_eq_mul hz
  obtain ⟨y, rfl⟩ := surjective_extensionEmbedding_of_isComplex hw u
  have hy0 : y ≠ 0 := by rintro rfl; exact hu0 (map_zero _)
  refine ⟨Additive.ofMul (Units.mk0 y hy0), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  rw [cycSub_unitsRep_toMul, toMul_ofMul, Units.val_mk0, div_eq_iff hy0]
  apply (extensionEmbedding w).injective
  rw [extensionEmbedding_completionConj, hu, map_mul]

theorem cyclicHerbrand_unitsRep_eq_two (hv : v.IsReal) (hw : w.IsComplex) :
    cyclicHerbrand (unitsRep v w) (completionConj hv) = 2 := by
  rw [cyclicHerbrand, herbrandQuotient, natCard_kerModRange_cycSub_normHom v w hv hw,
    natCard_kerModRange_normHom_cycSub v w hv hw]
  norm_num

theorem hasCyclicHerbrand_unitsRep (hv : v.IsReal) (hw : w.IsComplex) :
    HasCyclicHerbrand (unitsRep v w) (completionConj hv) :=
  ⟨Nat.finite_of_card_ne_zero (by rw [natCard_kerModRange_cycSub_normHom v w hv hw]; norm_num),
    Nat.finite_of_card_ne_zero (by rw [natCard_kerModRange_normHom_cycSub v w hv hw]; norm_num)⟩

theorem cyclicHerbrand_unitsRep_eq_finrank (σ : Gal(w.Completion/v.Completion))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cyclicHerbrand (unitsRep v w) σ = Module.finrank v.Completion w.Completion := by
  by_cases h2 : v.IsReal ∧ w.IsComplex
  · obtain ⟨hv, hw⟩ := h2
    have hσc : σ = completionConj hv := by
      rcases eq_one_or_eq_completionConj hv hw σ with h | h
      · exfalso
        have := hσ (completionConj hv)
        rw [h, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
        exact completionConj_ne_one hv hw this
      · exact h
    rw [hσc, cyclicHerbrand_unitsRep_eq_two v w hv hw, (finrank_completion_eq_two_iff w).2 ⟨hv, hw⟩]
    norm_num
  · rw [(finrank_completion_eq_one_iff w).2 h2]
    have := subsingleton_gal w h2
    have hsub : ∀ x, cycSub (unitsRep v w) σ x = 0 := fun x => by
      rw [Subsingleton.elim σ 1, cycSub_apply, map_one, Module.End.one_apply, sub_self]
    have hnorm : ∀ x, normHom (unitsRep v w) x = x := fun x => by
      rw [normHom_apply, Fintype.sum_subsingleton _ 1, map_one, Module.End.one_apply]
    rw [cyclicHerbrand, herbrandQuotient, natCard_kerModRange_eq_one (fun x _ => ⟨x, hnorm x⟩),
      natCard_kerModRange_eq_one (fun x hx => ⟨0, by
        rw [map_zero]; rw [AddMonoidHom.mem_ker, hnorm] at hx; exact hx.symm⟩)]
    norm_num

end Herbrand

end InfinitePlace

end GroundTheory.Global

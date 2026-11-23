import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersEqSumZetaPowStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Pointwise

noncomputable section

namespace GlobalTheory.TateDecomp

variable {l : ℕ} [Fact l.Prime]

abbrev io (l : ℕ) [Fact l.Prime] : Om l →+* PadicComplex l := algebraMap (Om l) (PadicComplex l)

def subC (F : IntermediateField ℚ_[l] (Om l)) : Subfield (PadicComplex l) := F.toSubfield.map (io l)

theorem inC_iff {F : IntermediateField ℚ_[l] (Om l)} {y : PadicComplex l} :
    y ∈ inC F ↔ y ∈ subC F := Iff.rfl

theorem intC_iff {F : IntermediateField ℚ_[l] (Om l)} {y : PadicComplex l} :
    y ∈ intC F ↔ y ∈ subC F ∧ ‖y‖ ≤ 1 := Iff.rfl

theorem norm_io (x : Om l) : ‖io l x‖ = ‖x‖ := PadicComplex.norm_extends l x

theorem subC_mono {F G : IntermediateField ℚ_[l] (Om l)} (h : F ≤ G) : subC F ≤ subC G := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

theorem Ks_mono (K : FinExt l) {i j : ℕ} (h : i ≤ j) : Ks K i ≤ Ks K j := by
  refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _
  intro x hx
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [pow_add, pow_mul, hx, one_pow]

theorem Ks_le_Kinf (K : FinExt l) (i : ℕ) : Ks K i ≤ Kinf K := by
  refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _
  exact fun x hx => ⟨i, hx⟩

theorem root_mem_Ks (K : FinExt l) {i : ℕ} {x : Om l} (hx : x ^ (l ^ i) = 1) : x ∈ Ks K i :=
  (le_sup_right : _ ≤ Ks K i) (IntermediateField.subset_adjoin _ _ hx)

theorem exists_level (K : FinExt l) {x : Om l} (hx : x ∈ Kinf K) : ∃ i, x ∈ Ks K i := by
  have h : Kinf K ≤ ⨆ i, Ks K i := by
    refine sup_le (le_trans (le_sup_left : _ ≤ Ks K 0) (le_iSup (Ks K) 0)) ?_
    rw [IntermediateField.adjoin_le_iff]
    rintro y ⟨i, hy⟩
    exact le_iSup (Ks K) i (root_mem_Ks K hy)
  have h2 := h hx
  have hd : Directed (· ≤ ·) (Ks K) := Monotone.directed_le fun _ _ h => Ks_mono K h
  have h3 : x ∈ ((⨆ i, Ks K i : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) := h2
  rw [IntermediateField.coe_iSup_of_directed hd] at h3
  simpa using h3

theorem exists_prim (i : ℕ) : ∃ ζ : Om l, IsPrimitiveRoot ζ (l ^ i) := by
  haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ i)

theorem root_mem_subC (K : FinExt l) {i : ℕ} {ξ : PadicComplex l} (h : ξ ^ (l ^ i) = 1) :
    ξ ∈ subC (Ks K i) := by
  haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_prim (l := l) i
  obtain ⟨k, -, rfl⟩ := (hζ.map_of_injective (io l).injective).eq_pow_of_pow_eq_one h
  exact pow_mem (⟨ζ, root_mem_Ks K hζ.pow_eq_one, rfl⟩ : io l ζ ∈ subC (Ks K i)) k

theorem norm_root {i : ℕ} {ξ : PadicComplex l} (h : ξ ^ (l ^ i) = 1) : ‖ξ‖ = 1 := by
  have h2 : ‖ξ‖ ^ (l ^ i) = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _)
    (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)).1 h2

def intA (F : IntermediateField ℚ_[l] (Om l)) : AddSubgroup (PadicComplex l) where
  carrier := intC F
  zero_mem' := ⟨zero_mem (subC F), by simp⟩
  add_mem' := fun {a b} ha hb => ⟨add_mem (intC_iff.1 ha).1 (intC_iff.1 hb).1,
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha.2 hb.2)⟩
  neg_mem' := fun {a} ha => ⟨neg_mem (intC_iff.1 ha).1, by rw [norm_neg]; exact ha.2⟩

theorem Xlev_le (K : FinExt l) (i : ℕ) : Xlev K i ≤ intA (Ks K i) := by
  rw [Xlev, AddSubgroup.closure_le]
  rintro z ⟨ζ, y, hζ, hy, rfl⟩
  refine ⟨mul_mem (root_mem_subC K hζ.pow_eq_one)
    (subC_mono (Ks_mono K (Nat.sub_le i 1)) (intC_iff.1 hy).1), ?_⟩
  rw [norm_mul, norm_root hζ.pow_eq_one, one_mul]
  exact hy.2

def Xsum (K : FinExt l) (j : ℕ) : AddSubgroup (PadicComplex l) := ⨆ (i : ℕ) (_ : j < i), Xlev K i

theorem Xlev_le_Xsum (K : FinExt l) {j i : ℕ} (h : j < i) : Xlev K i ≤ Xsum K j :=
  le_iSup₂_of_le (f := fun (i : ℕ) (_ : j < i) => Xlev K i) i h le_rfl

theorem Xsum_le (K : FinExt l) (j : ℕ) : Xsum K j ≤ intA (Kinf K) := by
  refine iSup₂_le fun i _ x hx => ?_
  have := Xlev_le K i hx
  exact ⟨subC_mono (Ks_le_Kinf K i) (intC_iff.1 this).1, this.2⟩

theorem mem_Xj {K : FinExt l} {j : ℕ} {x : PadicComplex l} :
    x ∈ Xj K j ↔ x ∈ closure (Xsum K j : Set (PadicComplex l)) := Iff.rfl

theorem map_Xj {K : FinExt l} {j : ℕ} (f : PadicComplex l →+ PadicComplex l) (hf : Continuous f)
    (h : ∀ i, j < i → ∀ ζ y : PadicComplex l, IsPrimitiveRoot ζ (l ^ i) →
      y ∈ intC (Ks K (i - 1)) → f (ζ * y) ∈ Xlev K i) {x : PadicComplex l} (hx : x ∈ Xj K j) :
    f x ∈ Xj K j := by
  have h1 : Xsum K j ≤ (Xsum K j).comap f := by
    refine iSup₂_le fun i hi => ?_
    rw [Xlev, AddSubgroup.closure_le]
    rintro z ⟨ζ, y, hζ, hy, rfl⟩
    exact Xlev_le_Xsum K hi (h i hi ζ y hζ hy)
  exact map_mem_closure hf (mem_Xj.1 hx) fun y hy => h1 hy

theorem mul_Xj {K : FinExt l} {j : ℕ} {y x : PadicComplex l} (hy : y ∈ intC (Ks K j))
    (hx : x ∈ Xj K j) : y * x ∈ Xj K j := by
  refine map_Xj (AddMonoidHom.mulLeft y) (continuous_const.mul continuous_id) ?_ hx
  intro i hi ζ w hζ hw
  refine AddSubgroup.subset_closure ⟨ζ, y * w, hζ, ⟨mul_mem
    (subC_mono (Ks_mono K (by omega)) (intC_iff.1 hy).1) (intC_iff.1 hw).1, ?_⟩, ?_⟩
  · rw [norm_mul]; exact mul_le_one₀ hy.2 (norm_nonneg _) hw.2
  · simp only [AddMonoidHom.coe_mulLeft]; ring

theorem gal_Ks {K : FinExt l} {g : GQ l} (hg : g ∈ (K0 K).fixingSubgroup) (i : ℕ) {w : Om l}
    (hw : w ∈ Ks K i) : g w ∈ Ks K i := by
  have h : Ks K i ≤ (Ks K i).comap (g : Om l →ₐ[ℚ_[l]] Om l) := by
    refine sup_le (fun x hx => ?_) ?_
    · have : g x = x := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x hx
      change g x ∈ Ks K i
      rw [this]
      exact (le_sup_left : _ ≤ Ks K i) hx
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      change g x ∈ Ks K i
      refine root_mem_Ks K ?_
      have hx' : x ^ (l ^ i) = 1 := hx
      rw [← map_pow, hx', map_one]
  exact h hw

theorem act_Xj {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {K : FinExt l} {j : ℕ} {g : GQ l} (hg : g ∈ (K0 K).fixingSubgroup) {x : PadicComplex l}
    (hx : x ∈ Xj K j) : act g x ∈ Xj K j := by
  have hc : Continuous ((act g).toRingHom.toAddMonoidHom) :=
    (AddMonoidHomClass.isometry_of_norm _ (ha.2 g)).continuous
  refine map_Xj (act g).toRingHom.toAddMonoidHom hc ?_ hx
  intro i _ ζ w hζ hw
  refine AddSubgroup.subset_closure ⟨act g ζ, act g w, hζ.map_of_injective (act g).injective,
    ⟨?_, by rw [ha.2]; exact hw.2⟩, by simp⟩
  obtain ⟨v, hv, rfl⟩ := hw.1
  exact ⟨g v, gal_Ks hg _ hv, (ha.1 g v).symm⟩

theorem finite_Ks (K : FinExt l) (j : ℕ) : FiniteDimensional ℚ_[l] (Ks K j) := by
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] (K0 K) :=
    Module.Finite.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have hf : {x : Om l | x ^ (l ^ j) = 1}.Finite := by
    refine (Polynomial.nthRootsFinset (l ^ j) (1 : Om l)).finite_toSet.subset fun x hx => ?_
    exact Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset
      (pow_pos (Fact.out : l.Prime).pos _) _).2 hx)
  haveI := hf.to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ j) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  exact IntermediateField.finiteDimensional_sup _ _

theorem isCompact_intC (F : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] F] :
    IsCompact (intC F) := by
  let M : Submodule ℚ_[l] (Om l) := Subalgebra.toSubmodule F.toSubalgebra
  haveI : FiniteDimensional ℚ_[l] M := ‹FiniteDimensional ℚ_[l] F›
  haveI : ProperSpace M := FiniteDimensional.proper ℚ_[l] M
  have hc : Continuous fun x : M => ((x : Om l) : PadicComplex l) :=
    (UniformSpace.Completion.continuous_coe _).comp continuous_subtype_val
  have : intC F = (fun x : M => ((x : Om l) : PadicComplex l)) '' Metric.closedBall 0 1 := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, h⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rw [mem_closedBall_zero_iff]
      exact (norm_io x).symm.le.trans h
    · rintro ⟨x, hx, rfl⟩
      rw [mem_closedBall_zero_iff] at hx
      exact ⟨⟨x, x.2, rfl⟩, (norm_io (x : Om l)).le.trans hx⟩
  rw [this]
  exact (isCompact_closedBall _ _).image hc

theorem Xlev_form (K : FinExt l) {i : ℕ} (hi : 1 ≤ i) {ζ : Om l} (hζ : IsPrimitiveRoot ζ (l ^ i))
    {x : PadicComplex l} (hx : x ∈ Xlev K i) :
    ∃ y : Fin l → Om l, (∀ a, y a ∈ Ks K (i - 1)) ∧ y ⟨0, (Fact.out : l.Prime).pos⟩ = 0 ∧
      x = io l (∑ a : Fin l, ζ ^ (a : ℕ) * y a) := by
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hp.ne_zero⟩
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨ξ, w, hξ, ⟨⟨v, hv, rfl⟩, -⟩, rfl⟩ := hz
    have hζ' := hζ.map_of_injective (io l).injective
    obtain ⟨k, -, rfl⟩ := hζ'.eq_pow_of_pow_eq_one hξ.pow_eq_one
    have hk : k.Coprime (l ^ i) := (hζ'.pow_iff_coprime (pow_pos hp.pos _) k).1 hξ
    have hk2 : k % l ≠ 0 := by
      intro h
      have h1 : l ∣ k := Nat.dvd_of_mod_eq_zero h
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hk h1 (dvd_pow_self l (by omega)))
    have hl : ζ ^ l ∈ Ks K (i - 1) := by
      refine root_mem_Ks K ?_
      rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hi, hζ.pow_eq_one]
    refine ⟨Pi.single ⟨k % l, Nat.mod_lt _ hp.pos⟩ ((ζ ^ l) ^ (k / l) * v), fun a => ?_, ?_, ?_⟩
    · rw [Pi.single_apply]
      split_ifs
      · exact mul_mem (pow_mem hl _) hv
      · exact zero_mem _
    · rw [Pi.single_eq_of_ne]
      intro h
      exact hk2 (congrArg Fin.val h).symm
    · rw [Finset.sum_eq_single ⟨k % l, Nat.mod_lt _ hp.pos⟩]
      · rw [Pi.single_eq_same, ← mul_assoc, ← pow_mul, ← pow_add, Nat.mod_add_div, map_mul, map_pow]
        rfl
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, mul_zero]
      · simp
  | zero => exact ⟨0, fun _ => zero_mem _, rfl, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, h1, h2, rfl⟩ := ha
    obtain ⟨y', h1', h2', rfl⟩ := hb
    refine ⟨y + y', fun a => add_mem (h1 a) (h1' a), by rw [Pi.add_apply, h2, h2', add_zero], ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add]
  | neg a _ ha =>
    obtain ⟨y, h1, h2, rfl⟩ := ha
    refine ⟨-y, fun a => neg_mem (h1 a), by rw [Pi.neg_apply, h2, neg_zero], ?_⟩
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, map_neg]

theorem Xlev_inter (K : FinExt l) {i : ℕ} (hi : 2 ≤ i) {x : PadicComplex l} (hx : x ∈ Xlev K i)
    (hx' : x ∈ subC (Ks K (i - 1))) : x = 0 := by
  have hp : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_prim (l := l) i
  obtain ⟨y, h1, h2, h3⟩ := Xlev_form K (by omega) hζ hx
  obtain ⟨w, hw, rfl⟩ := hx'
  have h4 := (io l).injective h3
  have h5 := (GlobalTheory.T.integers_eq_sum_zeta_pow_unique l K i hi ζ hζ).2 (y - Pi.single ⟨0, hp.pos⟩ w) (fun a => by
    refine sub_mem (h1 a) ?_
    rw [Pi.single_apply]
    split_ifs
    · exact hw
    · exact zero_mem _) (by
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [← h4, Finset.sum_eq_single ⟨0, hp.pos⟩]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · simp) ⟨0, hp.pos⟩
  have h6 : w = 0 := by
    rwa [Pi.sub_apply, h2, Pi.single_eq_same, zero_sub, neg_eq_zero] at h5
  rw [h6, map_zero]

theorem step (K : FinExt l) {i : ℕ} (hi : 2 ≤ i) {z : PadicComplex l} (hz : z ∈ intC (Ks K i)) :
    ∃ y ∈ intC (Ks K (i - 1)), z - y ∈ Xlev K i := by
  have hp : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_prim (l := l) i
  obtain ⟨⟨w, hw, rfl⟩, hn⟩ := intC_iff.1 hz
  rw [norm_io] at hn
  obtain ⟨y, h1, h2⟩ := (GlobalTheory.T.integers_eq_sum_zeta_pow_unique l K i hi ζ hζ).1 w hw hn
  have h3 : ∀ a, io l (y a) ∈ intC (Ks K (i - 1)) := fun a =>
    ⟨⟨y a, (h1 a).1, rfl⟩, (norm_io _).le.trans (h1 a).2⟩
  refine ⟨io l (y ⟨0, hp.pos⟩), h3 _, ?_⟩
  rw [h2, ← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨0, hp.pos⟩)]
  simp only [pow_zero, one_mul, map_add, add_sub_cancel_left, map_sum, map_mul]
  refine sum_mem fun a ha => AddSubgroup.subset_closure ⟨_, _, ?_, h3 a, rfl⟩
  refine (hζ.pow_of_coprime a ?_).map_of_injective (io l).injective
  refine Nat.Coprime.pow_right _ (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 ?_))
  refine Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero fun h => ?_) a.2
  exact (Finset.mem_erase.1 ha).1 (Fin.ext h)

theorem decomp (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {z : PadicComplex l} (hz : z ∈ intC (Kinf K)) :
    ∃ y ∈ intC (Ks K j), z - y ∈ Xsum K j := by
  have key : ∀ n, ∀ z ∈ intC (Ks K (j + n)), ∃ y ∈ intC (Ks K j), z - y ∈ Xsum K j := by
    intro n
    induction n with
    | zero => exact fun z hz => ⟨z, hz, by simp⟩
    | succ n ih =>
      intro z hz
      obtain ⟨w, hw, h⟩ := step K (i := j + (n + 1)) (by omega) hz
      obtain ⟨y, hy, h'⟩ := ih w hw
      refine ⟨y, hy, ?_⟩
      have := add_mem (Xlev_le_Xsum K (show j < j + (n + 1) by omega) h) h'
      simpa using this
  obtain ⟨⟨w, hw, rfl⟩, hn⟩ := intC_iff.1 hz
  obtain ⟨i, hi⟩ := exists_level K hw
  exact key i _ ⟨⟨w, Ks_mono K (by omega) hi, rfl⟩, hn⟩

def Xfin (K : FinExt l) (j : ℕ) (n : ℕ) : AddSubgroup (PadicComplex l) :=
  Nat.rec ⊥ (fun m G => G ⊔ Xlev K (j + (m + 1))) n

theorem Xfin_subC (K : FinExt l) (j n : ℕ) : ∀ x ∈ Xfin K j n, x ∈ subC (Ks K (j + n)) := by
  induction n with
  | zero => intro x hx; rw [AddSubgroup.mem_bot.1 hx]; exact zero_mem _
  | succ n ih =>
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hx
    exact add_mem (subC_mono (Ks_mono K (by omega)) (ih a ha)) (intC_iff.1 (Xlev_le K _ hb)).1

theorem Xsum_inter (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {x : PadicComplex l} (hx : x ∈ Xsum K j)
    (hx' : x ∈ subC (Ks K j)) : x = 0 := by
  have hm : Monotone (Xfin K j) := monotone_nat_of_le_succ fun n => le_sup_left
  have h1 : Xsum K j ≤ ⨆ n, Xfin K j n := by
    refine iSup₂_le fun i hi => ?_
    obtain ⟨n, rfl⟩ : ∃ n, i = j + (n + 1) := ⟨i - j - 1, by omega⟩
    exact le_trans (le_sup_right : _ ≤ Xfin K j (n + 1)) (le_iSup (Xfin K j) (n + 1))
  obtain ⟨n, hn⟩ := (AddSubgroup.mem_iSup_of_directed hm.directed_le).1 (h1 hx)
  clear hx
  induction n with
  | zero => exact AddSubgroup.mem_bot.1 hn
  | succ n ih =>
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hn
    have hb0 : b = 0 := by
      refine Xlev_inter K (by omega) hb ?_
      have := sub_mem (subC_mono (Ks_mono K (show j ≤ j + n by omega)) hx') (Xfin_subC K j n a ha)
      simpa using this
    subst hb0
    exact ih (by rw [add_zero]; exact ha)

theorem natCast_mul_mem {G : AddSubgroup (PadicComplex l)} {x : PadicComplex l} (hx : x ∈ G)
    (m : ℕ) : (l : PadicComplex l) ^ m * x ∈ G := by
  have := nsmul_mem hx (l ^ m)
  rwa [nsmul_eq_mul, Nat.cast_pow] at this

theorem norm_le_of_close (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {y x : PadicComplex l}
    (hy : y ∈ subC (Ks K j)) (hx : x ∈ Xsum K j) (m : ℕ)
    (h : ‖y - x‖ ≤ ‖(l : PadicComplex l)‖ ^ m) : ‖y‖ ≤ ‖(l : PadicComplex l)‖ ^ m := by
  have hl : (l : PadicComplex l) ^ m ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hz : (y - x) / (l : PadicComplex l) ^ m ∈ intC (Kinf K) := by
    refine intC_iff.2 ⟨div_mem (sub_mem (subC_mono (Ks_le_Kinf K j) hy)
      (intC_iff.1 (Xsum_le K j hx)).1) (pow_mem (natCast_mem _ _) _), ?_⟩
    rw [norm_div, norm_pow]
    exact div_le_one_of_le₀ h (by positivity)
  obtain ⟨y', hy', h'⟩ := decomp K hj hz
  have h1 := add_mem (natCast_mul_mem h' m) hx
  have h2 : (l : PadicComplex l) ^ m * ((y - x) / (l : PadicComplex l) ^ m - y') + x
      = y - (l : PadicComplex l) ^ m * y' := by
    field_simp
    ring
  rw [h2] at h1
  have h3 := Xsum_inter K hj h1
    (sub_mem hy (mul_mem (pow_mem (natCast_mem _ _) _) (intC_iff.1 hy').1))
  rw [sub_eq_zero.1 h3, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) hy'.2

theorem norm_l_lt : ‖(l : PadicComplex l)‖ < 1 := by
  have h : (l : PadicComplex l) = io l (algebraMap ℚ_[l] (Om l) (l : ℚ_[l])) := by simp
  rw [h, norm_io, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem Xj_inter (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {x : PadicComplex l} (hx : x ∈ Xj K j)
    (hx' : x ∈ subC (Ks K j)) : x = 0 := by
  have hl : 0 < ‖(l : PadicComplex l)‖ :=
    norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  by_contra h0
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 h0) (norm_l_lt (l := l))
  obtain ⟨w, hw, hd⟩ := Metric.mem_closure_iff.1 (mem_Xj.1 hx) _ (pow_pos hl m)
  rw [dist_eq_norm] at hd
  exact absurd (norm_le_of_close K hj hx' hw m hd.le) (not_le.2 hm)

theorem Ohat_decomp (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {z : PadicComplex l} (hz : z ∈ Ohat K) :
    ∃ y ∈ intC (Ks K j), ∃ x ∈ Xj K j, z = y + x := by
  haveI := finite_Ks K j
  have hc : IsClosed (intC (Ks K j) + (Xj K j : Set (PadicComplex l))) :=
    (AddSubgroup.isClosed_topologicalClosure _).add_left_of_isCompact (isCompact_intC _)
  have h : Ohat K ⊆ intC (Ks K j) + (Xj K j : Set (PadicComplex l)) := by
    refine closure_minimal (fun w hw => ?_) hc
    obtain ⟨y, hy, h⟩ := decomp K hj hw
    exact ⟨y, hy, w - y, subset_closure h, by simp⟩
  obtain ⟨y, hy, x, hx, rfl⟩ := h hz
  exact ⟨y, hy, x, hx, rfl⟩

theorem tate_decomposition : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, 1 ≤ j → (∀ z ∈ Ohat K, ∃ y ∈ intC (Ks K j), ∃ x ∈ Xj K j, z = y + x) ∧ (∀ y ∈ inC (Ks K j), ∀ x ∈ Xj K j, ∀ n : ℕ, (l : PadicComplex l) ^ n * y = x → y = 0) ∧ (∀ x ∈ Xj K j, x ∈ Ohat K) ∧ (∀ y ∈ intC (Ks K j), ∀ x ∈ Xj K j, y * x ∈ Xj K j) ∧ (∀ g ∈ (K0 K).fixingSubgroup, ∀ x ∈ Xj K j, act g x ∈ Xj K j) ∧ (∀ x ∈ Ohat K, ∀ y ∈ intC (Ks K j), y ≠ 0 → y * x ∈ Xj K j → x ∈ Xj K j) := by
  intro l _ act χ ha _ K j hj
  refine ⟨fun z hz => Ohat_decomp K hj hz, ?_, ?_, fun y hy x hx => mul_Xj hy hx,
    fun g hg x hx => act_Xj ha hg hx, ?_⟩
  · rintro y hy x hx n rfl
    have h := Xj_inter K hj hx (mul_mem (pow_mem (natCast_mem _ _) _) (inC_iff.1 hy))
    exact (mul_eq_zero.1 h).resolve_left
      (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  · exact fun x hx => closure_mono (Xsum_le K j) (mem_Xj.1 hx)
  · intro x hx y hy h0 hyx
    obtain ⟨a, ha, b, hb, rfl⟩ := Ohat_decomp K hj hx
    have h1 := sub_mem hyx (mul_Xj hy hb)
    rw [mul_add, add_sub_cancel_right] at h1
    have h2 := Xj_inter K hj h1 (mul_mem (intC_iff.1 hy).1 (intC_iff.1 ha).1)
    rw [(mul_eq_zero.1 h2).resolve_left h0, zero_add]
    exact hb

end GlobalTheory.TateDecomp

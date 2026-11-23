import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory

universe w

variable {ι : Type w}

abbrev Chain (ι : Type w) (n : ℕ) : Type w := (Fin (n + 1) → ι) →₀ ℤ

noncomputable def chainMap {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) : Chain ι n →+ Chain ι m :=
  Finsupp.mapDomain.addMonoidHom fun i => i ∘ θ

lemma chainMap_single {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) (i : Fin (n + 1) → ι) (z : ℤ) :
    chainMap θ (Finsupp.single i z) = Finsupp.single (i ∘ θ) z :=
  Finsupp.mapDomain_single

noncomputable def chainSimplicial (ι : Type w) : SimplicialObject AddCommGrpCat.{w} where
  obj n := AddCommGrpCat.of (Chain ι n.unop.len)
  map θ := AddCommGrpCat.ofHom (chainMap θ.unop.toOrderHom)
  map_id n := AddCommGrpCat.ext fun c => Finsupp.mapDomain_id
  map_comp θ θ' := AddCommGrpCat.ext fun c => by
    change Finsupp.mapDomain _ c = Finsupp.mapDomain _ (Finsupp.mapDomain _ c)
    rw [← Finsupp.mapDomain_comp]
    rfl

noncomputable def bd (n : ℕ) : Chain ι (n + 1) →+ Chain ι n :=
  (AlgebraicTopology.AlternatingFaceMapComplex.objD (chainSimplicial ι) n).hom

lemma bd_apply (n : ℕ) (c : Chain ι (n + 1)) :
    bd n c = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) • chainMap k.succAbove c := by
  have h := hom_finset_sum_apply Finset.univ
    (fun k : Fin (n + 2) => ((-1 : ℤ) ^ (k : ℕ)) • (chainSimplicial ι).δ k) c
  refine h.trans (Finset.sum_congr rfl fun k _ => ?_)
  rfl

lemma bd_single (n : ℕ) (i : Fin (n + 2) → ι) (z : ℤ) :
    bd n (Finsupp.single i z) =
      ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) • Finsupp.single (i ∘ k.succAbove) z := by
  rw [bd_apply]
  simp only [chainMap_single]

lemma bd_bd (n : ℕ) (c : Chain ι (n + 2)) : bd n (bd (n + 1) c) = 0 := by
  have := AlgebraicTopology.AlternatingFaceMapComplex.d_squared (chainSimplicial ι) n
  exact congrArg (fun f => f.hom c) this

noncomputable def aug : Chain ι 0 →+ ℤ := Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ

lemma aug_single (j : Fin 1 → ι) (z : ℤ) : aug (Finsupp.single j z) = z :=
  Finsupp.liftAddHom_apply_single _ _ _

lemma aug_bd (c : Chain ι 1) : aug (bd 0 c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
  | single i z =>
    rw [bd_single, Fin.sum_univ_two]
    simp [aug_single]

noncomputable def lin {m n : ℕ} (f : (Fin (m + 1) → ι) → Chain ι n) : Chain ι m →+ Chain ι n :=
  Finsupp.liftAddHom fun j => zmultiplesHom _ (f j)

lemma lin_single {m n : ℕ} (f : (Fin (m + 1) → ι) → Chain ι n) (j : Fin (m + 1) → ι) (z : ℤ) :
    lin f (Finsupp.single j z) = z • f j := by
  rw [lin, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]

lemma map_mem_supported {m n : ℕ} (L : Chain ι m →+ Chain ι n) {S : Set (Fin (m + 1) → ι)}
    {T : Set (Fin (n + 1) → ι)}
    (h : ∀ j ∈ S, ∀ z : ℤ, L (Finsupp.single j z) ∈ Finsupp.supported ℤ ℤ T) {c : Chain ι m}
    (hc : c ∈ Finsupp.supported ℤ ℤ S) : L c ∈ Finsupp.supported ℤ ℤ T := by
  rw [← Finsupp.sum_single c, Finsupp.sum, map_sum]
  exact Submodule.sum_mem _ fun j hj => h j ((Finsupp.mem_supported ℤ c).1 hc hj) _

lemma eq_of_supported {m : ℕ} {M : Type*} [AddCommGroup M] (L L' : Chain ι m →+ M)
    {S : Set (Fin (m + 1) → ι)} (h : ∀ j ∈ S, ∀ z : ℤ, L (Finsupp.single j z) = L' (Finsupp.single j z))
    {c : Chain ι m} (hc : c ∈ Finsupp.supported ℤ ℤ S) : L c = L' c := by
  rw [← Finsupp.sum_single c, Finsupp.sum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j hj => h j ((Finsupp.mem_supported ℤ c).1 hc hj) _

def rangeIn {n : ℕ} (S : Set ι) : Set (Fin (n + 1) → ι) := {j | Set.range j ⊆ S}

lemma mem_rangeIn {n : ℕ} {S : Set ι} {j : Fin (n + 1) → ι} : j ∈ rangeIn S ↔ Set.range j ⊆ S :=
  Iff.rfl

lemma single_mem_rangeIn {n : ℕ} (i : Fin (n + 1) → ι) (z : ℤ) :
    Finsupp.single i z ∈ Finsupp.supported ℤ ℤ (rangeIn (Set.range i)) :=
  Finsupp.single_mem_supported ℤ z (mem_rangeIn.2 subset_rfl)

lemma lin_mem_rangeIn {m n : ℕ} (f : (Fin (m + 1) → ι) → Chain ι n) {S : Set ι}
    (hf : ∀ j : Fin (m + 1) → ι, Set.range j ⊆ S →
      f j ∈ Finsupp.supported ℤ ℤ (rangeIn (n := n) (Set.range j)))
    {c : Chain ι m} (hc : c ∈ Finsupp.supported ℤ ℤ (rangeIn S)) :
    lin f c ∈ Finsupp.supported ℤ ℤ (rangeIn S) :=
  map_mem_supported _ (fun j hj z => by
    rw [lin_single]
    exact Submodule.smul_mem _ z (Finsupp.supported_mono
      (fun k hk => mem_rangeIn.2 ((mem_rangeIn.1 hk).trans (mem_rangeIn.1 hj))) (hf j hj))) hc

lemma bd_mem_rangeIn {n : ℕ} {S : Set ι} {c : Chain ι (n + 1)}
    (hc : c ∈ Finsupp.supported ℤ ℤ (rangeIn S)) :
    bd n c ∈ Finsupp.supported ℤ ℤ (rangeIn S) :=
  map_mem_supported _ (fun j hj z => by
    rw [bd_single]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Finsupp.single_mem_supported ℤ z
        (mem_rangeIn.2 ((Set.range_comp_subset_range _ _).trans (mem_rangeIn.1 hj))))) hc

noncomputable def cone {n : ℕ} (s : ι) : Chain ι n →+ Chain ι (n + 1) :=
  Finsupp.mapDomain.addMonoidHom fun i => (Fin.cons s i : Fin (n + 2) → ι)

lemma cone_single {n : ℕ} (s : ι) (i : Fin (n + 1) → ι) (z : ℤ) :
    cone s (Finsupp.single i z) = Finsupp.single (Fin.cons s i : Fin (n + 2) → ι) z :=
  Finsupp.mapDomain_single

lemma bd_cone_add_cone_bd (n : ℕ) (s : ι) (c : Chain ι (n + 1)) :
    bd (n + 1) (cone s c) + cone s (bd n c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add]
    rw [add_add_add_comm, hf, hg]
  | single i z =>
    rw [cone_single, bd_single, Fin.sum_univ_succ, bd_single, map_sum]
    simp only [Fin.val_zero, pow_zero, one_smul, cons_comp_succAbove_zero,
      cons_comp_succAbove_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_smul, map_zsmul,
      cone_single]
    rw [add_assoc, ← Finset.sum_add_distrib]
    simp

lemma cone_mem_rangeIn {n : ℕ} {S : Set ι} {s : ι} (hs : s ∈ S) {c : Chain ι n}
    (hc : c ∈ Finsupp.supported ℤ ℤ (rangeIn S)) :
    cone s c ∈ Finsupp.supported ℤ ℤ (rangeIn S) :=
  map_mem_supported _ (fun j hj z => by
    rw [cone_single]
    refine Finsupp.single_mem_supported ℤ z (mem_rangeIn.2 ?_)
    rintro x ⟨a, rfl⟩
    cases a using Fin.cases with
    | zero => simpa using hs
    | succ a => simpa using (mem_rangeIn.1 hj) ⟨a, rfl⟩) hc

section Order

variable [LinearOrder ι]

lemma strictMono_cons {n : ℕ} {s : ι} {j : Fin (n + 1) → ι} (hj : StrictMono j) (hs : s < j 0) :
    StrictMono (Fin.cons s j : Fin (n + 2) → ι) := by
  refine Fin.strictMono_iff_lt_succ.2 fun k => ?_
  cases k using Fin.cases with
  | zero => simpa using hs
  | succ k =>
    rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
    exact hj Fin.castSucc_lt_succ

def ordIn {n : ℕ} (S : Set ι) : Set (Fin (n + 1) → ι) := {j | StrictMono j ∧ Set.range j ⊆ S}

lemma mem_ordIn {n : ℕ} {S : Set ι} {j : Fin (n + 1) → ι} :
    j ∈ ordIn S ↔ StrictMono j ∧ Set.range j ⊆ S :=
  Iff.rfl

def ordFrom {n : ℕ} (s : ι) : Set (Fin (n + 1) → ι) := {j | StrictMono j ∧ s ≤ j 0}

lemma mem_ordFrom {n : ℕ} {s : ι} {j : Fin (n + 1) → ι} : j ∈ ordFrom s ↔ StrictMono j ∧ s ≤ j 0 :=
  Iff.rfl

lemma strictMono_of_fin_one (j : Fin 1 → ι) : StrictMono j := fun a b hab => by
  rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b] at hab
  exact absurd hab (lt_irrefl _)

lemma ordIn_subset_rangeIn {n : ℕ} (S : Set ι) : ordIn (n := n) S ⊆ rangeIn S :=
  fun _ h => mem_rangeIn.2 (mem_ordIn.1 h).2

noncomputable def ocone {n : ℕ} (s : ι) : Chain ι n →+ Chain ι (n + 1) :=
  Finsupp.liftAddHom fun i =>
    if s < i 0 then Finsupp.singleAddHom (Fin.cons s i : Fin (n + 2) → ι) else 0

lemma ocone_single_of_lt {n : ℕ} {s : ι} {i : Fin (n + 1) → ι} (h : s < i 0) (z : ℤ) :
    ocone s (Finsupp.single i z) = Finsupp.single (Fin.cons s i : Fin (n + 2) → ι) z := by
  rw [ocone, Finsupp.liftAddHom_apply_single, if_pos h]
  rfl

lemma ocone_single_of_not_lt {n : ℕ} {s : ι} {i : Fin (n + 1) → ι} (h : ¬ s < i 0) (z : ℤ) :
    ocone s (Finsupp.single i z) = 0 := by
  rw [ocone, Finsupp.liftAddHom_apply_single, if_neg h]
  rfl

lemma bd_ocone_add_ocone_bd (n : ℕ) (s : ι) {c : Chain ι (n + 1)}
    (hc : c ∈ Finsupp.supported ℤ ℤ (ordFrom s)) :
    bd (n + 1) (ocone s c) + ocone s (bd n c) = c := by
  refine eq_of_supported (((bd (n + 1)).comp (ocone s)) + (ocone s).comp (bd n))
    (AddMonoidHom.id _) (fun j hj z => ?_) hc
  obtain ⟨hmono, hsj⟩ := mem_ordFrom.1 hj
  simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
  have hface : ∀ k : Fin (n + 2), s ≤ (j ∘ k.succAbove) 0 := fun k =>
    hsj.trans (hmono.monotone (Fin.zero_le _))
  by_cases hlt : s < j 0
  · have h1 : ocone s (Finsupp.single j z) = cone s (Finsupp.single j z) := by
      rw [ocone_single_of_lt hlt, cone_single]
    have h2 : ocone s (bd n (Finsupp.single j z)) = cone s (bd n (Finsupp.single j z)) := by
      rw [bd_single, map_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, map_zsmul, ocone_single_of_lt (i := j ∘ k.succAbove)
        (show s < j (k.succAbove 0) from hlt.trans_le (hmono.monotone (Fin.zero_le _))),
        cone_single]
    rw [h1, h2]
    exact bd_cone_add_cone_bd n s _
  · have hs : s = j 0 := le_antisymm hsj (not_lt.1 hlt)
    rw [ocone_single_of_not_lt hlt, map_zero, zero_add, bd_single, map_sum, Fin.sum_univ_succ]
    have h0 : s < (j ∘ (0 : Fin (n + 2)).succAbove) 0 := by
      rw [hs]
      exact hmono (by simp)
    rw [map_zsmul, ocone_single_of_lt h0]
    have hrest : ∀ k : Fin (n + 1), ¬ s < (j ∘ k.succ.succAbove) 0 := fun k => by
      simp [Function.comp_apply, hs]
    simp only [map_zsmul, ocone_single_of_not_lt (hrest _), smul_zero, Finset.sum_const_zero,
      add_zero, Fin.val_zero, pow_zero, one_smul]
    congr 1
    rw [hs]
    exact Fin.cons_self_tail j

lemma bd_ocone_zero (s : ι) {c : Chain ι 0} (hc : c ∈ Finsupp.supported ℤ ℤ (ordFrom s)) :
    bd 0 (ocone s c) = c - aug c • Finsupp.single (fun _ => s) 1 := by
  refine eq_of_supported ((bd 0).comp (ocone s))
    (AddMonoidHom.id _ - (zmultiplesHom _ (Finsupp.single (fun _ => s) 1)).comp aug)
    (fun j hj z => ?_) hc
  obtain ⟨-, hsj⟩ := mem_ordFrom.1 hj
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
    zmultiplesHom_apply, aug_single, Finsupp.smul_single_one]
  have hconst : (fun _ : Fin 1 => s) = Fin.cons s j ∘ (1 : Fin 2).succAbove := by
    funext a
    rw [Fin.fin_one_eq_zero a]
    rfl
  by_cases hlt : s < j 0
  · rw [ocone_single_of_lt hlt, bd_single, Fin.sum_univ_two, cons_comp_succAbove_zero, ← hconst]
    simp [sub_eq_add_neg]
  · have hj : j = fun _ => s := by
      funext a
      rw [Fin.fin_one_eq_zero a]
      exact (le_antisymm hsj (not_lt.1 hlt)).symm
    rw [ocone_single_of_not_lt hlt, map_zero, hj, sub_self]

noncomputable def minIdx {n : ℕ} (i : Fin (n + 1) → ι) : ι := Finset.univ.inf' Finset.univ_nonempty i

lemma minIdx_le {n : ℕ} (i : Fin (n + 1) → ι) (a : Fin (n + 1)) : minIdx i ≤ i a :=
  Finset.inf'_le _ (Finset.mem_univ a)

lemma minIdx_mem {n : ℕ} (i : Fin (n + 1) → ι) : minIdx i ∈ Set.range i := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty i
  exact ⟨a, ha.symm⟩

lemma minIdx_of_strictMono {n : ℕ} {i : Fin (n + 1) → ι} (hi : StrictMono i) : minIdx i = i 0 :=
  le_antisymm (minIdx_le i 0)
    (Finset.le_inf' _ _ fun a _ => hi.monotone (Fin.zero_le a))

lemma ordIn_subset_ordFrom {n m : ℕ} (i : Fin (m + 1) → ι) :
    ordIn (n := n) (Set.range i) ⊆ ordFrom (minIdx i) := fun j hjr => by
  obtain ⟨hj, hr⟩ := mem_ordIn.1 hjr
  refine mem_ordFrom.2 ⟨hj, ?_⟩
  obtain ⟨a, ha⟩ := hr ⟨0, rfl⟩
  rw [← ha]
  exact minIdx_le i a

lemma ocone_mem_ordIn {n m : ℕ} (i : Fin (m + 1) → ι) {c : Chain ι n}
    (hc : c ∈ Finsupp.supported ℤ ℤ (ordIn (Set.range i))) :
    ocone (minIdx i) c ∈ Finsupp.supported ℤ ℤ (ordIn (Set.range i)) :=
  map_mem_supported _ (fun j hj z => by
    obtain ⟨hj1, hj2⟩ := mem_ordIn.1 hj
    by_cases hlt : minIdx i < j 0
    · rw [ocone_single_of_lt hlt]
      refine Finsupp.single_mem_supported ℤ z (mem_ordIn.2 ⟨strictMono_cons hj1 hlt, ?_⟩)
      rintro x ⟨a, rfl⟩
      cases a using Fin.cases with
      | zero => simpa using minIdx_mem i
      | succ a => simpa using hj2 ⟨a, rfl⟩
    · rw [ocone_single_of_not_lt hlt]
      exact Submodule.zero_mem _) hc

noncomputable def rho : (n : ℕ) → (Fin (n + 1) → ι) → Chain ι n
  | 0, i => Finsupp.single i 1
  | n + 1, i => ocone (minIdx i) (lin (rho n) (bd n (Finsupp.single i 1)))

lemma lin_rho_zero (c : Chain ι 0) : lin (rho (ι := ι) 0) c = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, hf, hg]
  | single i z => rw [lin_single, rho, Finsupp.smul_single_one]

theorem rho_mem : ∀ (n : ℕ) (i : Fin (n + 1) → ι),
    rho n i ∈ Finsupp.supported ℤ ℤ (ordIn (Set.range i))
  | 0, i => Finsupp.single_mem_supported ℤ _ (mem_ordIn.2 ⟨strictMono_of_fin_one _, subset_rfl⟩)
  | n + 1, i => by
    refine ocone_mem_ordIn i ?_
    refine map_mem_supported _ (fun j hj z => ?_) (bd_mem_rangeIn (single_mem_rangeIn i 1))
    rw [lin_single]
    exact Submodule.smul_mem _ z (Finsupp.supported_mono
      (fun k hk => mem_ordIn.2 ⟨(mem_ordIn.1 hk).1, (mem_ordIn.1 hk).2.trans (mem_rangeIn.1 hj)⟩)
      (rho_mem n j))

theorem bd_rho : ∀ (n : ℕ) (i : Fin (n + 2) → ι),
    bd n (rho (n + 1) i) = lin (rho n) (bd n (Finsupp.single i 1))
  | 0, i => by
    have hx : lin (rho (ι := ι) 0) (bd 0 (Finsupp.single i 1)) ∈
        Finsupp.supported ℤ ℤ (ordFrom (minIdx i)) := by
      rw [lin_rho_zero]
      refine map_mem_supported _ (fun j hj z => ?_) (single_mem_rangeIn i 1)
      rw [bd_single]
      refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
        (Finsupp.single_mem_supported ℤ z (mem_ordFrom.2 ⟨strictMono_of_fin_one _, ?_⟩))
      have hmem : (j ∘ k.succAbove) 0 ∈ Set.range i := (mem_rangeIn.1 hj) ⟨k.succAbove 0, rfl⟩
      obtain ⟨a, ha⟩ := hmem
      rw [← ha]
      exact minIdx_le i a
    rw [rho, bd_ocone_zero _ hx, lin_rho_zero, aug_bd, zero_smul, sub_zero]
  | n + 1, i => by
    have ih := bd_rho n
    have hlin : ∀ c : Chain ι (n + 1), bd n (lin (rho (n + 1)) c) = lin (rho n) (bd n c) := by
      intro c
      have : (bd n).comp (lin (rho (ι := ι) (n + 1))) = (lin (rho (ι := ι) n)).comp (bd n) := by
        refine Finsupp.addHom_ext fun j z => ?_
        simp only [AddMonoidHom.comp_apply, lin_single, map_zsmul, ih]
        rw [← Finsupp.smul_single_one j z, map_zsmul, map_zsmul]
      exact congrArg (fun L => L c) this
    set x := lin (rho (n + 1)) (bd (n + 1) (Finsupp.single i 1)) with hxdef
    have hx : x ∈ Finsupp.supported ℤ ℤ (ordFrom (minIdx i)) := by
      refine Finsupp.supported_mono (ordIn_subset_ordFrom i) ?_
      refine map_mem_supported _ (fun j hj z => ?_) (bd_mem_rangeIn (single_mem_rangeIn i 1))
      rw [lin_single]
      exact Submodule.smul_mem _ z (Finsupp.supported_mono
        (fun k hk => mem_ordIn.2 ⟨(mem_ordIn.1 hk).1, (mem_ordIn.1 hk).2.trans (mem_rangeIn.1 hj)⟩)
        (rho_mem (n + 1) j))
    have hbx : bd n x = 0 := by rw [hxdef, hlin, bd_bd, map_zero]
    have key := bd_ocone_add_ocone_bd n (minIdx i) hx
    rw [hbx, map_zero, add_zero] at key
    change bd (n + 1) (ocone (minIdx i) x) = x
    exact key

theorem rho_of_strictMono : ∀ (n : ℕ) (i : Fin (n + 1) → ι), StrictMono i →
    rho n i = Finsupp.single i 1
  | 0, _, _ => rfl
  | n + 1, i, hi => by
    have h1 : lin (rho n) (bd n (Finsupp.single i 1)) = bd n (Finsupp.single i 1) := by
      rw [bd_single, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, lin_single, one_smul,
        rho_of_strictMono n _ (hi.comp (Fin.strictMono_succAbove k))]
    change ocone (minIdx i) (lin (rho n) (bd n (Finsupp.single i 1))) = _
    rw [h1, minIdx_of_strictMono hi]
    have key := bd_ocone_add_ocone_bd n (i 0) (c := Finsupp.single i 1)
      (Finsupp.single_mem_supported ℤ _ (mem_ordFrom.2 ⟨hi, le_rfl⟩))
    rw [ocone_single_of_not_lt (lt_irrefl _), map_zero, zero_add] at key
    exact key

noncomputable def hmt : (n : ℕ) → (Fin (n + 1) → ι) → Chain ι (n + 1)
  | 0, _ => 0
  | n + 1, i => cone (i 0)
      (Finsupp.single i 1 - rho (n + 1) i - lin (hmt n) (bd n (Finsupp.single i 1)))

theorem hmt_mem : ∀ (n : ℕ) (i : Fin (n + 1) → ι),
    hmt n i ∈ Finsupp.supported ℤ ℤ (rangeIn (Set.range i))
  | 0, _ => Submodule.zero_mem _
  | n + 1, i => by
    refine cone_mem_rangeIn (Set.mem_range_self 0) (Submodule.sub_mem _ (Submodule.sub_mem _
      (single_mem_rangeIn i 1) (Finsupp.supported_mono (ordIn_subset_rangeIn _) (rho_mem _ i))) ?_)
    exact lin_mem_rangeIn _ (fun j _ => hmt_mem n j) (bd_mem_rangeIn (single_mem_rangeIn i 1))

lemma lin_hmt_zero (c : Chain ι 0) : lin (hmt (ι := ι) 0) c = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, hf, hg, add_zero]
  | single i z => rw [lin_single, hmt, smul_zero]

theorem boundary_homotopy : ∀ (n : ℕ) (i : Fin (n + 2) → ι),
    bd (n + 1) (hmt (n + 1) i) + lin (hmt n) (bd n (Finsupp.single i 1)) =
      Finsupp.single i 1 - rho (n + 1) i
  | n, i => by
    set y := Finsupp.single i 1 - rho (n + 1) i - lin (hmt n) (bd n (Finsupp.single i 1))
      with hydef
    have hby : bd n y = 0 := by
      rw [hydef, map_sub, map_sub, bd_rho]
      cases n with
      | zero => rw [lin_hmt_zero, lin_rho_zero, map_zero, sub_self, sub_zero]
      | succ n =>
        have ih := boundary_homotopy n
        have hlin : ∀ c : Chain ι (n + 1), bd (n + 1) (lin (hmt (n + 1)) c) =
            c - lin (rho (n + 1)) c - lin (hmt n) (bd n c) := by
          intro c
          have : (bd (n + 1)).comp (lin (hmt (ι := ι) (n + 1))) =
              AddMonoidHom.id _ - lin (rho (ι := ι) (n + 1)) - (lin (hmt (ι := ι) n)).comp (bd n) := by
            refine Finsupp.addHom_ext fun j z => ?_
            simp only [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
              lin_single, map_zsmul]
            rw [← Finsupp.smul_single_one j z, map_zsmul, map_zsmul, ← smul_sub, ← smul_sub,
              ← ih j, add_sub_cancel_right]
          exact congrArg (fun L => L c) this
        rw [hlin, bd_bd, map_zero, sub_zero]
        abel
    have key := bd_cone_add_cone_bd n (i 0) y
    rw [hby, map_zero, add_zero] at key
    change bd (n + 1) (cone (i 0) y) + _ = _
    rw [key, hydef, sub_add_cancel]

end Order

end GroundTheory.Arith.SchemeCoh

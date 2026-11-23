import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechLeray
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace

universe w u

namespace CechOrdered

section Chains

variable (ι : Type w)

abbrev Chain (q : ℕ) : Type w := (Fin (q + 1) → ι) →₀ ℤ

noncomputable def chainSimplicial : SimplicialObject AddCommGrpCat.{w} where
  obj n := AddCommGrpCat.of (Chain ι n.unop.len)
  map θ := AddCommGrpCat.ofHom (Finsupp.mapDomain.addMonoidHom fun t => t ∘ θ.unop.toOrderHom)
  map_id n := by
    refine AddCommGrpCat.ext fun z => ?_
    change Finsupp.mapDomain id z = z
    exact Finsupp.mapDomain_id
  map_comp θ θ' := by
    refine AddCommGrpCat.ext fun z => ?_
    change Finsupp.mapDomain _ z = Finsupp.mapDomain _ (Finsupp.mapDomain _ z)
    rw [← Finsupp.mapDomain_comp]
    rfl

variable {ι}

noncomputable def bd (q : ℕ) : Chain ι (q + 1) →+ Chain ι q :=
  (AlgebraicTopology.AlternatingFaceMapComplex.objD (chainSimplicial ι) q).hom

lemma bd_single (q : ℕ) (t : Fin (q + 2) → ι) (c : ℤ) :
    bd q (Finsupp.single t c) =
      ∑ a : Fin (q + 2), ((-1 : ℤ) ^ (a : ℕ)) • Finsupp.single (t ∘ a.succAbove) c := by
  have h := hom_finset_sum_apply Finset.univ
    (fun a : Fin (q + 2) => ((-1 : ℤ) ^ (a : ℕ)) • (chainSimplicial ι).δ a) (Finsupp.single t c)
  refine h.trans (Finset.sum_congr rfl fun a _ => ?_)
  change ((-1 : ℤ) ^ (a : ℕ)) • Finsupp.mapDomain _ (Finsupp.single t c) = _
  rw [Finsupp.mapDomain_single]
  rfl

lemma bd_bd (q : ℕ) (z : Chain ι (q + 2)) : bd q (bd (q + 1) z) = 0 := by
  have := AlgebraicTopology.AlternatingFaceMapComplex.d_squared (chainSimplicial ι) q
  exact congrArg (fun f => f.hom z) this

noncomputable def lin {q r : ℕ} (B : (Fin (q + 1) → ι) → Chain ι r) : Chain ι q →+ Chain ι r :=
  Finsupp.liftAddHom fun s => (smulAddHom ℤ (Chain ι r)).flip (B s)

@[simp] lemma lin_single {q r : ℕ} (B : (Fin (q + 1) → ι) → Chain ι r) (s : Fin (q + 1) → ι)
    (c : ℤ) : lin B (Finsupp.single s c) = c • B s := by
  simp [lin]

lemma lin_apply {q r : ℕ} (B : (Fin (q + 1) → ι) → Chain ι r) (z : Chain ι q) :
    lin B z = z.sum fun s c => c • B s := by
  simp [lin, Finsupp.liftAddHom_apply]
  rfl

noncomputable def cone {q : ℕ} (c : ι) : Chain ι q →+ Chain ι (q + 1) :=
  Finsupp.mapDomain.addMonoidHom fun t => (Fin.cons c t : Fin (q + 2) → ι)

lemma cone_single {q : ℕ} (c : ι) (t : Fin (q + 1) → ι) (k : ℤ) :
    cone c (Finsupp.single t k) = Finsupp.single (Fin.cons c t : Fin (q + 2) → ι) k := by
  simp [cone]

lemma cons_comp_succAbove_zero' {n : ℕ} (c : ι) (i : Fin (n + 1) → ι) :
    (Fin.cons c i : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = i := by
  funext a
  simp

lemma cons_comp_succAbove_succ' {n : ℕ} (c : ι) (i : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    (Fin.cons c i : Fin (n + 2) → ι) ∘ k.succ.succAbove = Fin.cons c (i ∘ k.succAbove) := by
  funext a
  cases a using Fin.cases with
  | zero => simp
  | succ a => simp

lemma bd_cone {q : ℕ} (c : ι) (z : Chain ι (q + 1)) :
    bd (q + 1) (cone c z) = z - cone c (bd q z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]; abel
  | single t k =>
    rw [cone_single, bd_single, Fin.sum_univ_succ, bd_single, map_sum]
    simp only [Fin.val_zero, pow_zero, one_smul, cons_comp_succAbove_zero', Fin.val_succ,
      cons_comp_succAbove_succ', map_zsmul, cone_single, pow_succ, mul_neg, mul_one, neg_smul,
      Finset.sum_neg_distrib, sub_eq_add_neg]

def Supp {q : ℕ} (Q : (Fin (q + 1) → ι) → Prop) (z : Chain ι q) : Prop :=
  ∀ t, z t ≠ 0 → Q t

section Supp

variable {q : ℕ} {Q Q' : (Fin (q + 1) → ι) → Prop}

lemma Supp.zero : Supp Q (0 : Chain ι q) := fun _ h => (h rfl).elim

lemma Supp.add {z z' : Chain ι q} (hz : Supp Q z) (hz' : Supp Q z') : Supp Q (z + z') :=
  fun t h => by
    by_cases h1 : z t = 0
    · exact hz' t (by simpa [h1] using h)
    · exact hz t h1

lemma Supp.smul {z : Chain ι q} (c : ℤ) (hz : Supp Q z) : Supp Q (c • z) :=
  fun t h => hz t fun h' => h (by simp [h'])

lemma Supp.neg {z : Chain ι q} (hz : Supp Q z) : Supp Q (-z) := by
  simpa using hz.smul (-1)

lemma Supp.sub {z z' : Chain ι q} (hz : Supp Q z) (hz' : Supp Q z') : Supp Q (z - z') := by
  rw [sub_eq_add_neg]
  exact hz.add hz'.neg

lemma Supp.single {t : Fin (q + 1) → ι} (c : ℤ) (ht : Q t) : Supp Q (Finsupp.single t c) :=
  fun s h => by
    by_cases hs : s = t
    · exact hs ▸ ht
    · exact (h (Finsupp.single_eq_of_ne hs)).elim

lemma Supp.sum {α : Type*} (s : Finset α) (f : α → Chain ι q) (h : ∀ a ∈ s, Supp Q (f a)) :
    Supp Q (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Supp.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

lemma Supp.mono {z : Chain ι q} (hz : Supp Q z) (h : ∀ t, Q t → Q' t) : Supp Q' z :=
  fun t ht => h t (hz t ht)

lemma lin_eq_sum {r : ℕ} (B : (Fin (q + 1) → ι) → Chain ι r) (z : Chain ι q) :
    lin B z = ∑ s ∈ z.support, z s • B s := by
  rw [lin_apply]
  rfl

lemma Supp.lin {r : ℕ} {R : (Fin (r + 1) → ι) → Prop} (B : (Fin (q + 1) → ι) → Chain ι r)
    (z : Chain ι q) (h : ∀ s, z s ≠ 0 → Supp R (B s)) : Supp R (lin B z) := by
  rw [lin_eq_sum]
  exact Supp.sum _ _ fun s hs => (h s (Finsupp.mem_support_iff.mp hs)).smul _

lemma Supp.mapDomain {r : ℕ} {R : (Fin (r + 1) → ι) → Prop}
    (f : (Fin (q + 1) → ι) → (Fin (r + 1) → ι)) {z : Chain ι q} (hz : Supp Q z)
    (h : ∀ t, Q t → R (f t)) : Supp R (Finsupp.mapDomain f z) := by
  classical
  intro s hs
  rw [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply] at hs
  obtain ⟨t, ht, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  by_cases hft : f t = s
  · exact hft ▸ h t (hz t (Finsupp.mem_support_iff.mp ht))
  · simp [hft] at hne

lemma eq_of_supp {M : Type*} [AddCommGroup M] (f g : Chain ι q →+ M) {z : Chain ι q}
    (hz : Supp Q z) (h : ∀ t (k : ℤ), Q t → f (Finsupp.single t k) = g (Finsupp.single t k)) :
    f z = g z := by
  rw [← Finsupp.sum_single z]
  simp only [Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun t ht => h t _ (hz t (Finsupp.mem_support_iff.mp ht))

end Supp

section Lin

variable {q r s : ℕ}

lemma lin_single_id (z : Chain ι q) : lin (fun t => Finsupp.single t 1) z = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z z' hz hz' => rw [map_add, hz, hz']
  | single t k => simp

lemma lin_comp (L : Chain ι r →+ Chain ι s) (B : (Fin (q + 1) → ι) → Chain ι r) (z : Chain ι q) :
    lin (fun t => L (B t)) z = L (lin B z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z z' hz hz' => rw [map_add, hz, hz', map_add, map_add]
  | single t k => simp

lemma lin_sub' (B B' : (Fin (q + 1) → ι) → Chain ι r) (z : Chain ι q) :
    lin (fun t => B t - B' t) z = lin B z - lin B' z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z z' hz hz' => rw [map_add, hz, hz', map_add, map_add]; abel
  | single t k => simp [smul_sub]

lemma lin_zero' (z : Chain ι q) : lin (fun _ => (0 : Chain ι r)) z = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z z' hz hz' => rw [map_add, hz, hz', add_zero]
  | single t k => simp

lemma lin_bd_single (B : (Fin (q + 1) → ι) → Chain ι r) (z : Chain ι (q + 1)) :
    lin (fun t => lin B (bd q (Finsupp.single t 1))) z = lin B (bd q z) := by
  rw [lin_comp (lin B) (fun t => bd q (Finsupp.single t 1)), lin_comp (bd q), lin_single_id]

lemma lin_bd_single_apply (B : (Fin (q + 1) → ι) → Chain ι r) (t : Fin (q + 2) → ι) :
    lin B (bd q (Finsupp.single t 1)) =
      ∑ a : Fin (q + 2), ((-1 : ℤ) ^ (a : ℕ)) • B (t ∘ a.succAbove) := by
  rw [bd_single, map_sum]
  simp

lemma Supp.bd {Q : (Fin (q + 2) → ι) → Prop} {R : (Fin (q + 1) → ι) → Prop} {z : Chain ι (q + 1)}
    (hz : Supp Q z) (h : ∀ t, Q t → ∀ a : Fin (q + 2), R (t ∘ a.succAbove)) : Supp R (bd q z) := by
  rw [← lin_single_id z, ← lin_comp]
  refine Supp.lin _ _ fun t ht => ?_
  rw [bd_single]
  refine Supp.sum _ _ fun a _ => ?_
  exact (Supp.single _ (h t (hz t (by simpa using ht)) a)).smul _

end Lin

variable [LinearOrder ι]

noncomputable def ocone {q : ℕ} (c : ι) : Chain ι q →+ Chain ι (q + 1) :=
  lin fun t => if c < t 0 then Finsupp.single (Fin.cons c t : Fin (q + 2) → ι) 1 else 0

lemma ocone_single {q : ℕ} (c : ι) (t : Fin (q + 1) → ι) (k : ℤ) :
    ocone c (Finsupp.single t k) =
      k • (if c < t 0 then Finsupp.single (Fin.cons c t : Fin (q + 2) → ι) 1 else 0) := by
  simp [ocone]

lemma bd_ocone {q : ℕ} (c : ι) (S : Set ι) (hc : ∀ s ∈ S, c ≤ s) (z : Chain ι (q + 1))
    (hz : Supp (fun t => StrictMono t ∧ ∀ a, t a ∈ S) z) :
    bd (q + 1) (ocone c z) = z - ocone c (bd q z) := by
  refine eq_of_supp ((bd (q + 1)).comp (ocone c))
    (AddMonoidHom.id _ - (ocone c).comp (bd q)) hz fun t k ⟨ht, htS⟩ => ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.sub_apply,
    AddMonoidHom.id_apply]
  rw [ocone_single, bd_single, map_sum]
  have hface : ∀ a : Fin (q + 2), t 0 ≤ (t ∘ a.succAbove) 0 := fun a =>
    ht.monotone (Fin.zero_le _)
  by_cases hct : c < t 0
  · rw [if_pos hct, map_zsmul, ← cone_single, bd_cone, bd_single, map_sum]
    simp only [ocone_single, smul_sub, map_zsmul, Finset.smul_sum]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [if_pos (hct.trans_le (hface a)), cone_single]
      simp [mul_comm]
  · have hc0 : t 0 = c := le_antisymm (not_lt.mp hct) (hc _ (htS 0))
    rw [if_neg hct, smul_zero, map_zero, Fin.sum_univ_succ]
    simp only [ocone_single, Fin.val_zero, pow_zero, one_smul, Fin.val_succ, map_zsmul]
    have h1 : c < (t ∘ (0 : Fin (q + 2)).succAbove) 0 := by
      rw [← hc0]
      exact ht (by simp)
    rw [if_pos h1]
    have h2 : ∀ b : Fin (q + 1), ¬ c < (t ∘ b.succ.succAbove) 0 := fun b => by
      simp [hc0]
    simp only [h2, if_false, smul_zero, Finset.sum_const_zero, add_zero]
    have h3 : (Fin.cons c (t ∘ (0 : Fin (q + 2)).succAbove) : Fin (q + 2) → ι) = t := by
      rw [← hc0]
      funext a
      cases a using Fin.cases with
      | zero => rfl
      | succ a => simp
    rw [h3]
    simp

omit [LinearOrder ι] in

noncomputable def aug {q : ℕ} : Chain ι q →+ ℤ :=
  Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ

omit [LinearOrder ι] in
lemma aug_single {q : ℕ} (t : Fin (q + 1) → ι) (k : ℤ) : aug (Finsupp.single t k) = k := by
  simp [aug]

lemma bd_ocone_zero (c : ι) (S : Set ι) (hc : ∀ s ∈ S, c ≤ s) (z : Chain ι 0)
    (hz : Supp (fun t => t 0 ∈ S) z) :
    bd 0 (ocone c z) = z - aug z • Finsupp.single (fun _ => c) 1 := by
  refine eq_of_supp ((bd 0).comp (ocone c))
    (AddMonoidHom.id _ - (zmultiplesHom _ (Finsupp.single (fun _ => c) 1)).comp aug) hz
    fun t k htS => ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.sub_apply,
    AddMonoidHom.id_apply, zmultiplesHom_apply, aug_single]
  rw [ocone_single]
  by_cases hct : c < t 0
  · rw [if_pos hct, map_zsmul, bd_single, Fin.sum_univ_two]
    have e0 : (Fin.cons c t : Fin 2 → ι) ∘ (0 : Fin 2).succAbove = t := by
      funext a; rw [Fin.fin_one_eq_zero a]; rfl
    have e1 : (Fin.cons c t : Fin 2 → ι) ∘ (1 : Fin 2).succAbove = fun _ => c := by
      funext a; rw [Fin.fin_one_eq_zero a]; rfl
    rw [e0, e1]
    simp [sub_eq_add_neg]
  · have hc0 : t 0 = c := le_antisymm (not_lt.mp hct) (hc _ htS)
    have ht : t = fun _ => c := by funext a; rw [Fin.fin_one_eq_zero a, hc0]
    rw [if_neg hct, smul_zero, map_zero, ht]
    simp

noncomputable def minR {q : ℕ} (i : Fin (q + 1) → ι) : ι :=
  Finset.univ.inf' Finset.univ_nonempty i

lemma minR_le {q : ℕ} (i : Fin (q + 1) → ι) (a : Fin (q + 1)) : minR i ≤ i a :=
  Finset.inf'_le _ (Finset.mem_univ a)

lemma minR_mem {q : ℕ} (i : Fin (q + 1) → ι) : minR i ∈ Set.range i := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty i
  exact ⟨a, ha.symm⟩

noncomputable def proj : (q : ℕ) → (Fin (q + 1) → ι) → Chain ι q
  | 0, i => Finsupp.single i 1
  | q + 1, i => ocone (minR i) (lin (proj q) (bd q (Finsupp.single i 1)))

def InRange {q r : ℕ} (i : Fin (r + 1) → ι) (t : Fin (q + 1) → ι) : Prop := ∀ a, t a ∈ Set.range i

omit [LinearOrder ι] in
lemma inRange_face {q r : ℕ} {i : Fin (r + 2) → ι} {t : Fin (q + 1) → ι} (a : Fin (r + 2))
    (h : InRange (i ∘ a.succAbove) t) : InRange i t := fun b => by
  obtain ⟨c, hc⟩ := h b
  exact ⟨_, hc⟩

lemma proj_supp : ∀ (q : ℕ) (i : Fin (q + 1) → ι),
    Supp (fun t => StrictMono t ∧ InRange i t) (proj q i)
  | 0, i => Supp.single _ ⟨fun a b hab => absurd hab (by simp [Fin.fin_one_eq_zero a,
      Fin.fin_one_eq_zero b]), fun a => ⟨a, rfl⟩⟩
  | q + 1, i => by
    refine Supp.lin _ _ fun t ht => ?_
    have hw : Supp (fun t => StrictMono t ∧ InRange i t)
        (lin (proj q) (bd q (Finsupp.single i 1))) := by
      rw [lin_bd_single_apply]
      refine Supp.sum _ _ fun a _ => ((proj_supp q _).mono fun s hs =>
        ⟨hs.1, inRange_face a hs.2⟩).smul _
    obtain ⟨hts, htr⟩ := hw t ht
    split_ifs with hc
    · refine Supp.single _ ⟨Fin.strictMono_cons.mpr ⟨fun j => hc.trans_le
        (hts.monotone (Fin.zero_le j)), hts⟩, fun a => ?_⟩
      cases a using Fin.cases with
      | zero => exact minR_mem i
      | succ a => simpa using htr a
    · exact Supp.zero

lemma bd_lin_proj (q : ℕ)
    (hq : ∀ i : Fin (q + 2) → ι, bd q (proj (q + 1) i) = lin (proj q) (bd q (Finsupp.single i 1)))
    (z : Chain ι (q + 1)) : bd q (lin (proj (q + 1)) z) = lin (proj q) (bd q z) := by
  rw [← lin_comp, ← lin_bd_single]
  exact congrArg (lin · z) (funext hq)

theorem bd_proj : ∀ (q : ℕ) (i : Fin (q + 2) → ι),
    bd q (proj (q + 1) i) = lin (proj q) (bd q (Finsupp.single i 1))
  | 0, i => by
    have hw : lin (proj 0) (bd 0 (Finsupp.single i 1)) = bd 0 (Finsupp.single i 1) :=
      lin_single_id _
    change bd 0 (ocone (minR i) (lin (proj 0) (bd 0 (Finsupp.single i 1)))) = _
    rw [hw, bd_ocone_zero (minR i) (Set.range i) (fun s ⟨a, ha⟩ => ha ▸ minR_le i a)]
    · have : aug (bd 0 (Finsupp.single i 1)) = 0 := by
        rw [bd_single, map_sum]
        simp [aug_single, Fin.sum_univ_two]
      rw [this, zero_smul, sub_zero]
    · exact Supp.bd (Supp.single (Q := fun t => InRange i t) _ fun a => ⟨a, rfl⟩)
        fun t ht a => ht _
  | q + 1, i => by
    change bd (q + 1) (ocone (minR i) (lin (proj (q + 1)) (bd (q + 1) (Finsupp.single i 1)))) = _
    rw [bd_ocone (minR i) (Set.range i) (fun s ⟨a, ha⟩ => ha ▸ minR_le i a)]
    · rw [bd_lin_proj q (bd_proj q), bd_bd, map_zero, map_zero, sub_zero]
    · rw [lin_bd_single_apply]
      exact Supp.sum _ _ fun a _ => ((proj_supp (q + 1) _).mono fun s hs =>
        ⟨hs.1, fun b => inRange_face a hs.2 b⟩).smul _

theorem proj_of_strictMono : ∀ (q : ℕ) (i : Fin (q + 1) → ι), StrictMono i →
    proj q i = Finsupp.single i 1
  | 0, i, _ => rfl
  | q + 1, i, hi => by
    change ocone (minR i) (lin (proj q) (bd q (Finsupp.single i 1))) = _
    have hmin : minR i = i 0 := le_antisymm (minR_le i 0) (by
      obtain ⟨a, ha⟩ := minR_mem i
      rw [← ha]
      exact hi.monotone (Fin.zero_le a))
    rw [lin_bd_single_apply, hmin]
    simp only [fun a : Fin (q + 2) => proj_of_strictMono q _ (hi.comp (Fin.strictMono_succAbove a)),
      map_sum, map_zsmul, ocone_single, one_smul]
    rw [Fin.sum_univ_succ]
    have h1 : i 0 < (i ∘ (0 : Fin (q + 2)).succAbove) 0 := hi (by simp)
    have h2 : ∀ b : Fin (q + 1), ¬ i 0 < (i ∘ b.succ.succAbove) 0 := fun b => by
      simp
    simp only [h1, h2, if_true, if_false, smul_zero, Finset.sum_const_zero, add_zero,
      Fin.val_zero, pow_zero, one_smul]
    congr 1
    funext a
    cases a using Fin.cases with
    | zero => rfl
    | succ a => simp

theorem proj_eq_zero_of_not_injective (q : ℕ) (i : Fin (q + 1) → ι)
    (hi : ¬ Function.Injective i) : proj q i = 0 := by
  classical
  ext t
  by_contra h
  obtain ⟨hts, htr⟩ := proj_supp q i t h
  have h1 : (Finset.univ.image t).card ≤ (Finset.univ.image i).card :=
    Finset.card_le_card fun x hx => by
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb⟩ := htr a
      exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb⟩
  rw [Finset.card_image_of_injective _ hts.injective, Finset.card_univ, Fintype.card_fin] at h1
  have h2 : (Finset.univ.image i).card = (Finset.univ : Finset (Fin (q + 1))).card :=
    le_antisymm Finset.card_image_le (by rw [Finset.card_univ, Fintype.card_fin]; exact h1)
  exact hi fun a b hab => Finset.card_image_iff.mp h2 (by simp) (by simp) hab

noncomputable def hom : (q : ℕ) → (Fin (q + 1) → ι) → Chain ι (q + 1)
  | 0, _ => 0
  | q + 1, i => cone (i 0)
      (Finsupp.single i 1 - proj (q + 1) i - lin (hom q) (bd q (Finsupp.single i 1)))

lemma hom_supp : ∀ (q : ℕ) (i : Fin (q + 1) → ι), Supp (fun t => InRange i t) (hom q i)
  | 0, _ => Supp.zero
  | q + 1, i => by
    have hw : Supp (fun t => InRange i t)
        (Finsupp.single i 1 - proj (q + 1) i - lin (hom q) (bd q (Finsupp.single i 1))) := by
      refine ((Supp.single _ fun a => ⟨a, rfl⟩).sub
        ((proj_supp (q + 1) i).mono fun t ht => ht.2)).sub ?_
      rw [lin_bd_single_apply]
      exact Supp.sum _ _ fun a _ => ((hom_supp q _).mono fun s hs => inRange_face a hs).smul _
    change Supp _ (Finsupp.mapDomain _ _)
    refine Supp.mapDomain _ hw fun t ht a => ?_
    cases a using Fin.cases with
    | zero => exact ⟨0, rfl⟩
    | succ a => simpa using ht a

theorem bd_hom : ∀ (q : ℕ) (i : Fin (q + 2) → ι),
    bd (q + 1) (hom (q + 1) i) =
      Finsupp.single i 1 - proj (q + 1) i - lin (hom q) (bd q (Finsupp.single i 1))
  | 0, i => by
    change bd 1 (cone (i 0) _) = _
    rw [bd_cone]
    have : bd 0 (Finsupp.single i 1 - proj 1 i - lin (hom 0) (bd 0 (Finsupp.single i 1))) = 0 := by
      rw [map_sub, map_sub, bd_proj, show hom 0 = fun _ => 0 from rfl, lin_zero', map_zero]
      rw [show lin (proj 0) (bd 0 (Finsupp.single i 1)) = bd 0 (Finsupp.single i 1) from
        lin_single_id _]
      simp
    rw [this, map_zero, sub_zero]
  | q + 1, i => by
    change bd (q + 2) (cone (i 0) _) = _
    rw [bd_cone]
    have : bd (q + 1) (Finsupp.single i 1 - proj (q + 2) i -
        lin (hom (q + 1)) (bd (q + 1) (Finsupp.single i 1))) = 0 := by
      rw [map_sub, map_sub, bd_proj, ← lin_comp]
      simp only [bd_hom q]
      rw [lin_sub', lin_sub', lin_single_id, lin_bd_single, bd_bd, map_zero]
      abel
    rw [this, map_zero, sub_zero]

end Chains

section Pairing

variable {ι : Type w} {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)

lemma inter_le_of_inRange {q r : ℕ} {i : Fin (r + 1) → ι} {t : Fin (q + 1) → ι}
    (h : ∀ a, t a ∈ Set.range i) : inter U i ≤ inter U t := by
  intro x hx
  rw [mem_inter_iff] at hx ⊢
  intro a
  obtain ⟨b, hb⟩ := h a
  rw [← hb]
  exact hx b

variable {P U}

open Classical in

noncomputable def pair {q : ℕ} (σ : Cochain P U q) (V : Opens X) : Chain ι q →+ P.obj (op V) :=
  Finsupp.liftAddHom fun t =>
    if h : V ≤ inter U t then zmultiplesHom _ (res P h (σ t)) else 0

lemma pair_single {q : ℕ} (σ : Cochain P U q) {V : Opens X} (t : Fin (q + 1) → ι) (k : ℤ)
    (h : V ≤ inter U t) : pair σ V (Finsupp.single t k) = k • res P h (σ t) := by
  simp [pair, h]

lemma pair_add {q : ℕ} (σ τ : Cochain P U q) (V : Opens X) (z : Chain ι q) :
    pair (σ + τ) V z = pair σ V z + pair τ V z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']; abel
  | single t k =>
    by_cases h : V ≤ inter U t
    · rw [pair_single _ _ _ h, pair_single _ _ _ h, pair_single _ _ _ h, Pi.add_apply, map_add,
        smul_add]
    · simp [pair, h]

lemma pair_zero {q : ℕ} (V : Opens X) (z : Chain ι q) : pair (0 : Cochain P U q) V z = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z z' hz hz' => rw [map_add, hz, hz', add_zero]
  | single t k =>
    by_cases h : V ≤ inter U t
    · rw [pair_single _ _ _ h, Pi.zero_apply, map_zero, smul_zero]
    · simp [pair, h]

lemma res_pair {q : ℕ} (σ : Cochain P U q) {V W : Opens X} (hVW : V ≤ W) {z : Chain ι q}
    (hz : Supp (fun t => W ≤ inter U t) z) : res P hVW (pair σ W z) = pair σ V z := by
  refine eq_of_supp ((res P hVW).comp (pair σ W)) (pair σ V) hz fun t k ht => ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply]
  rw [pair_single _ _ _ ht, pair_single _ _ _ (hVW.trans ht), map_zsmul, res_res]

lemma pair_d {q : ℕ} (σ : Cochain P U q) {V : Opens X} {z : Chain ι (q + 1)}
    (hz : Supp (fun t => V ≤ inter U t) z) : pair (d P U q σ) V z = pair σ V (bd q z) := by
  refine eq_of_supp (pair (d P U q σ) V) ((pair σ V).comp (bd q)) hz fun t k ht => ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply]
  rw [pair_single _ _ _ ht, bd_single, map_sum, d_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_zsmul, res_res, map_zsmul, pair_single _ _ _ (ht.trans (inter_le_comp U t a.succAbove)),
    smul_comm]

end Pairing

section Cochains

variable {ι : Type w} [LinearOrder ι] {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (U : ι → Opens X)

omit [LinearOrder ι] in
lemma supp_inter {q r : ℕ} {i : Fin (r + 1) → ι} {Q : (Fin (q + 1) → ι) → Prop} {z : Chain ι q}
    (hz : Supp Q z) (h : ∀ t, Q t → InRange i t) : Supp (fun t => inter U i ≤ inter U t) z :=
  hz.mono fun t ht => inter_le_of_inRange U (h t ht)

noncomputable def altProj (q : ℕ) : Cochain P U q →+ Cochain P U q where
  toFun σ i := pair σ (inter U i) (proj q i)
  map_zero' := funext fun _ => pair_zero _ _
  map_add' σ τ := funext fun _ => pair_add σ τ _ _

noncomputable def homotopy (q : ℕ) : Cochain P U (q + 1) →+ Cochain P U q where
  toFun σ i := pair σ (inter U i) (hom q i)
  map_zero' := funext fun _ => pair_zero _ _
  map_add' σ τ := funext fun _ => pair_add σ τ _ _

variable {P U}

lemma altProj_apply (q : ℕ) (σ : Cochain P U q) (i : Fin (q + 1) → ι) :
    altProj P U q σ i = pair σ (inter U i) (proj q i) := rfl

lemma homotopy_apply (q : ℕ) (σ : Cochain P U (q + 1)) (i : Fin (q + 1) → ι) :
    homotopy P U q σ i = pair σ (inter U i) (hom q i) := rfl

theorem altProj_apply_of_strictMono (q : ℕ) (σ : Cochain P U q) {i : Fin (q + 1) → ι}
    (hi : StrictMono i) : altProj P U q σ i = σ i := by
  rw [altProj_apply, proj_of_strictMono q i hi, pair_single _ _ _ le_rfl, one_smul, res_refl]

theorem altProj_apply_of_not_injective (q : ℕ) (σ : Cochain P U q) {i : Fin (q + 1) → ι}
    (hi : ¬ Function.Injective i) : altProj P U q σ i = 0 := by
  rw [altProj_apply, proj_eq_zero_of_not_injective q i hi, map_zero]

theorem altProj_eq_zero [Fintype ι] {q : ℕ} (hq : Fintype.card ι ≤ q) (σ : Cochain P U q) :
    altProj P U q σ = 0 := by
  funext i
  refine altProj_apply_of_not_injective q σ fun hi => ?_
  have := Fintype.card_le_of_injective i hi
  rw [Fintype.card_fin] at this
  omega

theorem d_altProj (q : ℕ) (σ : Cochain P U q) :
    d P U q (altProj P U q σ) = altProj P U (q + 1) (d P U q σ) := by
  funext i
  rw [d_apply, altProj_apply, pair_d σ (supp_inter U (proj_supp (q + 1) i) fun t ht => ht.2),
    bd_proj, lin_bd_single_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [altProj_apply, res_pair σ _ (supp_inter U (proj_supp q _) fun t ht => ht.2), map_zsmul]

theorem d_homotopy_add (q : ℕ) (σ : Cochain P U (q + 1)) :
    d P U q (homotopy P U q σ) + homotopy P U (q + 1) (d P U (q + 1) σ) =
      σ - altProj P U (q + 1) σ := by
  funext i
  rw [Pi.add_apply, Pi.sub_apply, d_apply, homotopy_apply,
    pair_d σ (supp_inter U (hom_supp (q + 1) i) fun t ht => ht), bd_hom, map_sub, map_sub,
    lin_bd_single_apply, map_sum, pair_single _ _ _ le_rfl, one_smul, res_refl, altProj_apply]
  have : ∑ a : Fin (q + 2), ((-1 : ℤ) ^ (a : ℕ)) •
      res P (inter_le_comp U i a.succAbove) (homotopy P U q σ (i ∘ a.succAbove)) =
      ∑ a : Fin (q + 2), pair σ (inter U i) (((-1 : ℤ) ^ (a : ℕ)) • hom q (i ∘ a.succAbove)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [homotopy_apply, res_pair σ _ (supp_inter U (hom_supp q _) fun t ht => ht), map_zsmul]
  rw [this]
  abel

theorem homotopy_d_zero (σ : Cochain P U 0) :
    homotopy P U 0 (d P U 0 σ) = σ - altProj P U 0 σ := by
  funext i
  rw [homotopy_apply, Pi.sub_apply, altProj_apply]
  change pair _ _ 0 = σ i - pair σ (inter U i) (Finsupp.single i 1)
  rw [map_zero, pair_single _ _ _ le_rfl, one_smul, res_refl, sub_self]

theorem exists_d_eq_sub_altProj (q : ℕ) (σ : Cochain P U (q + 1)) (hσ : d P U (q + 1) σ = 0) :
    ∃ τ, d P U q τ = σ - altProj P U (q + 1) σ :=
  ⟨homotopy P U q σ, by rw [← d_homotopy_add, hσ, map_zero, add_zero]⟩

theorem eq_altProj_of_d_eq_zero (σ : Cochain P U 0) (hσ : d P U 0 σ = 0) :
    altProj P U 0 σ = σ := by
  have := homotopy_d_zero σ
  rw [hσ, map_zero] at this
  exact (sub_eq_zero.mp this.symm).symm

theorem exists_d_eq_of_card_le [Fintype ι] (q : ℕ) (hq : Fintype.card ι ≤ q + 1)
    (σ : Cochain P U (q + 1)) (hσ : d P U (q + 1) σ = 0) : ∃ τ, d P U q τ = σ := by
  obtain ⟨τ, hτ⟩ := exists_d_eq_sub_altProj q σ hσ
  exact ⟨τ, by rw [hτ, altProj_eq_zero hq, sub_zero]⟩

theorem altProj_congr (q : ℕ) {σ σ' : Cochain P U q} (h : ∀ t, StrictMono t → σ t = σ' t) :
    altProj P U q σ = altProj P U q σ' := by
  funext i
  refine eq_of_supp (pair σ (inter U i)) (pair σ' (inter U i)) (proj_supp q i) fun t k ht => ?_
  have hle := inter_le_of_inRange U ht.2
  rw [pair_single _ _ _ hle, pair_single _ _ _ hle, h t ht.1]

theorem cls_altProj (q : ℕ) (σ : Cochain P U (q + 1)) (hσ : d P U (q + 1) σ = 0) :
    cls (altProj P U (q + 1) σ) (by rw [d_altProj, hσ, map_zero]) = cls σ hσ := by
  rw [cls_eq_cls_iff, coboundaries_succ]
  obtain ⟨τ, hτ⟩ := exists_d_eq_sub_altProj q σ hσ
  exact ⟨τ, hτ⟩

theorem subsingleton_cechH [Fintype ι] {n : ℕ} (hn : Fintype.card ι ≤ n) (hn0 : 0 < n) :
    Subsingleton (cechH P U n) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
  refine subsingleton_of_forall_eq 0 fun c => ?_
  obtain ⟨σ, hσ, rfl⟩ := exists_cls c
  rw [cls_eq_zero_iff, coboundaries_succ]
  exact exists_d_eq_of_card_le q hn σ hσ

end Cochains

end CechOrdered

end GroundTheory.Arith.SchemeCoh

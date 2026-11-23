import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PDFil

variable {B : Type} [CommRing B] {J : Ideal B}

theorem fil_mul_le (δ : DividedPowers J) (a c : ℕ) :
    GlobalTheory.PDA.fil δ a * GlobalTheory.PDA.fil δ c ≤ GlobalTheory.PDA.fil δ (a + c) := by
  unfold GlobalTheory.PDA.fil
  rw [Ideal.span_mul_span']
  refine Ideal.span_mono ?_
  rintro _ ⟨_, ⟨l, hl, hn, rfl⟩, _, ⟨m, hm, hk, rfl⟩, rfl⟩
  refine ⟨l ++ m, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with h | h
    · exact hl p h
    · exact hm p h
  · simp only [List.map_append, List.sum_append]
    omega
  · simp only [List.map_append, List.prod_append]

theorem fil_anti (δ : DividedPowers J) {a c : ℕ} (h : a ≤ c) :
    GlobalTheory.PDA.fil δ c ≤ GlobalTheory.PDA.fil δ a := by
  refine Ideal.span_mono ?_
  rintro b ⟨l, h1, h2, h3⟩
  exact ⟨l, h1, h.trans h2, h3⟩

theorem fil_zero (δ : DividedPowers J) : GlobalTheory.PDA.fil δ 0 = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨[], by simp, by simp, by simp⟩)

theorem dpow_mem_fil (δ : DividedPowers J) (n : ℕ) {x : B} (hx : x ∈ J) :
    δ.dpow n x ∈ GlobalTheory.PDA.fil δ n :=
  Ideal.subset_span ⟨[(n, x)], by simpa using hx, by simp, by simp⟩

def coefFil (δ : DividedPowers J) (Q : PDPoly B) (r : ℕ) : Submodule B Q.P where
  carrier := {z | ∀ k, Q.e.repr z k ∈ GlobalTheory.PDA.fil δ (r - k)}
  add_mem' := by
    intro x y hx hy k
    simpa using Ideal.add_mem _ (hx k) (hy k)
  zero_mem' := by
    intro k
    simp
  smul_mem' := by
    intro c x hx k
    simpa using Ideal.mul_mem_left _ c (hx k)

theorem coefFil_anti (δ : DividedPowers J) (Q : PDPoly B) {a c : ℕ} (h : a ≤ c) {z : Q.P}
    (hz : z ∈ coefFil δ Q c) : z ∈ coefFil δ Q a :=
  fun k ↦ fil_anti δ (by omega) (hz k)

theorem mem_coefFil_zero (δ : DividedPowers J) (Q : PDPoly B) (z : Q.P) :
    z ∈ coefFil δ Q 0 := by
  intro k
  simp [fil_zero]

theorem smul_e_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) {r k : ℕ} {b : B}
    (hb : b ∈ GlobalTheory.PDA.fil δ (r - k)) : b • Q.e k ∈ coefFil δ Q r := by
  intro j
  by_cases h : j = k
  · subst h
    simpa using hb
  · have : Q.e.repr (b • Q.e k) j = 0 := by
      simp [Finsupp.single_apply, Ne.symm h]
    rw [this]
    exact Ideal.zero_mem _

theorem eq_sum_repr (Q : PDPoly B) (z : Q.P) :
    z = ∑ k ∈ (Q.e.repr z).support, Q.e.repr z k • Q.e k := by
  conv_lhs => rw [← Q.e.linearCombination_repr z]
  rfl

theorem smul_e_mul_smul_e_mem (δ : DividedPowers J) (Q : PDPoly B) {a c k l : ℕ} {b b' : B}
    (hb : b ∈ GlobalTheory.PDA.fil δ (a - k)) (hb' : b' ∈ GlobalTheory.PDA.fil δ (c - l)) :
    (b • Q.e k) * (b' • Q.e l) ∈ coefFil δ Q (a + c) := by
  have h1 : b * b' ∈ GlobalTheory.PDA.fil δ (a + c - (k + l)) :=
    fil_anti δ (by omega) (fil_mul_le δ _ _ (Ideal.mul_mem_mul hb hb'))
  rw [smul_mul_smul_comm, Q.e_mul, ← nsmul_eq_mul, smul_comm]
  exact nsmul_mem (smul_e_mem_coefFil δ Q h1) _

theorem mul_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) {a c : ℕ} {z w : Q.P}
    (hz : z ∈ coefFil δ Q a) (hw : w ∈ coefFil δ Q c) : z * w ∈ coefFil δ Q (a + c) := by
  rw [eq_sum_repr Q z, eq_sum_repr Q w, Finset.sum_mul_sum]
  exact Submodule.sum_mem _ fun k _ ↦ Submodule.sum_mem _ fun l _ ↦
    smul_e_mul_smul_e_mem δ Q (hz k) (hw l)

def coefIdeal (δ : DividedPowers J) (Q : PDPoly B) (r : ℕ) : Ideal Q.P where
  carrier := coefFil δ Q r
  add_mem' := (coefFil δ Q r).add_mem
  zero_mem' := (coefFil δ Q r).zero_mem
  smul_mem' := by
    intro c x hx
    simpa using mul_mem_coefFil δ Q (mem_coefFil_zero δ Q c) hx

theorem mem_coefIdeal (δ : DividedPowers J) (Q : PDPoly B) (r : ℕ) (z : Q.P) :
    z ∈ coefIdeal δ Q r ↔ z ∈ coefFil δ Q r := Iff.rfl

theorem algebraMap_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) {r : ℕ} {b : B}
    (hb : b ∈ GlobalTheory.PDA.fil δ r) : algebraMap B Q.P b ∈ coefFil δ Q r := by
  have : algebraMap B Q.P b = b • Q.e 0 := by
    rw [Q.e_zero, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact smul_e_mem_coefFil δ Q (by simpa using hb)

theorem e_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) {n m : ℕ} (h : n ≤ m) :
    Q.e m ∈ coefFil δ Q n := by
  have : (1 : B) ∈ GlobalTheory.PDA.fil δ (n - m) := by
    rw [Nat.sub_eq_zero_of_le h, fil_zero]
    trivial
  simpa using smul_e_mem_coefFil δ Q this

theorem e_mem_ext (Q : PDPoly B) (J : Ideal B) (k : ℕ) : Q.e (k + 1) ∈ Q.ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)

theorem dpow_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) {y : Q.P} (hy : y ∈ Q.ext J) (n : ℕ) :
    η.dpow n y ∈ coefFil δ Q n := by
  let S : Ideal Q.P :=
    { carrier := {y | y ∈ Q.ext J ∧ ∀ n, η.dpow n y ∈ coefFil δ Q n}
      add_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨Ideal.add_mem _ hx hy, fun n ↦ ?_⟩
        rw [η.dpow_add hx hy]
        refine Submodule.sum_mem _ fun p hp ↦ ?_
        have := mul_mem_coefFil δ Q (hx' p.1) (hy' p.2)
        rwa [Finset.HasAntidiagonal.mem_antidiagonal.1 hp] at this
      zero_mem' := by
        refine ⟨Ideal.zero_mem _, fun n ↦ ?_⟩
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · exact mem_coefFil_zero δ Q _
        · rw [η.dpow_eval_zero hn.ne']
          exact Submodule.zero_mem _
      smul_mem' := by
        rintro a y ⟨hy, hy'⟩
        refine ⟨Ideal.mul_mem_left _ a hy, fun n ↦ ?_⟩
        rw [smul_eq_mul, η.dpow_mul hy]
        exact (coefIdeal δ Q n).mul_mem_left _ (hy' n) }
  have hS : Q.ext J ≤ S := by
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun j hj ↦ ?_) (Ideal.span_le.2 ?_)
    · refine ⟨Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hj), fun n ↦ ?_⟩
      rw [h.dp.dpow_comp j hj]
      exact algebraMap_mem_coefFil δ Q (dpow_mem_fil δ n hj)
    · rintro _ ⟨k, rfl⟩
      have h1 : Q.e 1 ∈ Q.ext J := e_mem_ext Q J 0
      refine ⟨e_mem_ext Q J k, fun n ↦ ?_⟩
      show η.dpow n (Q.e (k + 1)) ∈ coefFil δ Q n
      rw [← h.var (k + 1), η.dpow_comp (Nat.succ_ne_zero k) h1, h.var, ← nsmul_eq_mul]
      exact nsmul_mem (e_mem_coefFil δ Q (Nat.le_mul_of_pos_right n (Nat.succ_pos k))) _
  exact (hS hy).2 n

theorem prod_dpow_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (l : List (ℕ × Q.P)) (hl : ∀ p ∈ l, p.2 ∈ Q.ext J) :
    (l.map fun p ↦ η.dpow p.1 p.2).prod ∈ coefFil δ Q (l.map Prod.fst).sum := by
  induction l with
  | nil => simpa using mem_coefFil_zero δ Q 1
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact mul_mem_coefFil δ Q (dpow_mem_coefFil δ Q η h (hl p (by simp)) p.1)
      (ih fun q hq ↦ hl q (List.mem_cons_of_mem _ hq))

theorem fil_le_coefIdeal (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (r : ℕ) : GlobalTheory.PDA.fil η r ≤ coefIdeal δ Q r := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hn, rfl⟩
  exact coefFil_anti δ Q hn (prod_dpow_mem_coefFil δ Q η h l hl)

theorem algebraMap_mem_fil (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (r : ℕ) {b : B} (hb : b ∈ GlobalTheory.PDA.fil δ r) :
    algebraMap B Q.P b ∈ GlobalTheory.PDA.fil η r := by
  have : (GlobalTheory.PDA.fil δ r).map (algebraMap B Q.P) ≤ GlobalTheory.PDA.fil η r := by
    refine Ideal.map_le_iff_le_comap.2 (Ideal.span_le.2 ?_)
    rintro _ ⟨l, hl, hn, rfl⟩
    have hmem : ∀ p ∈ l, algebraMap B Q.P p.2 ∈ Q.ext J := fun p hp ↦
      Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (hl p hp))
    have key : algebraMap B Q.P (l.map fun p ↦ δ.dpow p.1 p.2).prod =
        ((l.map fun p ↦ (p.1, algebraMap B Q.P p.2)).map fun p ↦ η.dpow p.1 p.2).prod := by
      rw [map_list_prod, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left fun p hp ↦ ?_
      exact (h.dp.dpow_comp p.2 (hl p hp)).symm
    show algebraMap B Q.P _ ∈ GlobalTheory.PDA.fil η r
    rw [key]
    refine Ideal.subset_span ⟨_, ?_, ?_, rfl⟩
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hmem q hq
    · simpa [List.map_map, Function.comp_def] using hn
  exact this (Ideal.mem_map_of_mem _ hb)

theorem coefFil_le_fil (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (r : ℕ) {z : Q.P} (hz : z ∈ coefFil δ Q r) : z ∈ GlobalTheory.PDA.fil η r := by
  rw [eq_sum_repr Q z]
  refine Ideal.sum_mem _ fun k _ ↦ ?_
  have h1 : Q.e 1 ∈ Q.ext J := e_mem_ext Q J 0
  have hk : Q.e k ∈ GlobalTheory.PDA.fil η k := by
    rw [← h.var k]
    exact dpow_mem_fil η k h1
  rw [Algebra.smul_def]
  exact fil_anti η (by omega)
    (fil_mul_le η _ _ (Ideal.mul_mem_mul (algebraMap_mem_fil δ Q η h _ (hz k)) hk))

theorem fil_pdPoly : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J)), Q.IsStd δ η → (∀ a c, fil δ a * fil δ c ≤ fil δ (a + c)) ∧ (∀ a c, a ≤ c → fil δ c ≤ fil δ a) ∧ fil δ 0 = ⊤ ∧ ∀ (r : ℕ) (z : Q.P), z ∈ fil η r ↔ ∀ k, Q.e.repr z k ∈ fil δ (r - k) := by
  intro B _ J δ Q η h
  exact ⟨fil_mul_le δ, fun _ _ hac ↦ fil_anti δ hac, fil_zero δ, fun r z ↦
    ⟨fun hz ↦ fil_le_coefIdeal δ Q η h r hz, fun hz ↦ coefFil_le_fil δ Q η h r hz⟩⟩

end GlobalTheory.CompanionTheory.PDFil

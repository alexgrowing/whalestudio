import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockVeronese
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace PowerBlockVeronese

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [∀ k, Fintype (ι k)] in

theorem chartLat_mul {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n m : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a m) : s * t ∈ chartLat y a (n + m) := by
  intro c hc
  have key : s * t * ∏ k, y ⟨k, c k⟩ ^ (-(((n + m : ℕ) : ℤ) * a k)) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) := by
    have hp : ∏ k, y ⟨k, c k⟩ ^ (-(((n + m : ℕ) : ℤ) * a k)) =
        (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_add₀ (hc k)]
      congr 1
      push_cast
      ring
    rw [hp]
    ring
  rw [key]
  exact mul_mem (hs c hc) (ht c hc)

omit [∀ k, Fintype (ι k)] in

theorem one_mem_chartLat (y : (Σ k, ι k) → Ω) (a : K → ℤ) : (1 : Ω) ∈ chartLat y a 0 := by
  intro c _
  simp

omit [∀ k, Fintype (ι k)] in

theorem pow_mem_chartLat {y : (Σ k, ι k) → Ω} {a : K → ℤ} {m : ℕ} {x : Ω} (hx : x ∈ chartLat y a m) (k : ℕ) :
    x ^ k ∈ chartLat y a (m * k) := by
  induction k with
  | zero => simpa using one_mem_chartLat y a
  | succ k ih =>
    rw [pow_succ, Nat.mul_succ]
    exact chartLat_mul ih hx

theorem prod_pow_mem_chartLat {y : (Σ k, ι k) → Ω} {a : K → ℤ} {T : Type} (s : Finset T) (x : T → Ω)
    (k : T → ℕ) (m : ℕ) (h : ∀ t ∈ s, k t ≠ 0 → x t ∈ chartLat y a m) :
    ∏ t ∈ s, x t ^ k t ∈ chartLat y a (m * ∑ t ∈ s, k t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_chartLat y a
  | insert t s ht ih =>
    rw [Finset.prod_insert ht, Finset.sum_insert ht, Nat.mul_add]
    have h1 : x t ^ k t ∈ chartLat y a (m * k t) := by
      by_cases hk : k t = 0
      · rw [hk, pow_zero, Nat.mul_zero]
        exact one_mem_chartLat y a
      · exact pow_mem_chartLat (h t (Finset.mem_insert_self t s) hk) _
    exact chartLat_mul h1 (ih fun t' ht' => h t' (Finset.mem_insert_of_mem ht'))

theorem mul_monomial_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {q : ℕ} {w : Fin q → Ω} {n : ℕ} {s : Ω}
    (hs : s ∈ chartLat y a n) (hw : ∀ j, w j ∈ chartLat y a 1) (μ : Fin q → ℕ) :
    s * ∏ j, w j ^ μ j ∈ chartLat y a (n + ∑ j, μ j) := by
  have h := prod_pow_mem_chartLat (y := y) (a := a) Finset.univ w μ 1 (fun j _ _ => hw j)
  rw [one_mul] at h
  exact chartLat_mul hs h

theorem exists_split {q : ℕ} (μ : Fin q → ℕ) :
    ∀ m : ℕ, m ≤ ∑ j, μ j → ∃ ν ν' : Fin q → ℕ, μ = ν + ν' ∧ ∑ j, ν j = m := by
  intro m
  induction m with
  | zero => intro _; exact ⟨0, μ, by simp, by simp⟩
  | succ m ih =>
    intro hm
    obtain ⟨ν, ν', rfl, hν⟩ := ih (by omega)
    have hs : ∑ j, (ν + ν') j = ∑ j, ν j + ∑ j, ν' j := by
      simp [Finset.sum_add_distrib]
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := ν') (by omega)
    refine ⟨ν + Pi.single j 1, ν' - Pi.single j 1, ?_, ?_⟩
    · funext k
      simp only [Pi.add_apply, Pi.sub_apply]
      by_cases hk : k = j
      · subst hk
        simp only [Pi.single_eq_same]
        omega
      · simp [hk]
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, hν]
      simp

variable [DecidableEq K]

omit [Fintype K] in

theorem blockDeg_add (n n' : ℕ) :
    (blockDeg (none : Option K) n + blockDeg (none : Option K) n' : Option K → ℕ) = blockDeg none (n + n') := by
  funext k
  simp only [Pi.add_apply, blockDeg]
  split_ifs <;> simp

theorem secM_mul {N : ℕ} {z : (Σ k, addIdx ι N k) → Ω} {n n' : ℕ} {s t : Ω}
    (hs : s ∈ secM z (blockDeg (none : Option K) n)) (ht : t ∈ secM z (blockDeg (none : Option K) n')) :
    s * t ∈ secM z (blockDeg (none : Option K) (n + n')) := by
  rw [secM, Submodule.mem_toAddSubgroup] at hs ht ⊢
  have h := Submodule.mul_mem_mul hs ht
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨g, hg, rfl⟩, _, ⟨g', hg', rfl⟩, rfl⟩
  exact ⟨g * g', by rw [← blockDeg_add]; exact ProjLine.mhMul hg hg', map_mul _ _ _⟩

theorem mem_secM_one {y : (Σ k, ι k) → Ω} {N : ℕ} (v : Fin N → Ω) (t : Fin N) :
    v t ∈ secM (addBlock y v) (blockDeg (none : Option K) 1) := by
  rw [secM, Submodule.mem_toAddSubgroup]
  refine Submodule.subset_span ⟨X ⟨none, t⟩, ?_, ?_⟩
  · exact ProjLine.isMultiHomog_X (ι := addIdx ι N) (⟨none, t⟩ : Σ k, addIdx ι N k)
  · rw [aeval_X]
    rfl

theorem secM_le_chartLat {y : (Σ k, ι k) → Ω} {a : K → ℤ} {m N : ℕ} {v : Fin N → Ω}
    (hv : ∀ t, v t ∈ chartLat y a m) (n : ℕ) :
    secM (addBlock y v) (blockDeg (none : Option K) n) ≤ chartLat y a (m * n) := by
  intro s hs
  rw [secM, Submodule.mem_toAddSubgroup] at hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [aeval_def, eval₂_eq']
    refine sum_mem fun α hα => ?_
    rw [← Algebra.smul_def]
    refine zsmul_mem ?_ _
    have hprod := prod_pow_mem_chartLat (y := y) (a := a) Finset.univ (addBlock y v) α m ?_
    · have htot : ∑ p, α p = n := by
        rw [Fintype.sum_sigma, Fintype.sum_option]
        simp only [hg α hα, blockDeg]
        simp
      rwa [htot] at hprod
    · rintro ⟨k, i⟩ - hk
      cases k with
      | none => exact hv i
      | some k =>
        exfalso
        apply hk
        have h0 := hg α hα (some k)
        simp only [blockDeg, reduceCtorEq, if_false] at h0
        exact (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ i)
  | zero => exact zero_mem _
  | add x x' _ _ hx hx' => exact add_mem hx hx'
  | smul r x _ hx => exact zsmul_mem hx r

theorem gen_mem_secM {y : (Σ k, ι k) → Ω} {a : K → ℤ} {q r : ℕ} {w : Fin q → Ω} {d : Fin r → ℕ}
    {e : Fin r → Ω} {m N : ℕ} {v : Fin N → Ω} (hw : ∀ j, w j ∈ chartLat y a 1) (hd : ∀ i, d i ≤ m)
    (hbase : ∀ i (μ : Fin q → ℕ), d i + ∑ j, μ j = m → e i * ∏ j, w j ^ μ j ∈ Set.range v)
    (hfull : chartLat y a m ≤ AddSubgroup.closure (Set.range v)) :
    ∀ n, 1 ≤ n → ∀ i (μ : Fin q → ℕ), d i + ∑ j, μ j = m * n →
      e i * ∏ j, w j ^ μ j ∈ secM (addBlock y v) (blockDeg (none : Option K) n) := by
  have hV1 : AddSubgroup.closure (Set.range v) ≤ secM (addBlock y v) (blockDeg (none : Option K) 1) :=
    (AddSubgroup.closure_le _).mpr (by rintro _ ⟨t, rfl⟩; exact mem_secM_one v t)
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro i μ h
    obtain ⟨t, ht⟩ := hbase i μ (by simpa using h)
    rw [← ht]
    exact mem_secM_one v t
  | succ n hn ih =>
    intro i μ h
    have h1 : m ≤ m * n := Nat.le_mul_of_pos_right m hn
    have h2 : m * (n + 1) = m * n + m := by ring
    have hi := hd i
    obtain ⟨ν, ν', rfl, hν⟩ := exists_split μ m (by
      have hs : ∑ j, μ j = m * (n + 1) - d i := by omega
      omega)
    have hs : ∑ j, (ν + ν') j = ∑ j, ν j + ∑ j, ν' j := by
      simp [Finset.sum_add_distrib]
    have hsplit : e i * ∏ j, w j ^ (ν + ν') j = (e i * ∏ j, w j ^ ν' j) * ∏ j, w j ^ ν j := by
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
      ring
    rw [hsplit]
    have hA := ih i ν' (by omega)
    have hB : ∏ j, w j ^ ν j ∈ secM (addBlock y v) (blockDeg (none : Option K) 1) := by
      have h3 := mul_monomial_mem (one_mem_chartLat y a) hw ν
      rw [one_mul, zero_add, hν] at h3
      exact hV1 (hfull h3)
    exact secM_mul hA hB

def fam {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (e : Fin r → Ω)
    (m : ℕ) : (Fin m → Fin q) ⊕ (Fin r × (Fin q → Fin (m + 1))) → Ω :=
  Sum.elim (fun σ => ∏ l, w (σ l))
    (fun p => if d p.1 + ∑ j, (p.2 j : ℕ) = m then e p.1 * ∏ j, w j ^ (p.2 j : ℕ) else 0)

end PowerBlockVeronese

open PowerBlockVeronese in

theorem PowerBlockVeronese.proof (hFin : SectionRingFinite.Statement) : PowerBlockVeronese.Statement := by
  intro K _ _ ι _ Ω _ y a q w hy hw hgen
  obtain ⟨r, d, e, he, hspan⟩ := hFin K ι Ω y a q w hy hw hgen
  refine ⟨Finset.univ.sup d, fun m hm => ?_⟩
  have hd : ∀ i, d i ≤ m := fun i => (Finset.le_sup (f := d) (Finset.mem_univ i)).trans hm
  set E := Fintype.equivFin ((Fin m → Fin q) ⊕ (Fin r × (Fin q → Fin (m + 1))))
  set v := fam w d e m ∘ E.symm with hvdef
  have hrange : Set.range v = Set.range (fam w d e m) := E.symm.surjective.range_comp _
  have hF1 : ∀ x, fam w d e m x ∈ chartLat y a m := by
    rintro (σ | ⟨i, ν⟩)
    · have h := prod_pow_mem_chartLat (y := y) (a := a) Finset.univ (fun l => w (σ l)) (fun _ => 1) 1
        (fun l _ _ => hw (σ l))
      simpa [fam] using h
    · simp only [fam, Sum.elim_inr]
      split_ifs with h
      · have h' := mul_monomial_mem (he i) hw (fun j => (ν j : ℕ))
        rwa [h] at h'
      · exact zero_mem _
  have hv : ∀ t, v t ∈ chartLat y a m := fun t => hF1 _
  have hbase : ∀ i (μ : Fin q → ℕ), d i + ∑ j, μ j = m → e i * ∏ j, w j ^ μ j ∈ Set.range v := by
    intro i μ h
    rw [hrange]
    have hlt : ∀ j, μ j < m + 1 := fun j => by
      have := Finset.single_le_sum (f := μ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    refine ⟨Sum.inr (i, fun j => ⟨μ j, hlt j⟩), ?_⟩
    simp [fam, h]
  have hfull : chartLat y a m ≤ AddSubgroup.closure (Set.range v) := by
    intro s hs
    refine (AddSubgroup.closure_le _).mpr ?_ (hspan m hs)
    rintro _ ⟨i, μ, h, rfl⟩
    exact AddSubgroup.subset_closure (hbase i μ h)
  refine ⟨Fintype.card ((Fin m → Fin q) ⊕ (Fin r × (Fin q → Fin (m + 1)))), v,
    le_antisymm ((AddSubgroup.closure_le _).mpr (by rintro _ ⟨t, rfl⟩; exact hv t)) hfull, ?_, ?_⟩
  ·
    intro c hc
    obtain ⟨u, hu, hsum⟩ := hgen c hc
    set Y := ∏ k, y ⟨k, c k⟩ ^ (-a k) with hY
    have hYm : Y ^ m = ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k)) := by
      rw [hY, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      ring
    let u' : (Fin m → Fin q) ⊕ (Fin r × (Fin q → Fin (m + 1))) → Ω :=
      Sum.elim (fun σ => ∏ l, u (σ l)) (fun _ => 0)
    refine ⟨u' ∘ E.symm, fun t => ?_, ?_⟩
    · show u' (E.symm t) ∈ _
      rcases E.symm t with σ | p
      · exact prod_mem fun l _ => hu (σ l)
      · exact zero_mem _
    · rw [← hYm]
      have hsum' : ∑ t, (u' ∘ E.symm) t * (v t * Y ^ m) =
          ∑ x, u' x * (fam w d e m x * Y ^ m) :=
        E.symm.sum_comp (fun x => u' x * (fam w d e m x * Y ^ m))
      rw [hsum', Fintype.sum_sum_type]
      simp only [u', fam, Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero]
      have hpow := congrArg (· ^ m) hsum
      simp only [one_pow] at hpow
      rw [← hpow, Fintype.sum_pow]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
  · intro n hn
    refine le_antisymm ?_ (secM_le_chartLat hv n)
    intro s hs
    refine (AddSubgroup.closure_le _).mpr ?_ (hspan (m * n) hs)
    rintro _ ⟨i, μ, h, rfl⟩
    exact gen_mem_secM hw hd hbase hfull n hn i μ h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

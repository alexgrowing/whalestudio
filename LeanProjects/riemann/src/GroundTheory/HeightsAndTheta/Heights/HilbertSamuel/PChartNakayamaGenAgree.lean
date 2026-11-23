import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace ChartNakayamaGen

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

def chart (c : ∀ k, ι k) : KH.Cell K ι 0 :=
  ⟨fun k => {c k}, fun k => Finset.singleton_nonempty _, by simp⟩

theorem eq_chart (J : KH.Cell K ι 0) : J = chart (fun k => (J.2.1 k).choose) := by
  apply Subtype.ext
  funext k
  have h0 : (J.1 k).card - 1 = 0 := (Finset.sum_eq_zero_iff.mp J.2.2) k (Finset.mem_univ k)
  have h1 : (J.1 k).card = 1 := by have := Finset.card_pos.mpr (J.2.1 k); omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
  have hc : (J.2.1 k).choose ∈ J.1 k := (J.2.1 k).choose_spec
  show J.1 k = {(J.2.1 k).choose}
  generalize (J.2.1 k).choose = x at hc ⊢
  rw [ha, Finset.mem_singleton] at hc
  rw [ha, hc]

def chartMon (c : ∀ k, ι k) (e : K → ℕ) : MRingOver S ι :=
  ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ e k

theorem chartMon_add (c : ∀ k, ι k) (e f : K → ℕ) :
    chartMon (S := S) c (e + f) = chartMon c e * chartMon c f := by
  simp only [chartMon, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem chartMon_zero (c : ∀ k, ι k) : chartMon (S := S) c 0 = 1 := by
  simp [chartMon]

theorem chartMon_mem (c : ∀ k, ι k) (e : K → ℕ) : chartMon (S := S) c e ∈ KH.cellMon S (chart c).1 :=
  Submonoid.prod_mem _ fun k _ =>
    Submonoid.pow_mem _ (by
      apply Submonoid.subset_closure
      exact ⟨k, c k, Finset.mem_singleton_self _, rfl⟩) _

theorem isMultiHomog_pow {p : MRingOver S ι} {a : K → ℕ} (hp : IsMultiHomog p a) (n : ℕ) :
    IsMultiHomog (p ^ n) (n • a) := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul]
    exact isMultiHomog_one_zero
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact GenSESStep.isMultiHomog_mul ih hp

theorem isMultiHomog_prod {β : Type} (s : Finset β) (f : β → MRingOver S ι) (a : β → K → ℕ)
    (h : ∀ i ∈ s, IsMultiHomog (f i) (a i)) : IsMultiHomog (∏ i ∈ s, f i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact isMultiHomog_one_zero
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact GenSESStep.isMultiHomog_mul (h b (Finset.mem_insert_self b s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isMultiHomog_chartMon (c : ∀ k, ι k) (e : K → ℕ) : IsMultiHomog (chartMon (S := S) c e) e := by
  classical
  have h := isMultiHomog_prod (S := S) Finset.univ (fun k => (X ⟨k, c k⟩ : MRingOver S ι) ^ e k)
    (fun k => e k • fun l => if l = k then 1 else 0)
    (fun k _ => isMultiHomog_pow (GenSESStep.isMultiHomog_X k (c k)) (e k))
  have he : (∑ k, e k • fun l : K => if l = k then (1 : ℕ) else 0) = e := by
    funext l
    simp [Finset.sum_apply]
  rw [he] at h
  exact h

theorem exists_chartMon {c : ∀ k, ι k} {v : MRingOver S ι} (hv : v ∈ KH.cellMon S (chart c).1) :
    ∃ e, v = chartMon c e := by
  classical
  induction hv using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    have hik : i = c k := Finset.mem_singleton.mp hi
    subst hik
    refine ⟨Pi.single k 1, ?_⟩
    rw [chartMon, Finset.prod_eq_single k]
    · simp
    · intro l _ hl
      simp [hl]
    · intro h
      exact absurd (Finset.mem_univ k) h
  | one => exact ⟨0, (chartMon_zero c).symm⟩
  | mul f g _ _ hf hg =>
    obtain ⟨e, rfl⟩ := hf
    obtain ⟨e', rfl⟩ := hg
    exact ⟨e + e', (chartMon_add c e e').symm⟩

theorem cellMon_notMem {P : Ideal (MRingOver S ι)} (hP : P.IsPrime) {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨k, c k⟩ : MRingOver S ι) ∉ P) {v : MRingOver S ι}
    (hv : v ∈ KH.cellMon S (chart c).1) : v ∉ P := by
  induction hv using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    have hik : i = c k := Finset.mem_singleton.mp hi
    subst hik
    exact hc k
  | one => exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  | mul f g _ _ hf hg => exact fun h => (hP.mem_or_mem h).elim hf hg

theorem dvd_of_mem_pair {c c' : ∀ k, ι k} {v : MRingOver S ι}
    (hv : v ∈ KH.cellMon S (fun k => ({c k, c' k} : Finset (ι k)))) :
    ∃ e : ℕ, v ∣ chartMon c (fun _ => e) * chartMon c' (fun _ => e) := by
  classical
  induction hv using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    refine ⟨1, ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have h : (X ⟨k, c k⟩ : MRingOver S ι) ∣ chartMon c (fun _ => 1) := by
        simpa [chartMon] using
          Finset.dvd_prod_of_mem (fun l => (X ⟨l, c l⟩ : MRingOver S ι)) (Finset.mem_univ k)
      exact h.mul_right _
    · rw [Finset.mem_singleton.mp hi]
      have h : (X ⟨k, c' k⟩ : MRingOver S ι) ∣ chartMon c' (fun _ => 1) := by
        simpa [chartMon] using
          Finset.dvd_prod_of_mem (fun l => (X ⟨l, c' l⟩ : MRingOver S ι)) (Finset.mem_univ k)
      exact h.mul_left _
  | one => exact ⟨0, one_dvd _⟩
  | mul f g _ _ hf hg =>
    obtain ⟨e, he⟩ := hf
    obtain ⟨e', he'⟩ := hg
    refine ⟨e + e', ?_⟩
    have h : chartMon (S := S) c (fun _ => e + e') * chartMon c' (fun _ => e + e') =
        (chartMon c (fun _ => e) * chartMon c' (fun _ => e)) *
          (chartMon c (fun _ => e') * chartMon c' (fun _ => e')) := by
      rw [show (fun _ : K => e + e') = (fun _ => e) + (fun _ => e') from rfl, chartMon_add, chartMon_add]
      ring
    rw [h]
    exact mul_dvd_mul he he'

def pairCell (c : ∀ k, ι k) (k : K) (j : ι k) (hj : j ≠ c k) : KH.Cell K ι 1 :=
  ⟨Function.update (fun l => ({c l} : Finset (ι l))) k {c k, j}, fun l => by
      by_cases hl : l = k
      · subst hl
        simp
      · simp [Function.update_of_ne hl], by
      rw [Finset.sum_eq_single k]
      · simp [Finset.card_pair hj.symm]
      · intro l _ hl
        simp [Function.update_of_ne hl]
      · simp⟩

theorem res_eq_of_pair {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] (c : ∀ k, ι k) (k : K)
    (j : ι k) (hj : j ≠ c k) (f : KH.CechC S ι M 0) (hf : KH.cechD S ι M 0 f = 0) :
    KH.cellRes S M (chart c).1 (pairCell c k j hj).1 (f (chart c)) =
      KH.cellRes S M (chart (Function.update c k j)).1 (pairCell c k j hj).1
        (f (chart (Function.update c k j))) := by
  classical
  have h := congrFun hf (pairCell c k j hj)
  have hIk : (pairCell c k j hj).1 k = {c k, j} := by simp [pairCell]
  have hIl : ∀ l, l ≠ k → (pairCell c k j hj).1 l = {c l} := fun l hl => by
    simp [pairCell, Function.update_of_ne hl]
  generalize pairCell c k j hj = I at h hIk hIl ⊢
  have hne : ∀ l, (I.1 l).Nonempty := I.2.1
  have hxy : c k ≠ j := hj.symm
  have hx : c k ∈ I.1 k := by rw [hIk]; simp
  have hy : j ∈ I.1 k := by rw [hIk]; simp
  have hcard₀ : (I.1 k).card = 2 := by rw [hIk]; exact Finset.card_pair hxy
  have hother : ∀ l, l ≠ k → (I.1 l).card = 1 := fun l hl => by rw [hIl l hl]; rfl
  have hface : ∀ i ∈ I.1 k, (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = 0 := by
    intro i hi
    have hc : ((I.1 k).erase i).card = 1 := by rw [Finset.card_erase_of_mem hi, hcard₀]
    refine ⟨fun l => ?_, Finset.sum_eq_zero fun l _ => ?_⟩
    · by_cases hl : l = k
      · subst hl; rw [Function.update_self]; exact Finset.card_pos.mp (by omega)
      · rw [Function.update_of_ne hl]; exact hne l
    · by_cases hl : l = k
      · subst hl; rw [Function.update_self, hc]; rfl
      · rw [Function.update_of_ne hl, hother l hl]; rfl
  have hsign : KH.faceSign I.1 k j = -KH.faceSign I.1 k (c k) := by
    unfold KH.faceSign
    rcases lt_or_gt_of_ne hxy with h' | h'
    · have e₁ : ((I.1 k).filter (· < c k)).card = 0 := by
        rw [hIk]; simp [Finset.filter_insert, Finset.filter_singleton, h'.not_gt]
      have e₂ : ((I.1 k).filter (· < j)).card = 1 := by
        rw [hIk]; simp [Finset.filter_insert, Finset.filter_singleton, h']
      rw [e₁, e₂, add_comm 1, pow_succ, zero_add]; ring
    · have e₁ : ((I.1 k).filter (· < c k)).card = 1 := by
        rw [hIk]; simp [Finset.filter_insert, Finset.filter_singleton, h']
      have e₂ : ((I.1 k).filter (· < j)).card = 0 := by
        rw [hIk]; simp [Finset.filter_insert, Finset.filter_singleton, h'.not_gt]
      rw [e₁, e₂, add_comm 1, pow_succ, zero_add]; ring
  have key : ∀ (c₀ : ∀ k, ι k) (a : ∀ l, Finset (ι l)) (p : (∀ l, (a l).Nonempty) ∧ ∑ l, ((a l).card - 1) = 0),
      a = (chart c₀).1 →
      KH.cellRes S M a I.1 (f ⟨a, p⟩) = KH.cellRes S M (chart c₀).1 I.1 (f (chart c₀)) := by
    rintro c₀ a p rfl
    rfl
  have f₁ : Function.update I.1 k ((I.1 k).erase (c k)) = (chart (Function.update c k j)).1 := by
    funext l
    by_cases hl : l = k
    · subst hl
      rw [Function.update_self, hIk]
      simp [chart, hxy]
    · rw [Function.update_of_ne hl, hIl l hl]
      simp [chart, Function.update_of_ne hl]
  have f₂ : Function.update I.1 k ((I.1 k).erase j) = (chart c).1 := by
    funext l
    by_cases hl : l = k
    · subst hl
      rw [Function.update_self, hIk]
      ext x
      simp only [chart, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact h2
        · exact absurd h2 h1
      · rintro rfl
        exact ⟨hxy, Or.inl rfl⟩
    · rw [Function.update_of_ne hl, hIl l hl]
      rfl
  change (∑ l : K, ∑ i ∈ I.1 l, _ :
    KH.CechC S ι M 0 →ₗ[MRingOver S ι] LocalizedModule (KH.cellMon S I.1) M) f = 0 at h
  rw [Finset.sum_eq_single k, Finset.sum_eq_add_of_mem (c k) j hx hy hxy, dif_pos (hface (c k) hx),
    dif_pos (hface j hy)] at h
  · rw [hsign, LinearMap.add_apply] at h
    change KH.faceSign I.1 k (c k) • (KH.cellRes S M _ I.1 (f _)) +
      (-KH.faceSign I.1 k (c k)) • (KH.cellRes S M _ I.1 (f _)) = 0 at h
    rw [key _ _ _ f₁, key _ _ _ f₂, neg_smul, ← sub_eq_add_neg] at h
    have h' := sub_eq_zero.mp h
    have hs2 : KH.faceSign I.1 k (c k) * KH.faceSign I.1 k (c k) = 1 := by
      unfold KH.faceSign
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have h'' := congrArg (fun x => KH.faceSign I.1 k (c k) • x) h'
    simp only [smul_smul, hs2, one_smul] at h''
    exact h''.symm
  · intro i hi _
    have : i = c k ∨ i = j := by rw [hIk] at hi; simpa using hi
    tauto
  · intro l _ hl
    refine Finset.sum_eq_zero fun i hi => dif_neg fun h' => ?_
    have := h'.1 l
    rw [Function.update_self, ← Finset.card_pos, Finset.card_erase_of_mem hi, hother l hl] at this
    omega
  · intro h'
    exact absurd (Finset.mem_univ k) h'

theorem cellRes_comp {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] {J P U : ∀ k, Finset (ι k)}
    (h₁ : ∀ k, J k ⊆ P k) (h₂ : ∀ k, P k ⊆ U k) (w : LocalizedModule (KH.cellMon S J) M) :
    KH.cellRes S M P U (KH.cellRes S M J P w) = KH.cellRes S M J U w := by
  induction w using LocalizedModule.induction_on with
  | h m t =>
    rw [GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono h₁),
      GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono h₂),
      GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono fun k => (h₁ k).trans (h₂ k))]

theorem res_agree {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (z : KH.CechC S ι M 0)
    (hz : KH.cechD S ι M 0 z = 0) (c c' : ∀ k, ι k) (U : ∀ k, Finset (ι k)) (hc : ∀ k, c k ∈ U k)
    (hc' : ∀ k, c' k ∈ U k) :
    KH.cellRes S M (chart c).1 U (z (chart c)) = KH.cellRes S M (chart c').1 U (z (chart c')) := by
  classical
  suffices H : ∀ s : Finset K, ∀ c : ∀ k, ι k, (∀ k, c k ∈ U k) → (∀ l ∉ s, c l = c' l) →
      KH.cellRes S M (chart c).1 U (z (chart c)) = KH.cellRes S M (chart c').1 U (z (chart c')) from
    H Finset.univ c hc fun l hl => (hl (Finset.mem_univ l)).elim
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro c _ h
    have e : c = c' := funext fun l => h l (Finset.notMem_empty l)
    subst e
    rfl
  | insert k s _ ih =>
    intro c hcU h
    have hc₂U : ∀ l, Function.update c k (c' k) l ∈ U l := by
      intro l
      by_cases hl : l = k
      · subst hl
        rw [Function.update_self]
        exact hc' l
      · rw [Function.update_of_ne hl]
        exact hcU l
    have hrest : ∀ l ∉ s, Function.update c k (c' k) l = c' l := by
      intro l hl
      by_cases hlk : l = k
      · subst hlk
        rw [Function.update_self]
      · rw [Function.update_of_ne hlk]
        exact h l (by simp [hlk, hl])
    rw [← ih _ hc₂U hrest]
    by_cases hj : c' k = c k
    · have e : Function.update c k (c' k) = c := by rw [hj, Function.update_eq_self]
      rw [e]
    · have hPU : ∀ l, (pairCell c k (c' k) hj).1 l ⊆ U l := by
        intro l
        by_cases hl : l = k
        · subst hl
          simp only [pairCell, Function.update_self]
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hcU _
          · exact hc' _
        · simp only [pairCell, Function.update_of_ne hl]
          intro x hx
          rw [Finset.mem_singleton.mp hx]
          exact hcU l
      have h₁ : ∀ l, (chart c).1 l ⊆ (pairCell c k (c' k) hj).1 l := by
        intro l
        by_cases hl : l = k
        · subst hl
          simp [chart, pairCell]
        · simp [chart, pairCell, Function.update_of_ne hl]
      have h₂ : ∀ l, (chart (Function.update c k (c' k))).1 l ⊆ (pairCell c k (c' k) hj).1 l := by
        intro l
        by_cases hl : l = k
        · subst hl
          simp [chart, pairCell]
        · simp [chart, pairCell, Function.update_of_ne hl]
      rw [← cellRes_comp h₁ hPU, ← cellRes_comp h₂ hPU, res_eq_of_pair c k (c' k) hj z hz]

end ChartNakayamaGen

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

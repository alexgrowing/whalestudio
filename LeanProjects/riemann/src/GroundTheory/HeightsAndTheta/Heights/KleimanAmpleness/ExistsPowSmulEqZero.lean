import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon IsMGraded)

namespace SectionMapInj

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

noncomputable def chartMon (S : Type) [CommRing S] (c : ∀ k, ι k) : MRingOver S ι :=
  ∏ k, X ⟨k, c k⟩

def chartCell (c : ∀ k, ι k) : Cell K ι 0 :=
  ⟨fun k => {c k}, fun _ => Finset.singleton_nonempty _, by simp⟩

theorem dvd_pow_of_mem_cellMon (c : ∀ k, ι k) {t : MRingOver S ι} (ht : t ∈ cellMon S (chartCell c).1) :
    ∃ n : ℕ, t ∣ chartMon S c ^ n := by
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    rw [show i = c k from Finset.mem_singleton.mp hi]
    exact ⟨1, by rw [pow_one]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ k)⟩
  | one => exact ⟨0, one_dvd _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    exact ⟨m + n, by rw [pow_add]; exact mul_dvd_mul hm hn⟩

variable {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]

theorem pow_smul_eq_zero_of_le {r : MRingOver S ι} {y : M} {m n : ℕ} (h : r ^ m • y = 0) (hmn : m ≤ n) :
    r ^ n • y = 0 := by
  rw [← Nat.sub_add_cancel hmn, pow_add, mul_smul, h, smul_zero]

theorem exists_pow_smul_eq_zero (c : ∀ k, ι k) {t : MRingOver S ι} (ht : t ∈ cellMon S (chartCell c).1) {y : M}
    (hy : t • y = 0) : ∃ n : ℕ, chartMon S c ^ n • y = 0 := by
  obtain ⟨n, q, hq⟩ := dvd_pow_of_mem_cellMon c ht
  exact ⟨n, by rw [hq, mul_comm, mul_smul, hy, smul_zero]⟩

theorem exists_chart_dvd (N : ℕ) (μ : (Σ k, ι k) →₀ ℕ) (r : S)
    (hμ : ∀ k, Fintype.card (ι k) * N + 1 ≤ ∑ i, μ ⟨k, i⟩) :
    ∃ c : ∀ k, ι k, chartMon S c ^ N ∣ (monomial μ r : MRingOver S ι) := by
  classical
  have hex : ∀ k, ∃ i, N ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra hne
    simp only [not_exists, not_le] at hne
    have hle : ∑ i, μ ⟨k, i⟩ ≤ ∑ _i : ι k, N := Finset.sum_le_sum fun i _ => (hne i).le
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    have := hμ k
    omega
  choose c hc using hex
  refine ⟨c, ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun q => pow_zero _), Fintype.prod_sigma, chartMon,
    ← Finset.prod_pow]
  refine Dvd.dvd.mul_left (Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_) _
  exact (pow_dvd_pow _ (hc k)).trans (Finset.dvd_prod_of_mem (fun i => (X ⟨k, i⟩ : MRingOver S ι) ^ μ ⟨k, i⟩)
    (Finset.mem_univ (c k)))

variable [Module S M] [IsScalarTower S (MRingOver S ι) M]

def killedSet (𝓜 : (K → ℤ) → Submodule S M) : Set M :=
  {y | (∃ d, y ∈ 𝓜 d) ∧ ∃ n : ℕ, ∀ c : ∀ k, ι k, chartMon S c ^ n • y = 0}

theorem bound_finset (𝓜 : (K → ℤ) → Submodule S M) (F : Finset M) (hF : (↑F : Set M) ⊆ killedSet (ι := ι) 𝓜) :
    ∃ (D : ℤ) (N : ℕ), ∀ f ∈ F, ∃ d : K → ℤ, f ∈ 𝓜 d ∧ (∀ k, d k ≤ D) ∧
      ∀ c : ∀ k, ι k, chartMon S c ^ N • f = 0 := by
  classical
  revert hF
  induction F using Finset.induction_on with
  | empty => intro _; exact ⟨0, 0, by simp⟩
  | insert a F ha ih =>
    intro hF
    rw [Finset.coe_insert, Set.insert_subset_iff] at hF
    obtain ⟨D, N, hDN⟩ := ih hF.2
    obtain ⟨⟨d, hd⟩, n, hn⟩ := hF.1
    refine ⟨max D (∑ k, |d k|), max N n, fun f hf => ?_⟩
    rcases Finset.mem_insert.mp hf with rfl | hf
    · refine ⟨d, hd, fun k => ?_, fun c => pow_smul_eq_zero_of_le (hn c) (le_max_right _ _)⟩
      exact ((le_abs_self _).trans (Finset.single_le_sum (f := fun k => |d k|) (fun l _ => abs_nonneg _)
        (Finset.mem_univ k))).trans (le_max_right _ _)
    · obtain ⟨e, he, heD, heN⟩ := hDN f hf
      exact ⟨e, he, fun k => (heD k).trans (le_max_left _ _),
        fun c => pow_smul_eq_zero_of_le (heN c) (le_max_left _ _)⟩

theorem exists_finset_span [IsNoetherian (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) :
    ∃ F : Finset M, (↑F : Set M) ⊆ killedSet (ι := ι) 𝓜 ∧
      ∀ y ∈ killedSet (ι := ι) 𝓜, y ∈ Submodule.span (MRingOver S ι) (↑F : Set M) := by
  classical
  obtain ⟨W, ⟨F, hFH, rfl⟩, hmax⟩ := (set_has_maximal_iff_noetherian (R := MRingOver S ι) (M := M)).mpr ‹_›
    {W | ∃ F : Finset M, (↑F : Set M) ⊆ killedSet (ι := ι) 𝓜 ∧ W = Submodule.span (MRingOver S ι) (↑F : Set M)}
    ⟨_, ∅, by simp, rfl⟩
  refine ⟨F, hFH, fun y hy => ?_⟩
  by_contra hn
  refine hmax (Submodule.span _ ↑(insert y F)) ⟨insert y F, ?_, rfl⟩ ?_
  · rw [Finset.coe_insert]; exact Set.insert_subset hy hFH
  · refine lt_of_le_of_ne (Submodule.span_mono (by simp)) fun h => hn ?_
    rw [h]; exact Submodule.subset_span (by simp)

end SectionMapInj

theorem SectionMapInj.full : SectionMapInj.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 hS hfin hM
  classical
  have := hS
  have : IsNoetherian (MRingOver S ι) M := isNoetherian_of_isNoetherianRing_of_finite _ _
  obtain ⟨F, hFH, hspan⟩ := SectionMapInj.exists_finset_span (ι := ι) 𝓜
  obtain ⟨D, N, hDN⟩ := SectionMapInj.bound_finset (ι := ι) 𝓜 F hFH
  set L : ℕ := ∑ k, Fintype.card (ι k) with hL
  refine ⟨D + L * N + 1, fun c hc x hx hloc => ?_⟩
  have hxH : x ∈ SectionMapInj.killedSet (ι := ι) 𝓜 := by
    refine ⟨⟨c, hx⟩, ?_⟩
    have hch : ∀ ch : ∀ k, ι k, ∃ n : ℕ, SectionMapInj.chartMon S ch ^ n • x = 0 := by
      intro ch
      have h := hloc (SectionMapInj.chartCell ch)
      rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h
      obtain ⟨u, hu⟩ := h
      rw [one_smul, one_smul, smul_zero] at hu
      exact SectionMapInj.exists_pow_smul_eq_zero ch u.2 hu
    choose n hn using hch
    exact ⟨Finset.univ.sup n, fun ch =>
      SectionMapInj.pow_smul_eq_zero_of_le (hn ch) (Finset.le_sup (Finset.mem_univ ch))⟩
  obtain ⟨g, -, hg⟩ := Submodule.mem_span_finset.mp (hspan x hxH)
  have hV : x ∈ ⨆ (e : K → ℤ) (_ : e ≠ c), 𝓜 e := by
    rw [← hg]
    refine Submodule.sum_mem _ fun f hf => ?_
    obtain ⟨d, hfd, hdD, hfN⟩ := hDN f hf
    rw [MvPolynomial.as_sum (g f), Finset.sum_smul]
    refine Submodule.sum_mem _ fun μ _ => ?_
    set a : K → ℕ := fun k => ∑ i, μ ⟨k, i⟩ with ha
    have hhom : IsMultiHomog (monomial μ (coeff μ (g f)) : MRingOver S ι) a := fun m hm k => by
      rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
    have hmem := hM.2 a d _ f hhom hfd
    by_cases he : (d + fun k => (a k : ℤ)) = c
    · have hdeg : ∀ k, Fintype.card (ι k) * N + 1 ≤ ∑ i, μ ⟨k, i⟩ := by
        intro k
        have h1 := congrFun he k
        have h2 := hc k
        have h3 := hdD k
        have h4 : Fintype.card (ι k) ≤ L :=
          Finset.single_le_sum (f := fun k => Fintype.card (ι k)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        have h5 : ((Fintype.card (ι k) * N : ℕ) : ℤ) ≤ ((L * N : ℕ) : ℤ) := by
          exact_mod_cast Nat.mul_le_mul_right _ h4
        simp only [Pi.add_apply] at h1
        push_cast at h5
        have h6 : ((Fintype.card (ι k) * N + 1 : ℕ) : ℤ) ≤ (a k : ℤ) := by push_cast; linarith
        exact_mod_cast h6
      obtain ⟨ch, q, hq⟩ := SectionMapInj.exists_chart_dvd (S := S) N μ (coeff μ (g f)) hdeg
      rw [hq, mul_comm, mul_smul, hfN ch, smul_zero]
      exact Submodule.zero_mem _
    · exact (le_iSup₂ (f := fun (e : K → ℤ) (_ : e ≠ c) => 𝓜 e) _ he) hmem
  exact Submodule.disjoint_def.mp (hM.1.submodule_iSupIndep c) x hx hV

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

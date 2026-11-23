import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgFiltSt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

namespace KHPrimeFilt

section Weight

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] (ι : K → Type)
  [∀ k, Fintype (ι k)]

def blockWeight : (Σ k, ι k) → Lex (K → ℕ) := fun p => toLex (Pi.single p.1 1)

variable {ι}

theorem ofLex_weight (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    ofLex (Finsupp.weight (blockWeight ι) d) k = ∑ i, d ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intros; simp)]
  change (∑ p : (Σ k, ι k), d p • (Pi.single p.1 1 : K → ℕ)) k = _
  rw [Finset.sum_apply, Fintype.sum_sigma]
  simp [Pi.single_apply]

theorem isMultiHomog_of_isWeightedHomogeneous {f : MRingOver S ι} {b : Lex (K → ℕ)}
    (h : IsWeightedHomogeneous (blockWeight ι) f b) : IsMultiHomog f (ofLex b) := by
  intro d hd k
  rw [← ofLex_weight, h (mem_support_iff.mp hd)]

end Weight

section Module

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} [DirectSum.Decomposition 𝓜]

def shift (e : K → ℤ) (b : Lex (K → ℕ)) : K → ℤ := e + fun k => (ofLex b k : ℤ)

theorem shift_injective (e : K → ℤ) : Function.Injective (shift e) := by
  intro a b h
  apply ofLex.injective
  funext k
  have := congrFun h k
  simp only [shift, Pi.add_apply, add_right_inj, Nat.cast_inj] at this
  exact this

abbrev colon (A : Submodule (MRingOver S ι) M) (g : M) : Ideal (MRingOver S ι) :=
  A.comap (LinearMap.toSpanSingleton (MRingOver S ι) M g)

theorem mem_colon {A : Submodule (MRingOver S ι) M} {g : M} {p : MRingOver S ι} :
    p ∈ colon A g ↔ p • g ∈ A := by
  simp [colon]

variable (𝓜) in

def IsGradedSub (A : Submodule (MRingOver S ι) M) : Prop :=
  ∀ m ∈ A, ∀ c, (DirectSum.decompose 𝓜 m c : M) ∈ A

theorem decompose_smul (hgr : IsMGraded S ι 𝓜) {g : M} {e : K → ℤ} (hg : g ∈ 𝓜 e)
    (r : MRingOver S ι) (b : Lex (K → ℕ)) :
    (DirectSum.decompose 𝓜 (r • g) (shift e b) : M) =
      weightedHomogeneousComponent (blockWeight ι) b r • g := by
  classical
  conv_lhs => rw [← r.support_sum_monomial_coeff]
  rw [Finset.sum_smul, DirectSum.decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum,
    weightedHomogeneousComponent_apply, Finset.sum_smul, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hm : monomial d (coeff d r) • g ∈ 𝓜 (shift e (Finsupp.weight (blockWeight ι) d)) :=
    hgr.2 _ e _ g (isMultiHomog_of_isWeightedHomogeneous
      (isWeightedHomogeneous_monomial _ _ _ rfl)) hg
  split_ifs with h
  · rw [← h]
    exact DirectSum.decompose_of_mem_same _ hm
  · exact DirectSum.decompose_of_mem_ne _ hm fun h' => h (shift_injective e h')

theorem decompose_smul_mem_span (hgr : IsMGraded S ι 𝓜) {g : M} {e : K → ℤ} (hg : g ∈ 𝓜 e)
    (r : MRingOver S ι) (c : K → ℤ) :
    (DirectSum.decompose 𝓜 (r • g) c : M) ∈ Submodule.span (MRingOver S ι) {g} := by
  classical
  rw [← r.support_sum_monomial_coeff]
  rw [Finset.sum_smul, DirectSum.decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  have hm : monomial d (coeff d r) • g ∈ 𝓜 (shift e (Finsupp.weight (blockWeight ι) d)) :=
    hgr.2 _ e _ g (isMultiHomog_of_isWeightedHomogeneous
      (isWeightedHomogeneous_monomial _ _ _ rfl)) hg
  by_cases h : shift e (Finsupp.weight (blockWeight ι) d) = c
  · subst h
    rw [DirectSum.decompose_of_mem_same _ hm]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g)
  · rw [DirectSum.decompose_of_mem_ne _ hm h]
    exact Submodule.zero_mem _

theorem isGradedSub_bot : IsGradedSub 𝓜 (⊥ : Submodule (MRingOver S ι) M) := by
  intro m hm c
  rw [(Submodule.mem_bot _).mp hm, DirectSum.decompose_zero]
  exact Submodule.zero_mem _

theorem isGradedSub_sup_span (hgr : IsMGraded S ι 𝓜) {A : Submodule (MRingOver S ι) M}
    (hA : IsGradedSub 𝓜 A) {g : M} {e : K → ℤ} (hg : g ∈ 𝓜 e) :
    IsGradedSub 𝓜 (A ⊔ Submodule.span (MRingOver S ι) {g}) := by
  intro m hm c
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hb
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (hA a ha c))
    (Submodule.mem_sup_right (decompose_smul_mem_span hgr hg r c))

theorem exists_homogeneous_notMem {A : Submodule (MRingOver S ι) M} (hne : A ≠ ⊤) :
    ∃ (g : M) (e : K → ℤ), g ∈ 𝓜 e ∧ g ∉ A := by
  classical
  by_contra! h
  apply hne
  rw [eq_top_iff]
  intro m _
  rw [← DirectSum.sum_support_decompose 𝓜 m]
  exact Submodule.sum_mem _ fun c _ => h _ c (SetLike.coe_mem _)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

abbrev lexDecEq : DecidableEq (Lex (K → ℕ)) := LinearOrder.toDecidableEq

attribute [local instance 2000] lexDecEq

theorem isMultiHomogIdeal_of_isHomogeneous {I : Ideal (MRingOver S ι)}
    (h : I.IsHomogeneous (weightedHomogeneousSubmodule S (blockWeight ι))) : IsMultiHomogIdeal I := by
  obtain ⟨T, hT⟩ := (Ideal.IsHomogeneous.iff_exists _ _).mp h
  refine ⟨(↑) '' T, ?_, hT⟩
  rintro f ⟨x, _, rfl⟩
  obtain ⟨b, hb⟩ := x.2
  exact ⟨ofLex b, isMultiHomog_of_isWeightedHomogeneous ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hb)⟩

theorem colon_isHomogeneous (hgr : IsMGraded S ι 𝓜) {A : Submodule (MRingOver S ι) M}
    (hA : IsGradedSub 𝓜 A) {g : M} {e : K → ℤ} (hg : g ∈ 𝓜 e) :
    (colon A g).IsHomogeneous (weightedHomogeneousSubmodule S (blockWeight ι)) := by
  intro b r hr
  change ((weightedDecomposition S (blockWeight ι)).decompose' r b : MRingOver S ι) ∈ _
  rw [weightedDecomposition.decompose'_apply, mem_colon, ← decompose_smul hgr hg]
  exact hA _ (mem_colon.mp hr) _

theorem exists_prime_colon [IsNoetherianRing S] (hgr : IsMGraded S ι 𝓜)
    {A : Submodule (MRingOver S ι) M} (hA : IsGradedSub 𝓜 A) (hne : A ≠ ⊤) :
    ∃ ge : M × (K → ℤ), ge.1 ∈ 𝓜 ge.2 ∧ (colon A ge.1).IsPrime ∧
      (colon A ge.1).IsHomogeneous (weightedHomogeneousSubmodule S (blockWeight ι)) := by
  obtain ⟨g0, e0, hg0, hg0A⟩ := exists_homogeneous_notMem (𝓜 := 𝓜) hne
  obtain ⟨I, ⟨g, e, hg, hgA, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr
      (inferInstance : IsNoetherian (MRingOver S ι) (MRingOver S ι))
      {I | ∃ (g : M) (e : K → ℤ), g ∈ 𝓜 e ∧ g ∉ A ∧ I = colon A g} ⟨_, g0, e0, hg0, hg0A, rfl⟩
  have hhom := colon_isHomogeneous hgr hA hg
  refine ⟨(g, e), hg, ?_, hhom⟩
  refine hhom.isPrime_of_homogeneous_mem_or_mem ?_ ?_
  · intro htop
    apply hgA
    have h1 : (1 : MRingOver S ι) ∈ colon A g := htop ▸ Submodule.mem_top
    simpa [mem_colon] using h1
  · rintro a b ⟨i, ha⟩ ⟨j, hb⟩ hab
    by_contra! hn
    obtain ⟨ha', hb'⟩ := hn
    have hag : a • g ∈ 𝓜 (shift e i) :=
      hgr.2 _ e a g (isMultiHomog_of_isWeightedHomogeneous
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mp ha)) hg
    have hagA : a • g ∉ A := fun h => ha' (mem_colon.mpr h)
    have hle : colon A g ≤ colon A (a • g) := fun p hp => by
      rw [mem_colon] at hp ⊢
      rw [smul_comm]
      exact A.smul_mem a hp
    have heq : colon A g = colon A (a • g) := by
      by_contra hne'
      exact hmax _ ⟨_, _, hag, hagA, rfl⟩ (lt_of_le_of_ne hle hne')
    apply hb'
    rw [heq, mem_colon, smul_smul, mul_comm]
    exact mem_colon.mp hab

variable (ι 𝓜)

open Classical in

def next [IsNoetherianRing S] (A : Submodule (MRingOver S ι) M) : M × (K → ℤ) :=
  if h : IsMGraded S ι 𝓜 ∧ IsGradedSub 𝓜 A ∧ A ≠ ⊤ then
    Classical.choose (exists_prime_colon h.1 h.2.1 h.2.2) else (0, 0)

theorem next_mem [IsNoetherianRing S] (A : Submodule (MRingOver S ι) M) :
    (next ι 𝓜 A).1 ∈ 𝓜 (next ι 𝓜 A).2 := by
  unfold next
  split_ifs with h
  · exact (Classical.choose_spec (exists_prime_colon h.1 h.2.1 h.2.2)).1
  · exact Submodule.zero_mem _

variable {ι 𝓜} in
theorem next_spec [IsNoetherianRing S] (hgr : IsMGraded S ι 𝓜) {A : Submodule (MRingOver S ι) M}
    (hA : IsGradedSub 𝓜 A) (hne : A ≠ ⊤) :
    (colon A (next ι 𝓜 A).1).IsPrime ∧
      (colon A (next ι 𝓜 A).1).IsHomogeneous (weightedHomogeneousSubmodule S (blockWeight ι)) := by
  unfold next
  rw [dif_pos ⟨hgr, hA, hne⟩]
  exact (Classical.choose_spec (exists_prime_colon hgr hA hne)).2

def seq [IsNoetherianRing S] : ℕ → Submodule (MRingOver S ι) M
  | 0 => ⊥
  | j + 1 => seq j ⊔ Submodule.span (MRingOver S ι) {(next ι 𝓜 (seq j)).1}

def gen [IsNoetherianRing S] (j : ℕ) : M := (next ι 𝓜 (seq ι 𝓜 j)).1

variable {ι 𝓜}

theorem seq_isGradedSub [IsNoetherianRing S] (hgr : IsMGraded S ι 𝓜) (j : ℕ) :
    IsGradedSub 𝓜 (seq ι 𝓜 j) := by
  induction j with
  | zero => exact isGradedSub_bot
  | succ j ih => exact isGradedSub_sup_span hgr ih (next_mem ι 𝓜 _)

theorem seq_eq_span [IsNoetherianRing S] (n : ℕ) :
    seq ι 𝓜 n = Submodule.span (MRingOver S ι) (gen ι 𝓜 '' {l | l < n}) := by
  induction n with
  | zero => simp [seq]
  | succ n ih =>
    have hs : {l : ℕ | l < n + 1} = insert n {l | l < n} := by
      ext l
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
      omega
    show seq ι 𝓜 n ⊔ Submodule.span _ {gen ι 𝓜 n} = _
    rw [hs, Set.image_insert_eq, Submodule.span_insert, sup_comm, ← ih]

theorem exists_seq_eq_top [IsNoetherianRing S] [Module.Finite (MRingOver S ι) M]
    (hgr : IsMGraded S ι 𝓜) : ∃ n, seq ι 𝓜 n = ⊤ := by
  have hmono : Monotone (seq ι 𝓜) := monotone_nat_of_le_succ fun k => le_sup_left
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian (MRingOver S ι) M) ⟨seq ι 𝓜, hmono⟩
  refine ⟨n, by_contra fun hne => ?_⟩
  have hp := (next_spec hgr (seq_isGradedSub hgr n) hne).1
  apply hp.ne_top
  rw [Ideal.eq_top_iff_one, mem_colon, one_smul]
  have h1 : (next ι 𝓜 (seq ι 𝓜 n)).1 ∈ seq ι 𝓜 (n + 1) :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have h2 : seq ι 𝓜 n = seq ι 𝓜 (n + 1) := hn (n + 1) (Nat.le_succ n)
  rwa [← h2] at h1

end Module

theorem image_fin_lt {M : Type} {r : ℕ} (f : ℕ → M) (j : Fin r) :
    (fun l : Fin r => f l) '' {l | l < j} = f '' {l : ℕ | l < j} := by
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, Fin.lt_def.mp hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, lt_trans hl j.2⟩, Fin.lt_def.mpr hl, rfl⟩

theorem range_fin {M : Type} {r : ℕ} (f : ℕ → M) :
    Set.range (fun l : Fin r => f l) = f '' {l : ℕ | l < r} := by
  ext x
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l, l.2, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩

end KHPrimeFilt

open KHPrimeFilt in

theorem KHPrimeFilt.full : PrimeFiltStatement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 hS hfin hgr
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ := hgr.1.chooseDecomposition
  have hex : ∃ n, seq ι 𝓜 n = ⊤ := exists_seq_eq_top hgr
  classical
  refine ⟨Nat.find hex, fun j => gen ι 𝓜 j, fun j => (next ι 𝓜 (seq ι 𝓜 j)).2,
    fun j => colon (seq ι 𝓜 j) (gen ι 𝓜 j), ?_⟩
  unfold IsPrimeFilt
  refine ⟨fun j => next_mem ι 𝓜 _, fun j => ?_, fun j p => ?_, ?_⟩
  · have hne : seq ι 𝓜 j ≠ ⊤ := Nat.find_min hex j.2
    obtain ⟨hp, hh⟩ := next_spec hgr (seq_isGradedSub hgr j) hne
    refine ⟨hp, isMultiHomogIdeal_of_isHomogeneous hh, fun p hp' => ?_⟩
    rw [mem_colon, Module.mem_annihilator.mp hp']
    exact Submodule.zero_mem _
  · rw [image_fin_lt, ← seq_eq_span]
    exact mem_colon.symm
  · rw [range_fin, ← seq_eq_span]
    exact Nat.find_spec hex

end GroundTheory.Heights₂.Heights.Kleiman

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Length

variable {R : Type*} [CommRing R] {L : Type*} [AddCommGroup L] [Module R L]

abbrev colonIdeal (A : Submodule R L) (y : L) : Ideal R :=
  A.comap (LinearMap.toSpanSingleton R L y)

theorem mem_colonIdeal {A : Submodule R L} {y : L} {r : R} : r ∈ colonIdeal A y ↔ r • y ∈ A := by
  simp [colonIdeal]

theorem length_sup_span_singleton (A : Submodule R L) (y : L) :
    Module.length R (A ⊔ Submodule.span R {y} : Submodule R L) =
      Module.length R A + Module.length R (R ⧸ colonIdeal A y) := by
  set B : Submodule R L := A ⊔ Submodule.span R {y}
  let A' : Submodule R B := A.comap B.subtype
  have e1 : Module.length R B = Module.length R A' + Module.length R (B ⧸ A') :=
    Module.length_eq_add_of_exact A'.subtype A'.mkQ A'.injective_subtype A'.mkQ_surjective
      (LinearMap.exact_subtype_mkQ A')
  let yB : B := ⟨y, Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)⟩
  let φ : R →ₗ[R] B ⧸ A' := A'.mkQ ∘ₗ LinearMap.toSpanSingleton R B yB
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨⟨m, hm⟩, rfl⟩ := A'.mkQ_surjective z
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hb
    refine ⟨r, ?_⟩
    simp only [φ, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    change (r • y - (a + r • y) : L) ∈ A
    simpa using A.neg_mem ha
  have hker : LinearMap.ker φ = colonIdeal A y := by
    ext r
    simp only [LinearMap.mem_ker, φ, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, mem_colonIdeal]
    rfl
  have e3 : (R ⧸ colonIdeal A y) ≃ₗ[R] B ⧸ A' :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hφ)
  rw [e1, (Submodule.comapSubtypeEquivOfLe (le_sup_left : A ≤ B)).length_eq, e3.length_eq]

end Length

namespace GradedPMod

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  (𝓜 : GradedPMod S N M) [DirectSum.Decomposition 𝓜.piece]

def IsGradedSub (A : Submodule (Poly S N) M) : Prop :=
  ∀ m ∈ A, ∀ c, (DirectSum.decompose 𝓜.piece m c : M) ∈ A

variable {𝓜}

theorem decompose_smul_eq {g : M} {e : ℤ} (hg : g ∈ 𝓜.piece e) (r : Poly S N) (c : ℤ) :
    (DirectSum.decompose 𝓜.piece (r • g) c : M) =
      ∑ i ∈ Finset.range (r.totalDegree + 1),
        if e + (i : ℤ) = c then homogeneousComponent i r • g else 0 := by
  conv_lhs => rw [← sum_homogeneousComponent r]
  rw [Finset.sum_smul, DirectSum.decompose_sum]
  rw [DFinsupp.finsetSum_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm := 𝓜.smul_mem i e _ g (homogeneousComponent_isHomogeneous i r) hg
  split_ifs with h
  · subst h; exact DirectSum.decompose_of_mem_same _ hm
  · exact DirectSum.decompose_of_mem_ne _ hm h

theorem decompose_smul_add {g : M} {e : ℤ} (hg : g ∈ 𝓜.piece e) (r : Poly S N) (d : ℕ) :
    (DirectSum.decompose 𝓜.piece (r • g) (e + d) : M) = homogeneousComponent d r • g := by
  rw [decompose_smul_eq hg]
  simp only [add_right_inj, Nat.cast_inj, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero d r (by omega), zero_smul]

theorem isGradedSub_bot : 𝓜.IsGradedSub ⊥ := by
  intro m hm c
  rw [(Submodule.mem_bot _).mp hm, DirectSum.decompose_zero]
  exact Submodule.zero_mem _

theorem isGradedSub_sup_span {A : Submodule (Poly S N) M} (hA : 𝓜.IsGradedSub A) {g : M} {e : ℤ}
    (hg : g ∈ 𝓜.piece e) : 𝓜.IsGradedSub (A ⊔ Submodule.span (Poly S N) {g}) := by
  intro m hm c
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hb
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, decompose_smul_eq hg]
  refine Submodule.add_mem _ (Submodule.mem_sup_left (hA a ha c)) (Submodule.sum_mem _ fun i _ => ?_)
  split_ifs
  · exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g))
  · exact Submodule.zero_mem _

theorem homogeneousComponent_mem_colonIdeal {A : Submodule (Poly S N) M} (hA : 𝓜.IsGradedSub A)
    {g : M} {e : ℤ} (hg : g ∈ 𝓜.piece e) {r : Poly S N} (hr : r ∈ colonIdeal A g) (d : ℕ) :
    homogeneousComponent d r ∈ colonIdeal A g := by
  rw [mem_colonIdeal, ← decompose_smul_add hg]
  exact hA _ (mem_colonIdeal.mp hr) _

theorem exists_homogeneous_notMem {A : Submodule (Poly S N) M} (hne : A ≠ ⊤) :
    ∃ (g : M) (e : ℤ), g ∈ 𝓜.piece e ∧ g ∉ A := by
  classical
  by_contra! h
  apply hne
  rw [eq_top_iff]
  intro m _
  rw [← DirectSum.sum_support_decompose 𝓜.piece m]
  exact Submodule.sum_mem _ fun c _ => h _ c (SetLike.coe_mem _)

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem exists_isPrime_colonIdeal [IsNoetherianRing S] {A : Submodule (Poly S N) M}
    (hA : 𝓜.IsGradedSub A) (hne : A ≠ ⊤) :
    ∃ ge : M × ℤ, ge.1 ∈ 𝓜.piece ge.2 ∧ (colonIdeal A ge.1).IsPrime ∧
      ∀ p ∈ colonIdeal A ge.1, ∀ d : ℕ, homogeneousComponent d p ∈ colonIdeal A ge.1 := by
  obtain ⟨g0, e0, hg0, hg0A⟩ := exists_homogeneous_notMem (𝓜 := 𝓜) hne
  obtain ⟨I, ⟨g, e, hg, hgA, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian (Poly S N) (Poly S N))
      {I | ∃ (g : M) (e : ℤ), g ∈ 𝓜.piece e ∧ g ∉ A ∧ I = colonIdeal A g}
      ⟨_, g0, e0, hg0, hg0A, rfl⟩
  refine ⟨(g, e), hg, ?_, fun p hp d => homogeneousComponent_mem_colonIdeal hA hg hp d⟩
  refine Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem
    (𝒜 := homogeneousSubmodule (Fin (N + 1)) S) ?_ ?_ ?_
  · intro i r hr
    change (decomposition.decompose' r i : Poly S N) ∈ _
    rw [decomposition.decompose'_apply]
    exact homogeneousComponent_mem_colonIdeal hA hg hr i
  · intro htop
    apply hgA
    have h1 : (1 : Poly S N) ∈ colonIdeal A g := htop ▸ Submodule.mem_top
    simpa [mem_colonIdeal] using h1
  · rintro a b ⟨i, ha⟩ ⟨j, hb⟩ hab
    by_contra! hn
    obtain ⟨ha', hb'⟩ := hn
    have hag : a • g ∈ 𝓜.piece (e + i) :=
      𝓜.smul_mem i e a g ((mem_homogeneousSubmodule _ _).mp ha) hg
    have hagA : a • g ∉ A := fun h => ha' (mem_colonIdeal.mpr h)
    have hle : colonIdeal A g ≤ colonIdeal A (a • g) := fun p hp => by
      rw [mem_colonIdeal] at hp ⊢
      rw [smul_comm]
      exact A.smul_mem a hp
    have heq : colonIdeal A g = colonIdeal A (a • g) := by
      by_contra hne'
      exact hmax _ ⟨_, _, hag, hagA, rfl⟩ (lt_of_le_of_ne hle hne')
    apply hb'
    rw [heq, mem_colonIdeal, smul_smul, mul_comm]
    exact mem_colonIdeal.mp hab

variable (𝓜)

open Classical in

def primeFiltNext [IsNoetherianRing S] (A : Submodule (Poly S N) M) : M × ℤ :=
  if h : 𝓜.IsGradedSub A ∧ A ≠ ⊤ then Classical.choose (exists_isPrime_colonIdeal h.1 h.2) else (0, 0)

theorem primeFiltNext_mem [IsNoetherianRing S] (A : Submodule (Poly S N) M) :
    (𝓜.primeFiltNext A).1 ∈ 𝓜.piece (𝓜.primeFiltNext A).2 := by
  unfold primeFiltNext
  split_ifs with h
  · exact (Classical.choose_spec (exists_isPrime_colonIdeal h.1 h.2)).1
  · exact Submodule.zero_mem _

theorem primeFiltNext_spec [IsNoetherianRing S] {A : Submodule (Poly S N) M}
    (hA : 𝓜.IsGradedSub A) (hne : A ≠ ⊤) :
    (colonIdeal A (𝓜.primeFiltNext A).1).IsPrime ∧
      ∀ p ∈ colonIdeal A (𝓜.primeFiltNext A).1, ∀ d : ℕ,
        homogeneousComponent d p ∈ colonIdeal A (𝓜.primeFiltNext A).1 := by
  unfold primeFiltNext
  rw [dif_pos ⟨hA, hne⟩]
  exact (Classical.choose_spec (exists_isPrime_colonIdeal hA hne)).2

def primeFiltSeq [IsNoetherianRing S] : ℕ → Submodule (Poly S N) M
  | 0 => ⊥
  | k + 1 => primeFiltSeq k ⊔ Submodule.span (Poly S N) {(𝓜.primeFiltNext (primeFiltSeq k)).1}

theorem primeFiltSeq_isGradedSub [IsNoetherianRing S] (k : ℕ) :
    𝓜.IsGradedSub (𝓜.primeFiltSeq k) := by
  induction k with
  | zero => exact isGradedSub_bot
  | succ k ih => exact isGradedSub_sup_span ih (𝓜.primeFiltNext_mem _)

theorem exists_primeFiltSeq_eq_top [IsNoetherianRing S] [Module.Finite (Poly S N) M] :
    ∃ n, 𝓜.primeFiltSeq n = ⊤ := by
  have hmono : Monotone 𝓜.primeFiltSeq := monotone_nat_of_le_succ fun k => le_sup_left
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian (Poly S N) M) ⟨𝓜.primeFiltSeq, hmono⟩
  refine ⟨n, by_contra fun hne => ?_⟩
  have hp := (𝓜.primeFiltNext_spec (𝓜.primeFiltSeq_isGradedSub n) hne).1
  apply hp.ne_top
  rw [Ideal.eq_top_iff_one, mem_colonIdeal, one_smul]
  have h1 : (𝓜.primeFiltNext (𝓜.primeFiltSeq n)).1 ∈ 𝓜.primeFiltSeq (n + 1) :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have h2 : 𝓜.primeFiltSeq n = 𝓜.primeFiltSeq (n + 1) := hn (n + 1) (Nat.le_succ n)
  rwa [← h2] at h1

open Classical in

def primeFilt [IsNoetherianRing S] [Module.Finite (Poly S N) M] : PrimeFilt 𝓜 where
  n := Nat.find 𝓜.exists_primeFiltSeq_eq_top
  step i := 𝓜.primeFiltSeq i
  gen k := (𝓜.primeFiltNext (𝓜.primeFiltSeq k)).1
  deg k := (𝓜.primeFiltNext (𝓜.primeFiltSeq k)).2
  prime k := colonIdeal (𝓜.primeFiltSeq k) (𝓜.primeFiltNext (𝓜.primeFiltSeq k)).1
  step_zero := rfl
  step_last := Nat.find_spec 𝓜.exists_primeFiltSeq_eq_top
  step_succ k := rfl
  gen_mem k := 𝓜.primeFiltNext_mem _
  mem_prime k p := mem_colonIdeal
  isPrime k := (𝓜.primeFiltNext_spec (𝓜.primeFiltSeq_isGradedSub k)
    (Nat.find_min 𝓜.exists_primeFiltSeq_eq_top k.2)).1
  isHomogeneous k := (𝓜.primeFiltNext_spec (𝓜.primeFiltSeq_isGradedSub k)
    (Nat.find_min 𝓜.exists_primeFiltSeq_eq_top k.2)).2
  ann_le k p hp := by
    rw [mem_colonIdeal, (Module.mem_annihilator.mp hp)]
    exact Submodule.zero_mem _

end GradedPMod

namespace PrimeFilt

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  {𝓜 : GradedPMod S N M}

theorem card_prime_eq_length (F : PrimeFilt 𝓜) (pp : Ideal (Poly S N)) [pp.IsPrime]
    (hpp : pp ∈ (Module.annihilator (Poly S N) M).minimalPrimes) :
    (((Finset.univ.filter fun k => F.prime k = pp).card : ℕ) : ℕ∞) =
      Module.length (Localization.AtPrime pp) (LocalizedModule pp.primeCompl M) := by
  classical
  let R := Localization.AtPrime pp
  let f := LocalizedModule.mkLinearMap pp.primeCompl M
  let Loc : Submodule (Poly S N) M → Submodule R (LocalizedModule pp.primeCompl M) :=
    fun A => A.localized' R pp.primeCompl f
  have hstep : ∀ k : Fin F.n, Module.length R (Loc (F.step k.succ)) =
      Module.length R (Loc (F.step k.castSucc)) + if F.prime k = pp then 1 else 0 := by
    intro k
    have hsup : Loc (F.step k.succ) =
        Loc (F.step k.castSucc) ⊔ Submodule.span R {f (F.gen k)} := by
      simp only [Loc]
      rw [F.step_succ k, (Submodule.localized'gi R pp.primeCompl f).gc.l_sup,
        Submodule.localized'_span, Set.image_singleton]
    rw [hsup, length_sup_span_singleton]
    congr 1
    have hmemloc : ∀ r : Poly S N, r • F.gen k ∈ F.step k.castSucc →
        algebraMap (Poly S N) R r ∈ colonIdeal (Loc (F.step k.castSucc)) (f (F.gen k)) := by
      intro r hr
      rw [mem_colonIdeal, algebraMap_smul, ← LinearMap.map_smul]
      exact ⟨r • F.gen k, hr, 1, IsLocalizedModule.mk'_one _ _ _⟩
    split_ifs with h
    · have hI : colonIdeal (Loc (F.step k.castSucc)) (f (F.gen k)) = IsLocalRing.maximalIdeal R := by
        apply le_antisymm
        · apply IsLocalRing.le_maximalIdeal
          intro htop
          have h1 : (1 : R) ∈ colonIdeal (Loc (F.step k.castSucc)) (f (F.gen k)) :=
            htop ▸ Submodule.mem_top
          rw [mem_colonIdeal, one_smul] at h1
          obtain ⟨m, hm, s, hms⟩ := h1
          rw [IsLocalizedModule.mk'_eq_iff, ← LinearMap.map_smul_of_tower] at hms
          obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := pp.primeCompl) hms
          have hcs : ((c : Poly S N) * s) ∈ F.prime k := by
            rw [F.mem_prime, mul_smul]
            change (c : Poly S N) • ((s : Poly S N) • F.gen k) ∈ _
            rw [← Submonoid.smul_def s, ← Submonoid.smul_def c, ← hc, Submonoid.smul_def]
            exact Submodule.smul_mem _ _ hm
          rw [h] at hcs
          exact (pp.primeCompl.mul_mem c.2 s.2) hcs
        · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
          intro r hr
          exact hmemloc r ((F.mem_prime k r).mp (h ▸ hr))
      rw [hI]
      have : IsSimpleModule R (R ⧸ IsLocalRing.maximalIdeal R) :=
        isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal R))
      exact Module.length_eq_one _ _
    · have hnle : ¬ F.prime k ≤ pp := fun hle =>
        h (le_antisymm hle (hpp.2 ⟨F.isPrime k, F.ann_le k⟩ hle))
      obtain ⟨t, ht, htp⟩ := Set.not_subset.mp hnle
      have hI : colonIdeal (Loc (F.step k.castSucc)) (f (F.gen k)) = ⊤ :=
        Ideal.eq_top_of_isUnit_mem _ (hmemloc t ((F.mem_prime k t).mp ht))
          (IsLocalization.map_units R (⟨t, htp⟩ : pp.primeCompl))
      rw [hI]
      exact Module.length_eq_zero_iff.mpr (Submodule.Quotient.subsingleton_iff.mpr rfl)
  have key : ∀ j (hj : j ≤ F.n), Module.length R (Loc (F.step ⟨j, by omega⟩)) =
      ∑ i ∈ Finset.range j, (if h : i < F.n then (if F.prime ⟨i, h⟩ = pp then 1 else 0) else 0 : ℕ∞) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [Finset.sum_range_zero, show (⟨0, by omega⟩ : Fin (F.n + 1)) = 0 from rfl, F.step_zero]
      change Module.length R (Submodule.localized' R pp.primeCompl f ⊥) = 0
      rw [Submodule.localized'_bot]
      exact Module.length_bot
    | succ j ih =>
      intro hj
      rw [Finset.sum_range_succ, ← ih (by omega), dif_pos (by omega)]
      exact hstep ⟨j, by omega⟩
  calc (((Finset.univ.filter fun k => F.prime k = pp).card : ℕ) : ℕ∞)
      = ∑ k : Fin F.n, (if F.prime k = pp then 1 else 0 : ℕ∞) := by
        rw [Finset.card_filter]; push_cast; rfl
    _ = ∑ i ∈ Finset.range F.n,
          (if h : i < F.n then (if F.prime ⟨i, h⟩ = pp then 1 else 0) else 0 : ℕ∞) := by
        rw [← Fin.sum_univ_eq_sum_range]
        exact Finset.sum_congr rfl fun k _ => by rw [dif_pos k.isLt]
    _ = Module.length R (Loc (F.step ⟨F.n, by omega⟩)) := (key _ le_rfl).symm
    _ = Module.length R (LocalizedModule pp.primeCompl M) := by
        rw [show (⟨F.n, by omega⟩ : Fin (F.n + 1)) = Fin.last F.n from rfl, F.step_last]
        change Module.length R (Submodule.localized' R pp.primeCompl f ⊤) = _
        rw [Submodule.localized'_top]
        exact Module.length_top

end PrimeFilt

theorem PrimeFiltration.Exists.proof : PrimeFiltration.Exists.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x M _ _ _ _ 𝓜 _ _
  let _ := 𝓜.isInternal.chooseDecomposition
  exact ⟨⟨𝓜.primeFilt⟩, fun F pp _ hpp => F.card_prime_eq_length pp hpp⟩

end

end GroundTheory.Heights₂.Heights.Kleiman

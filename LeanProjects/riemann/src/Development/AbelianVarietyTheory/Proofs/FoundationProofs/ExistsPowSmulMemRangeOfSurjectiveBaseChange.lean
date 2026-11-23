import Mathlib

open Submodule TensorProduct

namespace GlobalTheory

namespace GenericFreeness

section Basic

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {X : Type*} [AddCommGroup X] [Module R X]

def IsBasisAway (a : R) (P Q : Submodule R M) (s : Set M) : Prop :=
  s ⊆ Q ∧ LinearIndepOn R P.mkQ s ∧ ∀ m ∈ Q, ∃ n : ℕ, a ^ n • m ∈ P ⊔ span R s

def HasBasisAway (a : R) (P Q : Submodule R M) : Prop :=
  ∃ s : Set M, IsBasisAway a P Q s

theorem HasBasisAway.of_dvd {a b : R} {P Q : Submodule R M} (h : HasBasisAway a P Q)
    (hab : a ∣ b) : HasBasisAway b P Q := by
  obtain ⟨s, h1, h2, h3⟩ := h
  obtain ⟨c, rfl⟩ := hab
  refine ⟨s, h1, h2, fun m hm => ?_⟩
  obtain ⟨n, hn⟩ := h3 m hm
  refine ⟨n, ?_⟩
  rw [mul_comm, mul_pow, mul_smul]
  exact smul_mem _ _ hn

theorem isBasisAway_empty (a : R) (P : Submodule R M) : IsBasisAway a P P ∅ :=
  ⟨Set.empty_subset _, linearIndepOn_empty _ _, fun m hm =>
    ⟨0, by simpa using hm⟩⟩

theorem IsBasisAway.union {a : R} {P Q U : Submodule R M} {s t : Set M} (hPQ : P ≤ Q)
    (hQU : Q ≤ U) (hs : IsBasisAway a P Q s) (ht : IsBasisAway a Q U t) :
    IsBasisAway a P U (s ∪ t) := by
  obtain ⟨s1, s2, s3⟩ := hs
  obtain ⟨t1, t2, t3⟩ := ht
  have t2' : LinearIndepOn R (factor hPQ ∘ P.mkQ) t := t2
  refine ⟨Set.union_subset (s1.trans hQU) t1, ?_, fun m hm => ?_⟩
  · refine s2.union (LinearIndepOn.of_comp _ t2') ?_
    have hd : Disjoint (span R (Set.range fun x : t => P.mkQ x)) (LinearMap.ker (factor hPQ)) :=
      range_ker_disjoint (f := factor hPQ) t2'
    rw [← Set.image_eq_range] at hd
    refine (hd.mono_right ?_).symm
    rw [span_le]
    rintro _ ⟨x, hx, rfl⟩
    simpa using s1 hx
  · obtain ⟨n, hn⟩ := t3 m hm
    obtain ⟨q, hq, x, hx, e⟩ := mem_sup.1 hn
    obtain ⟨k, hk⟩ := s3 q hq
    refine ⟨k + n, ?_⟩
    rw [pow_add, mul_smul, ← e, smul_add, span_union, ← sup_assoc]
    exact add_mem_sup hk (smul_mem _ _ hx)

theorem HasBasisAway.trans {a : R} {P Q U : Submodule R M} (hPQ : P ≤ Q)
    (hQU : Q ≤ U) (hs : HasBasisAway a P Q) (ht : HasBasisAway a Q U) :
    HasBasisAway a P U := by
  obtain ⟨s, hs⟩ := hs
  obtain ⟨t, ht⟩ := ht
  exact ⟨_, hs.union hPQ hQU ht⟩

theorem HasBasisAway.iSup {a : R} (F : ℕ → Submodule R M) (hF : Monotone F)
    (h : ∀ d, HasBasisAway a (F d) (F (d + 1))) : HasBasisAway a (F 0) (⨆ d, F d) := by
  choose s hs using h
  let t : ℕ → Set M := fun d => Nat.rec ∅ (fun d t => t ∪ s d) d
  have ht : ∀ d, IsBasisAway a (F 0) (F d) (t d) := by
    intro d
    induction d with
    | zero => exact isBasisAway_empty a _
    | succ d ih => exact ih.union (hF (Nat.zero_le d)) (hF (Nat.le_succ d)) (hs d)
  have hmono : Monotone t := monotone_nat_of_le_succ fun d => Set.subset_union_left
  refine ⟨⋃ d, t d, Set.iUnion_subset fun d => (ht d).1.trans (le_iSup F d), ?_, fun m hm => ?_⟩
  · exact linearIndepOn_iUnion_of_directed hmono.directed_le fun d => (ht d).2.1
  · obtain ⟨d, hd⟩ := (mem_iSup_of_directed F hF.directed_le).1 hm
    obtain ⟨n, hn⟩ := (ht d).2.2 m hd
    exact ⟨n, (sup_le_sup_left (span_mono (Set.subset_iUnion t d)) (F 0) :) hn⟩

theorem HasBasisAway.map {a : R} (φ : X →ₗ[R] M) (P : Submodule R M)
    (h : HasBasisAway a (P.comap φ) ⊤) : HasBasisAway a P (P ⊔ LinearMap.range φ) := by
  obtain ⟨s, -, h2, h3⟩ := h
  refine ⟨φ '' s, ?_, ?_, fun m hm => ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact mem_sup_right ⟨x, rfl⟩
  · apply LinearIndepOn.image_of_comp
    have hinj : LinearMap.ker (mapQ (P.comap φ) P φ le_rfl) = ⊥ := by
      rw [mapQ, ker_liftQ_eq_bot]
      rw [LinearMap.ker_comp, ker_mkQ]
    exact LinearIndependent.map' h2 _ hinj
  · obtain ⟨p, hp, _, ⟨x, rfl⟩, rfl⟩ := mem_sup.1 hm
    obtain ⟨n, hn⟩ := h3 x trivial
    obtain ⟨q, hq, y, hy, e⟩ := mem_sup.1 hn
    refine ⟨n, ?_⟩
    rw [smul_add, ← map_smul, ← e, map_add, ← add_assoc]
    refine add_mem_sup (add_mem (smul_mem _ _ hp) hq) ?_
    rw [← map_span]
    exact mem_map_of_mem hy

theorem HasBasisAway.comap {a : R} (π : X →ₗ[R] M) (hπ : Function.Surjective π)
    (h : HasBasisAway a (⊥ : Submodule R M) ⊤) : HasBasisAway a (LinearMap.ker π) ⊤ := by
  obtain ⟨s, -, h2, h3⟩ := h
  obtain ⟨σ, hσ⟩ := hπ.hasRightInverse
  refine ⟨σ '' s, Set.subset_univ _, ?_, fun m _ => ?_⟩
  · apply LinearIndepOn.image_of_comp
    apply LinearIndepOn.of_comp (mapQ (LinearMap.ker π) ⊥ π le_rfl)
    have : (mapQ (LinearMap.ker π) ⊥ π le_rfl) ∘ (LinearMap.ker π).mkQ ∘ σ =
        (⊥ : Submodule R M).mkQ := by
      ext x
      change (⊥ : Submodule R M).mkQ (π (σ x)) = _
      rw [hσ x]
    rwa [this]
  · obtain ⟨n, hn⟩ := h3 (π m) trivial
    refine ⟨n, ?_⟩
    have : s = π '' (σ '' s) := by
      rw [Set.image_image]
      simp [hσ _]
    rw [bot_sup_eq, this, ← map_span, ← map_smul] at hn
    rw [sup_comm, ← comap_map_eq]
    exact hn

theorem HasBasisAway.quotient {a : R} {P : Submodule R M} (h : HasBasisAway a P ⊤) :
    HasBasisAway a (⊥ : Submodule R (M ⧸ P)) ⊤ := by
  have := HasBasisAway.map (a := a) P.mkQ ⊥ (by simpa using h)
  simpa using this

theorem IsBasisAway.linearIndepOn {a : R} {s : Set M}
    (h : IsBasisAway a (⊥ : Submodule R M) ⊤ s) : LinearIndepOn R id s :=
  LinearIndepOn.of_comp (⊥ : Submodule R M).mkQ h.2.1

theorem hasBasisAway_of_free [Module.Free R M] (a : R) :
    HasBasisAway a (⊥ : Submodule R M) ⊤ := by
  let b := Module.Free.chooseBasis R M
  refine ⟨Set.range b, Set.subset_univ _, ?_, fun m _ => ⟨0, by simp⟩⟩
  exact LinearIndependent.map' b.linearIndependent.linearIndepOn_id (⊥ : Submodule R M).mkQ
    (ker_mkQ _)

theorem IsBasisAway.exists_basis {a : R} {s : Set M}
    (h : IsBasisAway a (⊥ : Submodule R M) ⊤ s) (S : Submonoid R) (ha : a ∈ S)
    (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
    {Mₛ : Type*} [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f] :
    Nonempty (Module.Basis s Rₛ Mₛ) := by
  refine ⟨Module.Basis.mk (v := f ∘ fun x : s => (x : M))
    (LinearIndependent.of_isLocalizedModule Rₛ S f h.linearIndepOn) ?_⟩
  have key : ∀ (c : S) (y : Mₛ), (c : R) • y ∈ span Rₛ (Set.range (f ∘ fun x : s => (x : M))) →
      y ∈ span Rₛ (Set.range (f ∘ fun x : s => (x : M))) := by
    intro c y hy
    obtain ⟨u, hu⟩ := IsLocalization.map_units Rₛ c
    rw [← algebraMap_smul Rₛ, ← hu] at hy
    exact (smul_mem_iff_of_isUnit _ u.isUnit).1 hy
  intro y _
  obtain ⟨⟨m, c⟩, hm⟩ := IsLocalizedModule.surj S f y
  apply key c
  obtain ⟨n, hn⟩ := h.2.2 m trivial
  apply key ⟨a ^ n, pow_mem ha n⟩
  change a ^ n • (c • y) ∈ _
  rw [hm, ← map_smul]
  rw [bot_sup_eq] at hn
  have := mem_map_of_mem (f := f) hn
  rw [map_span] at this
  have h2 := span_subset_span R Rₛ _ this
  rwa [Set.range_comp, Subtype.range_coe]

theorem HasBasisAway.free_of_isLocalizedModule {a : R}
    (h : HasBasisAway a (⊥ : Submodule R M) ⊤) (S : Submonoid R) (ha : a ∈ S)
    (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
    {Mₛ : Type*} [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f] : Module.Free Rₛ Mₛ := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨b⟩ := hs.exists_basis S ha Rₛ f
  exact .of_basis b

theorem HasBasisAway.free_away {a : R} (h : HasBasisAway a (⊥ : Submodule R M) ⊤) :
    Module.Free (Localization.Away a) (LocalizedModule.Away a M) :=
  h.free_of_isLocalizedModule (.powers a) (Submonoid.mem_powers a) _
    (LocalizedModule.mkLinearMap _ M)

theorem HasBasisAway.free (h : HasBasisAway (1 : R) (⊥ : Submodule R M) ⊤) :
    Module.Free R M := by
  obtain ⟨s, hs⟩ := h
  refine .of_basis (Module.Basis.mk hs.linearIndepOn ?_)
  intro m _
  obtain ⟨n, hn⟩ := hs.2.2 m trivial
  simpa using hn

theorem exists_hasBasisAway_of_finite [IsDomain R] [Module.Finite R M] :
    ∃ a : R, a ≠ 0 ∧ HasBasisAway a (⊥ : Submodule R M) ⊤ := by
  obtain ⟨s, hs, hs'⟩ := exists_maximal_linearIndepOn R (id : M → M)
  have ht : Module.IsTorsion R (M ⧸ span R s) := by
    intro x
    obtain ⟨x, rfl⟩ := mkQ_surjective _ x
    by_cases hx : x ∈ s
    · exact ⟨1, by simpa using subset_span hx⟩
    · obtain ⟨c, hc, hcx⟩ := hs' x hx
      refine ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, ?_⟩
      change c • (span R s).mkQ x = 0
      rw [← map_smul, mkQ_apply, Quotient.mk_eq_zero]
      simpa using hcx
  obtain ⟨a, ha, ha0⟩ := annihilator_top_inter_nonZeroDivisors ht
  refine ⟨a, nonZeroDivisors.ne_zero ha0, s, Set.subset_univ _,
    LinearIndependent.map' hs (⊥ : Submodule R M).mkQ (ker_mkQ _), fun m _ => ⟨1, ?_⟩⟩
  have := mem_annihilator.1 ha ((span R s).mkQ m) trivial
  rw [← map_smul, mkQ_apply, Quotient.mk_eq_zero] at this
  simpa using this

end Basic

section Step

variable {R : Type*} [CommRing R] {T : Type*} [CommRing T] [Algebra R T]
  {M : Type*} [AddCommGroup M] [Module R M] [Module T M] [IsScalarTower R T M]

noncomputable def powerChain (t : Module.End T M) (N : Submodule T M) : ℕ → Submodule T M
  | 0 => N
  | d + 1 => powerChain t N d ⊔ N.map (t ^ (d + 1))

theorem powerChain_mono (t : Module.End T M) (N : Submodule T M) : Monotone (powerChain t N) :=
  monotone_nat_of_le_succ fun _ => le_sup_left

theorem map_powerChain_le (t : Module.End T M) (N : Submodule T M) (d : ℕ) :
    (powerChain t N d).map t ≤ powerChain t N (d + 1) := by
  induction d with
  | zero => simp [powerChain]
  | succ d ih =>
    conv_lhs => rw [powerChain, Submodule.map_sup, ← Submodule.map_comp, ← Module.End.mul_eq_comp,
      ← pow_succ']
    exact sup_le_sup_right ih _

theorem exists_hasBasisAway_powerChain [IsDomain R] (t : Module.End T M) (N : Submodule T M)
    [IsNoetherian T N]
    (H : ∀ K : Submodule T N, ∃ a : R, a ≠ 0 ∧ HasBasisAway a (⊥ : Submodule R (N ⧸ K)) ⊤) :
    ∃ a : R, a ≠ 0 ∧
      HasBasisAway a (N.restrictScalars R) (⨆ d, (powerChain t N d).restrictScalars R) := by
  let K : ℕ → Submodule T N := fun d => (powerChain t N d).comap ((t ^ (d + 1)) ∘ₗ N.subtype)
  have hK : Monotone K := monotone_nat_of_le_succ fun d x hx => by
    have := map_powerChain_le t N d (mem_map_of_mem hx)
    simpa [K, pow_succ' t (d + 1)] using this
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.2 inferInstance ⟨K, hK⟩
  choose a ha0 ha using H
  refine ⟨∏ i ∈ Finset.range (n + 1), a (K i), Finset.prod_ne_zero_iff.2 fun i _ => ha0 _, ?_⟩
  refine HasBasisAway.iSup (fun d => (powerChain t N d).restrictScalars R)
    (fun i j hij => powerChain_mono t N hij) fun d => ?_
  have hdvd : a (K d) ∣ ∏ i ∈ Finset.range (n + 1), a (K i) := by
    rcases le_total d n with h | h
    · exact Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (Nat.lt_succ_of_le h))
    · have : K n = K d := hn d h
      rw [← this]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (Nat.lt_succ_self n))
  have h1 := ((ha (K d)).of_dvd hdvd).comap ((K d).mkQ.restrictScalars R)
    (K d).mkQ_surjective
  have e1 : LinearMap.ker ((K d).mkQ.restrictScalars R) =
      ((powerChain t N d).restrictScalars R).comap
        (((t ^ (d + 1)) ∘ₗ N.subtype).restrictScalars R) := by
    ext x
    exact Quotient.mk_eq_zero (K d)
  rw [e1] at h1
  have h2 := HasBasisAway.map _ _ h1
  have e2 : LinearMap.range (((t ^ (d + 1)) ∘ₗ N.subtype).restrictScalars R) =
      (N.map (t ^ (d + 1))).restrictScalars R := by
    ext x
    exact ⟨by rintro ⟨y, rfl⟩; exact ⟨y, y.2, rfl⟩, by rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩⟩
  rw [e2, ← restrictScalars_sup] at h2
  exact h2

end Step

section Main

universe u v

variable (R : Type*) [CommRing R] [IsDomain R] (A : Type*) [CommRing A] [Algebra R A]

def QuotientsFreeAway (T : Type u) [CommRing T] [Algebra A T] : Prop :=
  ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module A M] [Module T M] [IsScalarTower R A M]
    [IsScalarTower A T M] [Module.Finite T M] (N : Submodule A M), N.FG →
    ∃ a : R, a ≠ 0 ∧ HasBasisAway a (N.restrictScalars R) ⊤

variable {R A}

theorem QuotientsFreeAway.step {B : Type*} {T : Type*} [CommRing B] [CommRing T] [Algebra A B]
    [Algebra A T] [Algebra B T] [IsScalarTower A B T] [IsNoetherianRing B] (t : T)
    (ht : Algebra.adjoin B {t} = ⊤) (H : QuotientsFreeAway.{_, v} R A B) :
    QuotientsFreeAway.{_, v} R A T := by
  intro M _ _ _ _ _ _ _ N hN
  letI : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A B := .of_algebraMap_eq' rfl
  letI : Module B M := Module.compHom M (algebraMap B T)
  haveI : IsScalarTower B T M := IsScalarTower.of_compHom B T M
  haveI : IsScalarTower A B M := .of_algebraMap_smul fun r x => by
    change algebraMap B T (algebraMap A B r) • x = _
    rw [← IsScalarTower.algebraMap_apply, algebraMap_smul]
  haveI : IsScalarTower R B M := .of_algebraMap_smul fun r x => by
    rw [IsScalarTower.algebraMap_apply R A B, algebraMap_smul, algebraMap_smul]
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := T) (M := M)
  obtain ⟨s', rfl⟩ := hN
  let M₀ : Submodule B M := span B (s ∪ s' : Set M)
  haveI : Module.Finite B M₀ :=
    Module.Finite.span_of_finite B (s.finite_toSet.union s'.finite_toSet)
  let τ : Module.End B M := (LinearMap.lsmul T M t).restrictScalars B
  obtain ⟨a, ha0, ha⟩ := exists_hasBasisAway_powerChain (R := R) τ M₀ fun K => by
    simpa using H (M₀ ⧸ K) ⊥ fg_bot
  have htop : (⨆ d, (powerChain τ M₀ d).restrictScalars R) = ⊤ := by
    have hdir := (powerChain_mono τ M₀).directed_le
    have key : ∀ (c : T), ∀ x ∈ ⨆ d, powerChain τ M₀ d, c • x ∈ ⨆ d, powerChain τ M₀ d := by
      intro c
      have hc : c ∈ Algebra.adjoin B {t} := ht ▸ Algebra.mem_top
      induction hc using Algebra.adjoin_induction with
      | mem y hy =>
        intro x hx
        obtain rfl : y = t := hy
        obtain ⟨d, hd⟩ := (mem_iSup_of_directed _ hdir).1 hx
        exact mem_iSup_of_mem (d + 1) (map_powerChain_le τ M₀ d (mem_map_of_mem hd))
      | algebraMap r => exact fun x hx => smul_mem _ r hx
      | add y z _ _ hy hz => exact fun x hx => add_smul y z x ▸ add_mem (hy x hx) (hz x hx)
      | mul y z _ _ hy hz => exact fun x hx => mul_smul y z x ▸ hy _ (hz x hx)
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ span T (s : Set M) := hs ▸ mem_top
    have : x ∈ ⨆ d, powerChain τ M₀ d := by
      induction hx using span_induction with
      | mem y hy => exact mem_iSup_of_mem 0 (subset_span (Or.inl hy))
      | zero => exact zero_mem _
      | add y z _ _ hy hz => exact add_mem (hy trivial) (hz trivial)
      | smul c y _ hy => exact key c y (hy trivial)
    obtain ⟨d, hd⟩ := (mem_iSup_of_directed _ hdir).1 this
    exact mem_iSup_of_mem d hd
  rw [htop] at ha
  have hle : span A (s' : Set M) ≤ M₀.restrictScalars A :=
    span_le.2 fun x hx => subset_span (Or.inr hx)
  obtain ⟨b, hb0, hb⟩ := H M₀ ((span A (s' : Set M)).comap (M₀.subtype.restrictScalars A)) (by
    apply fg_of_fg_map_injective (M₀.subtype.restrictScalars A) Subtype.val_injective
    rw [map_comap_eq_of_le]
    · exact ⟨s', rfl⟩
    · intro x hx
      exact ⟨⟨x, hle hx⟩, rfl⟩)
  have hb' := HasBasisAway.map (M₀.subtype.restrictScalars R)
    ((span A (s' : Set M)).restrictScalars R) hb
  have he : (span A (s' : Set M)).restrictScalars R ⊔
      LinearMap.range (M₀.subtype.restrictScalars R) = M₀.restrictScalars R := by
    apply le_antisymm
    · exact sup_le (fun x hx => hle hx) (by rintro _ ⟨x, rfl⟩; exact x.2)
    · exact fun x hx => mem_sup_right ⟨⟨x, hx⟩, rfl⟩
  rw [he] at hb'
  exact ⟨a * b, mul_ne_zero ha0 hb0, (hb'.of_dvd (dvd_mul_left b a)).trans (fun x hx => hle hx)
    le_top (ha.of_dvd (dvd_mul_right a b))⟩

theorem quotientsFreeAway_of_finiteType [IsNoetherianRing A]
    (H : ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
      [Module.Finite A M], ∃ a : R, a ≠ 0 ∧ HasBasisAway a (⊥ : Submodule R M) ⊤)
    (T : Type u) [CommRing T] [Algebra A T] [hT : Algebra.FiniteType A T] :
    QuotientsFreeAway.{_, v} R A T := by
  obtain ⟨n, f, hf⟩ : ∃ (n : ℕ) (f : Fin n → T), Algebra.adjoin A (Set.range f) = ⊤ := by
    obtain ⟨s, hs⟩ := hT.out
    refine ⟨s.card, fun i => s.equivFin.symm i, ?_⟩
    rw [← hs]
    congr 1
    ext x
    simp only [Set.mem_range, SetLike.mem_coe]
    exact ⟨by rintro ⟨i, rfl⟩; exact (s.equivFin.symm i).2,
      fun hx => ⟨s.equivFin ⟨x, hx⟩, by simp⟩⟩
  clear hT
  induction n generalizing T with
  | zero =>
    intro M _ _ _ _ _ _ _ N _
    have hsurj : Function.Surjective (algebraMap A T) := by
      intro y
      have : y ∈ Algebra.adjoin A (Set.range f) := hf ▸ Algebra.mem_top
      rw [Set.range_eq_empty, Algebra.adjoin_empty] at this
      exact Algebra.mem_bot.1 this
    haveI : Module.Finite A T := Module.Finite.of_surjective (Algebra.linearMap A T) hsurj
    haveI : Module.Finite A M := Module.Finite.trans T M
    obtain ⟨a, ha0, ha⟩ := H (M ⧸ N)
    refine ⟨a, ha0, ?_⟩
    have e1 : LinearMap.ker (N.mkQ.restrictScalars R) = N.restrictScalars R := by
      ext x
      exact Quotient.mk_eq_zero N
    exact e1 ▸ ha.comap (N.mkQ.restrictScalars R) N.mkQ_surjective
  | succ n ih =>
    let B := Algebra.adjoin A (Set.range (Fin.tail f))
    let g : Fin n → B := fun i => ⟨Fin.tail f i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
    have hg : Algebra.adjoin A (Set.range g) = ⊤ := by
      rw [← Algebra.adjoin_adjoin_coe_preimage (R := A) (s := Set.range (Fin.tail f))]
      congr 1
      ext x
      simp [g, Subtype.ext_iff]
    haveI : Algebra.FiniteType A B := ⟨⟨(Set.finite_range g).toFinset, by simpa using hg⟩⟩
    haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
    refine QuotientsFreeAway.step (B := B) (f 0) ?_ (ih B g hg)
    apply Subalgebra.restrictScalars_injective A
    rw [← Algebra.adjoin_union_eq_adjoin_adjoin, Subalgebra.restrictScalars_top, ← hf,
      Fin.range_fin_succ, Set.union_singleton]

theorem exists_hasBasisAway_of_finite_algebra [Module.Finite R A]
    (M : Type v) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Finite A M] : ∃ a : R, a ≠ 0 ∧ HasBasisAway a (⊥ : Submodule R M) ⊤ :=
  haveI : Module.Finite R M := Module.Finite.trans A M
  exists_hasBasisAway_of_finite

theorem exists_hasBasisAway_of_finiteType [IsNoetherianRing R] [Algebra.FiniteType R A]
    (M : Type v) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Finite A M] : ∃ a : R, a ≠ 0 ∧ HasBasisAway a (⊥ : Submodule R M) ⊤ := by
  simpa using quotientsFreeAway_of_finiteType (R := R) (A := R)
    exists_hasBasisAway_of_finite_algebra A M ⊥ fg_bot

end Main

section BaseChange

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem IsBasisAway.exists_basis_tensor {a : R} {s : Set M}
    (h : IsBasisAway a (⊥ : Submodule R M) ⊤ s) (R' : Type*) [CommRing R'] [Algebra R R']
    (ha : IsUnit (algebraMap R R' a)) : Nonempty (Module.Basis s R' (R' ⊗[R] M)) := by
  obtain ⟨b⟩ := h.exists_basis (.powers a) (Submonoid.mem_powers a) (Localization.Away a)
    (TensorProduct.mk R (Localization.Away a) M 1)
  letI : Algebra (Localization.Away a) R' := (IsLocalization.Away.lift a ha).toAlgebra
  haveI : IsScalarTower R (Localization.Away a) R' :=
    .of_algebraMap_eq fun r => (IsLocalization.Away.lift_eq a ha r).symm
  exact ⟨(b.baseChange R').map (AlgebraTensorModule.cancelBaseChange R _ R' R' M)⟩

theorem HasBasisAway.free_tensor {a : R} (h : HasBasisAway a (⊥ : Submodule R M) ⊤)
    (R' : Type*) [CommRing R'] [Algebra R R'] (ha : IsUnit (algebraMap R R' a)) :
    Module.Free R' (R' ⊗[R] M) := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨b⟩ := hs.exists_basis_tensor R' ha
  exact .of_basis b

theorem HasBasisAway.exists_pow_smul_eq_zero {a : R} (h : HasBasisAway a (⊥ : Submodule R M) ⊤)
    (R' : Type*) [CommRing R'] [Nontrivial R'] [Algebra R R'] (ha : IsUnit (algebraMap R R' a))
    [Subsingleton (R' ⊗[R] M)] (m : M) : ∃ n : ℕ, a ^ n • m = 0 := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨b⟩ := hs.exists_basis_tensor R' ha
  obtain rfl : s = ∅ := Set.eq_empty_of_forall_notMem fun x hx =>
    b.ne_zero ⟨x, hx⟩ (Subsingleton.elim _ _)
  simpa using hs.2.2 m trivial

end BaseChange

section Quotient

universe v

variable (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem exists_hasBasisAway_quotient (A₀ : Type*) [CommRing A₀] [Algebra R A₀]
    [Algebra.FiniteType R A₀] (A : Type*) [CommRing A] [Algebra A₀ A] [Algebra.FiniteType A₀ A]
    {M : Type v} [AddCommGroup M] [Module R M] [Module A₀ M] [Module A M] [IsScalarTower R A₀ M]
    [IsScalarTower A₀ A M] [Module.Finite A M] (N : Submodule A₀ M) (hN : N.FG) :
    ∃ a : R, a ≠ 0 ∧ HasBasisAway a (N.restrictScalars R) ⊤ :=
  haveI : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing R A₀
  quotientsFreeAway_of_finiteType (R := R) (A := A₀) exists_hasBasisAway_of_finiteType A M N hN

variable {R}

theorem exists_hasBasisAway_coker {A₀ : Type*} [CommRing A₀] [Algebra R A₀]
    [Algebra.FiniteType R A₀] {A : Type*} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (φ : A₀ →ₐ[R] A) :
    ∃ a : R, a ≠ 0 ∧
      HasBasisAway a (⊥ : Submodule R (A ⧸ LinearMap.range φ.toLinearMap)) ⊤ := by
  letI : Algebra A₀ A := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R A₀ A := .of_algebraMap_eq fun r => (φ.commutes r).symm
  haveI : Algebra.FiniteType A₀ A := .of_restrictScalars_finiteType R A₀ A
  obtain ⟨a, ha0, ha⟩ := exists_hasBasisAway_quotient R A₀ A (span A₀ {(1 : A)})
    (fg_span_singleton _)
  have e : (span A₀ {(1 : A)}).restrictScalars R = LinearMap.range φ.toLinearMap := by
    ext x
    simp only [restrictScalars_mem, mem_span_singleton, Algebra.smul_def, mul_one]
    rfl
  rw [e] at ha
  exact ⟨a, ha0, ha.quotient⟩

end Quotient

end GenericFreeness

open GenericFreeness

section Chain

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem free_quotient_of_chain (F : ℕ → Submodule R M) (hF : Monotone F) (htop : ⨆ d, F d = ⊤)
    (h : ∀ d, Module.Free R (F (d + 1) ⧸ (F d).submoduleOf (F (d + 1)))) :
    Module.Free R (M ⧸ F 0) := by
  have := HasBasisAway.iSup (a := 1) F hF fun d => by
    have h1 := (hasBasisAway_of_free (M := F (d + 1) ⧸ (F d).submoduleOf (F (d + 1))) 1).comap
      ((F d).submoduleOf (F (d + 1))).mkQ (mkQ_surjective _)
    rw [ker_mkQ] at h1
    have h2 := HasBasisAway.map (F (d + 1)).subtype (F d) h1
    rwa [range_subtype, sup_eq_right.2 (hF (Nat.le_succ d))] at h2
  rw [htop] at this
  exact this.quotient.free

theorem free_of_chain (F : ℕ → Submodule R M) (hF : Monotone F) (htop : ⨆ d, F d = ⊤)
    (h0 : Module.Free R (F 0))
    (h : ∀ d, Module.Free R (F (d + 1) ⧸ (F d).submoduleOf (F (d + 1)))) :
    Module.Free R M := by
  haveI := free_quotient_of_chain F hF htop h
  have h1 := (hasBasisAway_of_free (M := M ⧸ F 0) (1 : R)).comap (F 0).mkQ (mkQ_surjective _)
  rw [ker_mkQ] at h1
  have h2 := HasBasisAway.map (a := 1) (F 0).subtype ⊥ (by
    rw [comap_bot, ker_subtype]
    exact hasBasisAway_of_free 1)
  rw [range_subtype, bot_sup_eq] at h2
  exact (h2.trans bot_le le_top h1).free

end Chain

section Statements

variable (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem exists_forall_dvd_free_away (S : Type*) [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (M : Type*) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M] :
    ∃ a : R, a ≠ 0 ∧
      ∀ b, a ∣ b → Module.Free (Localization.Away b) (LocalizedModule.Away b M) := by
  obtain ⟨a, ha0, ha⟩ := exists_hasBasisAway_of_finiteType (R := R) (A := S) M
  exact ⟨a, ha0, fun b hb => (ha.of_dvd hb).free_away⟩

theorem exists_free_away (S : Type*) [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (M : Type*) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M] :
    ∃ a : R, a ≠ 0 ∧ Module.Free (Localization.Away a) (LocalizedModule.Away a M) := by
  obtain ⟨a, ha0, ha⟩ := exists_forall_dvd_free_away R S M
  exact ⟨a, ha0, ha a dvd_rfl⟩

theorem exists_free_tensor_of_isUnit.{w} (S : Type*) [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (M : Type*) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M] :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type w) [CommRing R'] [Algebra R R'],
      IsUnit (algebraMap R R' a) → Module.Free R' (R' ⊗[R] M) := by
  obtain ⟨a, ha0, ha⟩ := exists_hasBasisAway_of_finiteType (R := R) (A := S) M
  exact ⟨a, ha0, fun R' _ _ h => ha.free_tensor R' h⟩

theorem exists_free_localization_away (S : Type*) [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] :
    ∃ a : R, a ≠ 0 ∧ Module.Free (Localization.Away a)
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a))) := by
  obtain ⟨a, ha0, ha⟩ := exists_hasBasisAway_of_finiteType (R := R) (A := S) S
  exact ⟨a, ha0, ha.free_of_isLocalizedModule (.powers a) (Submonoid.mem_powers a) _
    (IsScalarTower.toAlgHom R S
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)))).toLinearMap⟩

theorem exists_free_away_quotient (A₀ : Type*) [CommRing A₀] [Algebra R A₀]
    [Algebra.FiniteType R A₀] (A : Type*) [CommRing A] [Algebra A₀ A] [Algebra.FiniteType A₀ A]
    {M : Type*} [AddCommGroup M] [Module R M] [Module A₀ M] [Module A M] [IsScalarTower R A₀ M]
    [IsScalarTower A₀ A M] [Module.Finite A M] (N : Submodule A₀ M) (hN : N.FG) :
    ∃ a : R, a ≠ 0 ∧ ∀ b, a ∣ b →
      Module.Free (Localization.Away b) (LocalizedModule.Away b (M ⧸ N.restrictScalars R)) := by
  obtain ⟨a, ha0, ha⟩ := exists_hasBasisAway_quotient R A₀ A N hN
  exact ⟨a, ha0, fun b hb => (ha.quotient.of_dvd hb).free_away⟩

variable {R} {A₀ : Type*} [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀]
  {A : Type*} [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (φ : A₀ →ₐ[R] A)

theorem exists_free_away_coker :
    ∃ a : R, a ≠ 0 ∧ Module.Free (Localization.Away a)
      (LocalizedModule.Away a (A ⧸ LinearMap.range φ.toLinearMap)) := by
  obtain ⟨a, ha0, ha⟩ := exists_hasBasisAway_coker φ
  exact ⟨a, ha0, ha.free_away⟩

theorem exists_pow_smul_mem_range_of_surjective_baseChange.{w}
    (h : ∀ a : R, a ≠ 0 → ∃ (K : Type w) (_ : CommRing K) (_ : Nontrivial K) (_ : Algebra R K),
      IsUnit (algebraMap R K a) ∧
        Function.Surjective (Algebra.TensorProduct.map (AlgHom.id K K) φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ y : A, ∃ (n : ℕ) (x : A₀), φ x = a ^ n • y := by
  obtain ⟨a, ha0, ha⟩ := exists_hasBasisAway_coker φ
  obtain ⟨K, _, _, _, hK, hsurj⟩ := h a ha0
  refine ⟨a, ha0, fun y => ?_⟩
  haveI : Subsingleton (K ⊗[R] (A ⧸ LinearMap.range φ.toLinearMap)) := by
    refine subsingleton_of_forall_eq 0 fun z => ?_
    obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective K
      (LinearMap.range φ.toLinearMap).mkQ_surjective z
    obtain ⟨z, rfl⟩ := hsurj z
    induction z with
    | zero => simp
    | tmul c x =>
      have : (LinearMap.range φ.toLinearMap).mkQ (φ x) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
      rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul, this, tmul_zero]
    | add z w hz hw => rw [map_add, map_add, hz, hw, add_zero]
  obtain ⟨n, hn⟩ := ha.exists_pow_smul_eq_zero K hK ((LinearMap.range φ.toLinearMap).mkQ y)
  rw [← map_smul, mkQ_apply, Submodule.Quotient.mk_eq_zero] at hn
  exact ⟨n, hn⟩

theorem exists_pow_smul_mem_range_of_dense {D : Set (PrimeSpectrum R)} (hD : Dense D)
    (h : ∀ x ∈ D, Function.Surjective (Algebra.TensorProduct.map
      (AlgHom.id x.asIdeal.ResidueField x.asIdeal.ResidueField) φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ y : A, ∃ (n : ℕ) (x : A₀), φ x = a ^ n • y := by
  refine exists_pow_smul_mem_range_of_surjective_baseChange φ fun a ha => ?_
  obtain ⟨x, hxD, hxa⟩ := hD.exists_mem_open (PrimeSpectrum.basicOpen a).isOpen
    ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using ha⟩
  refine ⟨x.asIdeal.ResidueField, inferInstance, inferInstance, inferInstance, ?_, h x hxD⟩
  rw [isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]
  exact hxa

theorem exists_awayMap_surjective_of_dense {D : Set (PrimeSpectrum R)} (hD : Dense D)
    (h : ∀ x ∈ D, Function.Surjective (Algebra.TensorProduct.map
      (AlgHom.id x.asIdeal.ResidueField x.asIdeal.ResidueField) φ)) :
    ∃ a : R, a ≠ 0 ∧
      Function.Surjective (Localization.awayMap (φ : A₀ →+* A) (algebraMap R A₀ a)) := by
  obtain ⟨a, ha0, ha⟩ := exists_pow_smul_mem_range_of_dense φ hD h
  refine ⟨a, ha0, Localization.awayMap_surjective_iff.2 fun y => ?_⟩
  obtain ⟨n, x, hx⟩ := ha y
  exact ⟨x, n, by simp [hx, Algebra.smul_def]⟩

theorem exists_baseChange_surjective_of_dense.{w} {D : Set (PrimeSpectrum R)} (hD : Dense D)
    (h : ∀ x ∈ D, Function.Surjective (Algebra.TensorProduct.map
      (AlgHom.id x.asIdeal.ResidueField x.asIdeal.ResidueField) φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type w) [CommRing R'] [Algebra R R'],
      IsUnit (algebraMap R R' a) →
        Function.Surjective (Algebra.TensorProduct.map (AlgHom.id R' R') φ) := by
  obtain ⟨a, ha0, ha⟩ := exists_pow_smul_mem_range_of_dense φ hD h
  refine ⟨a, ha0, fun R' _ _ hu z => ?_⟩
  change z ∈ (Algebra.TensorProduct.map (AlgHom.id R' R') φ).range
  induction z with
  | zero => exact zero_mem _
  | tmul c y =>
    obtain ⟨n, x, hx⟩ := ha y
    obtain ⟨u, hu⟩ := (hu.pow n).exists_left_inv
    refine ⟨(c * u) ⊗ₜ x, ?_⟩
    change Algebra.TensorProduct.map (AlgHom.id R' R') φ _ = _
    rw [Algebra.TensorProduct.map_tmul, hx, ← smul_tmul, Algebra.smul_def, map_pow,
      AlgHom.id_apply, mul_comm, mul_assoc, hu, mul_one]
  | add z w hz hw => exact add_mem hz hw

end Statements

theorem generic_freeness.{u, v} (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] :
    (∀ (M : Type v) [AddCommGroup M] [Module R M] (F : ℕ → Submodule R M), Monotone F →
      ⨆ d, F d = ⊤ → Module.Free R (F 0) →
      (∀ d, Module.Free R (F (d + 1) ⧸ (F d).submoduleOf (F (d + 1)))) → Module.Free R M) ∧
    (∀ (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (M : Type v)
      [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite S M],
      ∃ a : R, a ≠ 0 ∧ Module.Free (Localization.Away a) (LocalizedModule.Away a M)) ∧
    (∀ (A₀ A : Type v) [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀]
      [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (φ : A₀ →ₐ[R] A),
      (∃ a : R, a ≠ 0 ∧ Module.Free (Localization.Away a)
        (LocalizedModule.Away a (A ⧸ LinearMap.range φ.toLinearMap))) ∧
      ∀ D : Set (PrimeSpectrum R), Dense D →
        (∀ x ∈ D, Function.Surjective (Algebra.TensorProduct.map
          (AlgHom.id x.asIdeal.ResidueField x.asIdeal.ResidueField) φ)) →
        ∃ a : R, a ≠ 0 ∧
          Function.Surjective (Localization.awayMap (φ : A₀ →+* A) (algebraMap R A₀ a))) :=
  ⟨fun _ _ _ F hF htop h0 h => free_of_chain F hF htop h0 h,
    fun S _ _ _ M _ _ _ _ _ => exists_free_away R S M,
    fun _ _ _ _ _ _ _ _ φ => ⟨exists_free_away_coker φ,
      fun _ hD h => exists_awayMap_surjective_of_dense φ hD h⟩⟩

end GlobalTheory

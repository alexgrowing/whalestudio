import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularMapCAppendMapLinForm

open MvPolynomial

noncomputable section

namespace GlobalTheory.Chow

section Defs

variable {K : Type*} [CommRing K] {σ β β' : Type*} [Fintype σ]

variable (K σ) in

def genericForm (i : β) : MvPolynomial (β × σ) (MvPolynomial σ K) :=
  linForm (X : σ → MvPolynomial σ K) i

theorem genericForm_eq (i : β) :
    genericForm K σ i = ∑ j, C (X j) * X (i, j) := rfl

variable (β) in

def incidenceIdeal (p : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial (β × σ) (MvPolynomial σ K)) :=
  p.map C ⊔ Ideal.span (Set.range (genericForm K σ : β → _))

theorem C_mem_incidenceIdeal {p : Ideal (MvPolynomial σ K)} {g : MvPolynomial σ K} (hg : g ∈ p) :
    C g ∈ incidenceIdeal β p :=
  Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg)

theorem genericForm_mem_incidenceIdeal (p : Ideal (MvPolynomial σ K)) (i : β) :
    genericForm K σ i ∈ incidenceIdeal β p :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)

theorem incidenceIdeal_le {p : Ideal (MvPolynomial σ K)}
    {J : Ideal (MvPolynomial (β × σ) (MvPolynomial σ K))} :
    incidenceIdeal β p ≤ J ↔ (∀ g ∈ p, C g ∈ J) ∧ ∀ i, genericForm K σ i ∈ J := by
  rw [incidenceIdeal, sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.span_le, Set.range_subset_iff]
  rfl

variable (β) in

def elimIdeal (p : Ideal (MvPolynomial σ K)) : Ideal (MvPolynomial (β × σ) K) where
  carrier := {f | ∃ m : ℕ, ∀ j, map C f * C (X j ^ m) ∈ incidenceIdeal β p}
  zero_mem' := ⟨0, fun _ => by simp⟩
  add_mem' := by
    rintro f g ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, fun j => ?_⟩
    have := Ideal.add_mem _ (Ideal.mul_mem_right (C (X j ^ n)) _ (hm j))
      (Ideal.mul_mem_right (C (X j ^ m)) _ (hn j))
    convert this using 1
    simp only [map_add, map_pow]
    ring
  smul_mem' := by
    rintro c f ⟨m, hm⟩
    refine ⟨m, fun j => ?_⟩
    rw [smul_eq_mul, map_mul, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hm j)

theorem mem_elimIdeal_iff_forall {p : Ideal (MvPolynomial σ K)} {f : MvPolynomial (β × σ) K} :
    f ∈ elimIdeal β p ↔ ∀ j, ∃ m : ℕ, map C f * C (X j ^ m) ∈ incidenceIdeal β p := by
  refine ⟨fun ⟨m, hm⟩ j => ⟨m, hm j⟩, fun h => ?_⟩
  choose m hm using h
  refine ⟨∑ j, m j, fun j => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  rw [hk, pow_add, C_mul, ← mul_assoc]
  exact Ideal.mul_mem_right _ _ (hm j)

theorem aeval_eq_zero_of_mem_elimIdeal {G : Type*} [CommRing G] [IsDomain G] [Algebra K G]
    {p : Ideal (MvPolynomial σ K)} {ξ : σ → G} (hξ : ∀ g ∈ p, aeval ξ g = 0) (hne : ξ ≠ 0)
    {t : β × σ → G} (ht : ∀ i, ∑ j, t (i, j) * ξ j = 0)
    {f : MvPolynomial (β × σ) K} (hf : f ∈ elimIdeal β p) : aeval t f = 0 := by
  obtain ⟨m, hm⟩ := hf
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  let ev : MvPolynomial (β × σ) (MvPolynomial σ K) →+* G :=
    eval₂Hom (aeval ξ : MvPolynomial σ K →ₐ[K] G).toRingHom t
  have hle : incidenceIdeal β p ≤ RingHom.ker ev := by
    refine incidenceIdeal_le.2 ⟨fun g hg => ?_, fun i => ?_⟩
    · simpa [ev, RingHom.mem_ker] using hξ g hg
    · rw [RingHom.mem_ker, genericForm_eq, map_sum, ← ht i]
      exact Finset.sum_congr rfl fun j _ => by simp [ev, mul_comm]
  have h := hle (hm j)
  have h2 : ev (map C f) = aeval t f := by
    have : ev.comp (map C) = (aeval t : _ →ₐ[K] G).toRingHom := by
      ext <;> simp [ev]
    exact DFunLike.congr_fun this f
  rw [RingHom.mem_ker, map_mul, h2] at h
  refine (mul_eq_zero.1 h).resolve_right ?_
  simpa [ev] using fun h0 => absurd h0 hj

theorem rename_mem_elimIdeal (e : β → β') {p : Ideal (MvPolynomial σ K)}
    {f : MvPolynomial (β × σ) K} (hf : f ∈ elimIdeal β p) :
    rename (Prod.map e id) f ∈ elimIdeal β' p := by
  obtain ⟨m, hm⟩ := hf
  refine ⟨m, fun j => ?_⟩
  have hle : incidenceIdeal β p ≤ (incidenceIdeal β' p).comap
      (rename (Prod.map e id : β × σ → β' × σ) : _ →ₐ[MvPolynomial σ K] _) := by
    refine incidenceIdeal_le.2 ⟨fun g hg => ?_, fun i => ?_⟩
    · simpa [Ideal.mem_comap] using C_mem_incidenceIdeal hg
    · have := genericForm_mem_incidenceIdeal p (e i)
      simpa [Ideal.mem_comap, genericForm_eq] using this
  have := hle (hm j)
  rwa [Ideal.mem_comap, map_mul, rename_C, ← map_rename] at this

theorem map_rename_elimIdeal (e : β ≃ β') (p : Ideal (MvPolynomial σ K)) :
    (elimIdeal β p).map (rename (Prod.map e id) : _ →ₐ[K] _) = elimIdeal β' p := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun f hf => rename_mem_elimIdeal e hf) ?_
  intro f hf
  have := Ideal.mem_map_of_mem (rename (Prod.map e id : β × σ → β' × σ) : _ →ₐ[K] _)
    (rename_mem_elimIdeal e.symm hf)
  rwa [rename_rename, Prod.map_comp_map, e.self_comp_symm, Function.id_comp, Prod.map_id,
    rename_id_apply] at this

end Defs

section Prime

variable {σ β : Type*} [Fintype σ]

theorem exists_pow_mul_sub_rename_mem {R : Type*} [CommRing R] (u : σ → R) (j : σ)
    (h : MvPolynomial (β × σ) R) :
    ∃ (m : ℕ) (g : MvPolynomial {v : β × σ // v ∉ elimIndices Set.univ j} R),
      h * C (u j ^ m) - rename Subtype.val g ∈ Ideal.span (Set.range (linForm u : β → _)) := by
  classical
  induction h using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, by simp⟩
  | add f g hf hg =>
    obtain ⟨m, f', hf⟩ := hf
    obtain ⟨n, g', hg⟩ := hg
    refine ⟨m + n, f' * C (u j ^ n) + g' * C (u j ^ m), ?_⟩
    have := Ideal.add_mem _ (Ideal.mul_mem_right (C (u j ^ n)) _ hf)
      (Ideal.mul_mem_right (C (u j ^ m)) _ hg)
    convert this using 1
    simp only [map_add, map_mul, map_pow, rename_C]
    ring
  | mul_X f v hf =>
    obtain ⟨m, f', hf⟩ := hf
    by_cases hv : v ∈ elimIndices Set.univ j
    · obtain ⟨i, k⟩ := v
      obtain rfl : k = j := hv.2
      let r : MvPolynomial {v : β × σ // v ∉ elimIndices Set.univ k} R :=
        ∑ l : {l : σ // l ≠ k}, C (u l) * X ⟨(i, l.1), fun h => l.2 h.2⟩
      have hr : linForm u i = C (u k) * X (i, k) + rename Subtype.val r := by
        rw [linForm_eq u i k, Finset.sum_subtype (p := fun l => l ≠ k) (F := inferInstance) _
          (by simp)]
        simp [r]
      refine ⟨m + 1, -(f' * r), ?_⟩
      have := Ideal.add_mem _ (Ideal.mul_mem_right (C (u k) * X (i, k)) _ hf)
        (Ideal.mul_mem_left _ (rename Subtype.val f') (Ideal.subset_span ⟨i, rfl⟩))
      convert this using 1
      simp only [hr, map_neg, map_mul, map_pow, pow_succ]
      ring
    · refine ⟨m, f' * X ⟨v, hv⟩, ?_⟩
      have := Ideal.mul_mem_right (X v) _ hf
      convert this using 1
      simp only [map_mul, rename_X]
      ring

theorem map_linForm {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (u : σ → R) (i : β) :
    map φ (linForm u i) = linForm (fun j => φ (u j)) i := by
  simp [linForm]

theorem map_mem_span_linForm {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {u : σ → R}
    {h : MvPolynomial (β × σ) R} (hh : h ∈ Ideal.span (Set.range (linForm u : β → _))) :
    map φ h ∈ Ideal.span (Set.range (linForm (fun j => φ (u j)) : β → _)) := by
  have hle : Ideal.span (Set.range (linForm u : β → _)) ≤
      (Ideal.span (Set.range (linForm (fun j => φ (u j)) : β → _))).comap (map φ) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨i, (map_linForm φ u i).symm⟩
  exact hle hh

variable {K : Type*} [CommRing K]

theorem mem_elimIdeal_iff_of_generic {F : Type*} [Field F] [Algebra K F]
    {p : Ideal (MvPolynomial σ K)} {ξ : σ → F} (hξ : ∀ g, aeval ξ g = 0 ↔ g ∈ p) (hne : ξ ≠ 0)
    {f : MvPolynomial (β × σ) K} :
    f ∈ elimIdeal β p ↔
      map (algebraMap K F) f ∈ Ideal.span (Set.range (linForm ξ : β → _)) := by
  let φ : MvPolynomial σ K →+* F := (aeval ξ : MvPolynomial σ K →ₐ[K] F).toRingHom
  have hφ : (fun j => φ (X j)) = ξ := by ext j; simp [φ]
  have hφj (j) : φ (X j) = ξ j := congrFun hφ j
  have hC : φ.comp C = algebraMap K F := by ext; simp [φ]
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    have hle : incidenceIdeal β p ≤
        (Ideal.span (Set.range (linForm ξ : β → _))).comap (map φ) := by
      refine incidenceIdeal_le.2 ⟨fun g hg => ?_, fun i => ?_⟩
      · have : φ g = 0 := (hξ g).2 hg
        simp [Ideal.mem_comap, this]
      · rw [Ideal.mem_comap, genericForm, map_linForm, hφ]
        exact Ideal.subset_span ⟨i, rfl⟩
    have := hle (hm j)
    rw [Ideal.mem_comap, map_mul, map_map, hC, map_C, map_pow, hφj] at this
    exact (Ideal.mul_unit_mem_iff_mem _ ((pow_ne_zero m hj).isUnit.map C)).1 this
  · intro hf
    refine mem_elimIdeal_iff_forall.2 fun j => ?_
    by_cases hj : ξ j = 0
    · exact ⟨1, Ideal.mul_mem_left _ _ (C_mem_incidenceIdeal (by
        rw [pow_one, ← hξ, aeval_X, hj]))⟩
    obtain ⟨m, g, hg⟩ := exists_pow_mul_sub_rename_mem (X : σ → MvPolynomial σ K) j (map C f)
    refine ⟨m, ?_⟩
    have h1 := map_mem_span_linForm φ hg
    rw [hφ, map_sub, map_mul, map_map, hC, map_rename] at h1
    have h2 : rename Subtype.val (map φ g) ∈ Ideal.span (Set.range (linForm ξ : β → _)) := by
      have := Ideal.sub_mem _ (Ideal.mul_mem_right (map φ (C (X j ^ m))) _ hf) h1
      rwa [sub_sub_cancel] at this
    rw [← Set.image_univ, ← ker_linFormElim ξ (Ne.isUnit hj), RingHom.mem_ker,
      linFormElim_rename, ← RingHom.mem_ker, MvPolynomial.ker_map] at h2
    have hker : RingHom.ker φ = p := Ideal.ext fun g => hξ g
    rw [hker] at h2
    have h3 : rename Subtype.val g ∈ p.map (C : _ →+* MvPolynomial (β × σ) (MvPolynomial σ K)) := by
      rw [← Ideal.mem_comap (f := (rename Subtype.val : _ →ₐ[MvPolynomial σ K] _))]
      refine Ideal.map_le_iff_le_comap.2 (fun a ha => ?_) h2
      simpa [Ideal.mem_comap] using Ideal.mem_map_of_mem _ ha
    have := Ideal.add_mem _ (Ideal.mem_sup_right (S := p.map C) hg) (Ideal.mem_sup_left h3)
    rwa [sub_add_cancel] at this

def genericPoint (p : Ideal (MvPolynomial σ K)) (j : σ) : FractionRing (MvPolynomial σ K ⧸ p) :=
  algebraMap (MvPolynomial σ K ⧸ p) _ (Ideal.Quotient.mk p (X j))

omit [Fintype σ] in
theorem aeval_genericPoint (p : Ideal (MvPolynomial σ K)) (g : MvPolynomial σ K) :
    aeval (genericPoint p) g = algebraMap (MvPolynomial σ K ⧸ p) _ (Ideal.Quotient.mk p g) := by
  have : (aeval (genericPoint p) : _ →ₐ[K] _) =
      (IsScalarTower.toAlgHom K (MvPolynomial σ K ⧸ p) _).comp (Ideal.Quotient.mkₐ K p) := by
    ext j; simp [genericPoint]
  exact DFunLike.congr_fun this g

omit [Fintype σ] in
theorem aeval_genericPoint_eq_zero_iff (p : Ideal (MvPolynomial σ K)) (g : MvPolynomial σ K) :
    aeval (genericPoint p) g = 0 ↔ g ∈ p := by
  rw [aeval_genericPoint, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

omit [Fintype σ] in
theorem genericPoint_ne_zero {p : Ideal (MvPolynomial σ K)} (hp : ∃ j, X j ∉ p) :
    genericPoint p ≠ 0 := by
  obtain ⟨j, hj⟩ := hp
  intro h
  exact hj ((aeval_genericPoint_eq_zero_iff p _).1 (by rw [aeval_X, h]; rfl))

theorem isPrime_elimIdeal {p : Ideal (MvPolynomial σ K)} [p.IsPrime] (hp : ∃ j, X j ∉ p) :
    (elimIdeal β p).IsPrime := by
  have hne := genericPoint_ne_zero hp
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  have h := isPrime_span_linForm (ι := β) (genericPoint p) (Ne.isUnit hj) Set.univ
  rw [Set.image_univ] at h
  have : elimIdeal β p = (Ideal.span (Set.range (linForm (genericPoint p) : β → _))).comap
      (map (algebraMap K _)) :=
    Ideal.ext fun f => mem_elimIdeal_iff_of_generic (aeval_genericPoint_eq_zero_iff p) hne
  rw [this]
  exact Ideal.comap_isPrime _ _

end Prime

section Homogeneous

variable {K : Type*} [CommRing K] {σ β β' : Type*}

def blockWeight [DecidableEq β] (v : β × σ) : β → ℕ := Pi.single v.1 1

def IsBlockHomogeneous [DecidableEq β] (f : MvPolynomial (β × σ) K) (a : β → ℕ) : Prop :=
  IsWeightedHomogeneous blockWeight f a

variable [DecidableEq β] [DecidableEq β']

theorem weight_blockWeight [Fintype σ] (d : β × σ →₀ ℕ) (i : β) :
    Finsupp.weight blockWeight d i = ∑ j, d (i, j) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simp [hd, he, Finset.sum_add_distrib]
  | single v n =>
    obtain ⟨k, l⟩ := v
    by_cases h : k = i
    · subst h
      simp [Finsupp.weight_single, blockWeight, Finsupp.single_apply]
    · simp [Finsupp.weight_single, blockWeight, Finsupp.single_apply, h, Ne.symm h]

theorem isBlockHomogeneous_iff [Fintype σ] {f : MvPolynomial (β × σ) K} {a : β → ℕ} :
    IsBlockHomogeneous f a ↔ ∀ d ∈ f.support, ∀ i, ∑ j, d (i, j) = a i := by
  simp only [IsBlockHomogeneous, IsWeightedHomogeneous, mem_support_iff, funext_iff,
    weight_blockWeight]

theorem IsBlockHomogeneous.mul {f g : MvPolynomial (β × σ) K} {a b : β → ℕ}
    (hf : IsBlockHomogeneous f a) (hg : IsBlockHomogeneous g b) :
    IsBlockHomogeneous (f * g) (a + b) := IsWeightedHomogeneous.mul hf hg

theorem IsBlockHomogeneous.unique {f : MvPolynomial (β × σ) K} {a b : β → ℕ} (h : f ≠ 0)
    (ha : IsBlockHomogeneous f a) (hb : IsBlockHomogeneous f b) : a = b :=
  IsWeightedHomogeneous.inj_right h ha hb

theorem IsBlockHomogeneous.isHomogeneous [Fintype σ] [Fintype β] {f : MvPolynomial (β × σ) K}
    {a : β → ℕ} (h : IsBlockHomogeneous f a) : f.IsHomogeneous (∑ i, a i) := by
  intro d hd
  have := isBlockHomogeneous_iff.1 h d (mem_support_iff.2 hd)
  change Finsupp.weight (fun _ => 1) d = _
  rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => this i

theorem IsBlockHomogeneous.rename [Fintype σ] (e : β ≃ β') {f : MvPolynomial (β × σ) K}
    {a : β → ℕ} (h : IsBlockHomogeneous f a) :
    IsBlockHomogeneous (rename (Prod.map e id) f) (a ∘ e.symm) := by
  classical
  rw [isBlockHomogeneous_iff] at h ⊢
  intro d hd i
  have hinj : Function.Injective (Prod.map e id : β × σ → β' × σ) :=
    e.injective.prodMap Function.injective_id
  rw [support_rename_of_injective hinj, Finset.mem_image] at hd
  obtain ⟨c, hc, rfl⟩ := hd
  rw [Function.comp_apply, ← h c hc]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := Finsupp.mapDomain_apply hinj c (e.symm i, j)
  simpa using this

theorem IsBlockHomogeneous.aeval_smul [Fintype σ] [Fintype β] {G : Type*} [CommRing G]
    [Algebra K G] {f : MvPolynomial (β × σ) K} {a : β → ℕ} (h : IsBlockHomogeneous f a)
    (c : β → G) (t : β × σ → G) :
    aeval (fun v => c v.1 * t v) f = (∏ i, c i ^ a i) * aeval t f := by
  rw [isBlockHomogeneous_iff] at h
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [mul_pow, Finset.prod_mul_distrib, Fintype.prod_prod_type,
    Finset.prod_pow_eq_pow_sum, h d hd]
  ring

theorem isBlockHomogeneous_linForm [Fintype σ] (u : σ → K) (i : β) :
    IsBlockHomogeneous (linForm u i) (Pi.single i 1) :=
  IsWeightedHomogeneous.sum _ _ _ fun j _ =>
    (isWeightedHomogeneous_X K blockWeight (i, j)).C_mul _

theorem map_weightedHomogeneousComponent {S τ M : Type*} [CommRing S] [AddCommMonoid M]
    (φ : K →+* S) (w : τ → M) (a : M) (f : MvPolynomial τ K) :
    map φ (weightedHomogeneousComponent w a f) = weightedHomogeneousComponent w a (map φ f) := by
  classical
  ext d
  simp only [coeff_map, coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

theorem weightedHomogeneousComponent_mem_elimIdeal [Fintype σ] [Finite β]
    {p : Ideal (MvPolynomial σ K)}
    {f : MvPolynomial (β × σ) K} (hf : f ∈ elimIdeal β p) (a : β → ℕ) :
    weightedHomogeneousComponent blockWeight a f ∈ elimIdeal β p := by
  classical
  letI := weightedGradedAlgebra (MvPolynomial σ K) (blockWeight : β × σ → β → ℕ)
  have hI : (incidenceIdeal β p).IsHomogeneous
      (weightedHomogeneousSubmodule (MvPolynomial σ K) (blockWeight : β × σ → β → ℕ)) := by
    refine Ideal.IsHomogeneous.sup (Ideal.homogeneous_span _ _ ?_) (Ideal.homogeneous_span _ _ ?_)
    · rintro _ ⟨g, -, rfl⟩
      exact ⟨0, isWeightedHomogeneous_C _ _⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨_, isBlockHomogeneous_linForm _ i⟩
  obtain ⟨m, hm⟩ := hf
  refine ⟨m, fun j => ?_⟩
  have := weightedHomogeneousComponent_mem_of_mem _ _ hI (hm j) a
  rwa [mul_comm, weightedHomogeneousComponent_C_mul, ← map_weightedHomogeneousComponent,
    mul_comm] at this

end Homogeneous

section Generator

variable {K : Type*} [Field K] {τ M : Type*} [AddCommMonoid M]

theorem exists_eq_C_mul_of_dvd {f g : MvPolynomial τ K} (hg : g ≠ 0) (h : f ∣ g)
    (hd : g.totalDegree ≤ f.totalDegree) : ∃ c : K, c ≠ 0 ∧ g = C c * f := by
  obtain ⟨q, rfl⟩ := h
  have hf := left_ne_zero_of_mul hg
  have hq := right_ne_zero_of_mul hg
  rw [totalDegree_mul_of_isDomain hf hq] at hd
  have h0 : q.totalDegree = 0 := by omega
  rw [totalDegree_eq_zero_iff_eq_C] at h0
  refine ⟨coeff 0 q, fun hc => hq ?_, ?_⟩
  · rw [h0, hc, C_0]
  · rw [← h0, mul_comm]

theorem exists_isWeightedHomogeneous_of_dvd (w : τ → M) {f : MvPolynomial τ K}
    (h : ∀ a, f ∣ weightedHomogeneousComponent w a f) : ∃ a, IsWeightedHomogeneous w f a := by
  classical
  by_cases hf : f = 0
  · exact ⟨0, hf ▸ isWeightedHomogeneous_zero K w 0⟩
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero hf
  have hne : weightedHomogeneousComponent w (Finsupp.weight w d) f ≠ 0 := by
    intro h0
    have := coeff_weightedHomogeneousComponent (w := w) (Finsupp.weight w d) f d
    rw [h0, if_pos rfl, coeff_zero] at this
    exact hd this.symm
  have hle : (weightedHomogeneousComponent w (Finsupp.weight w d) f).totalDegree ≤
      f.totalDegree := by
    refine totalDegree_le_of_support_subset fun e he => ?_
    rw [mem_support_iff, coeff_weightedHomogeneousComponent] at he
    rw [mem_support_iff]
    intro h0
    simp [h0] at he
  obtain ⟨c, hc, hcf⟩ := exists_eq_C_mul_of_dvd hne (h _) hle
  refine ⟨Finsupp.weight w d, ?_⟩
  have := (weightedHomogeneousComponent_isWeightedHomogeneous (w := w)
    (Finsupp.weight w d) f).C_mul c⁻¹
  rwa [hcf, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul] at this

theorem exists_eq_C_mul_of_span_eq {f g : MvPolynomial τ K}
    (h : Ideal.span {f} = Ideal.span {g}) : ∃ c : K, c ≠ 0 ∧ g = C c * f := by
  obtain ⟨u, rfl⟩ := Ideal.span_singleton_eq_span_singleton.1 h
  obtain ⟨c, hc, hu⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
  exact ⟨c, hc.ne_zero, by rw [hu, mul_comm]⟩

end Generator

end GlobalTheory.Chow

import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUnitSmulEqOfBijectiveToSpanSingleton

open scoped TensorProduct

namespace GlobalTheory

def IsFreeRingAction (G A : Type*) [Group G] [CommRing A] [MulSemiringAction G A] : Prop :=
  ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤

namespace FreeQuotient

section Basic

variable (G : Type*) [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]

theorem isFreeRingAction_iff_inertia_eq_bot :
    IsFreeRingAction G A ↔ ∀ P : Ideal A, P.IsMaximal → P.inertia G = ⊥ := by
  constructor
  · intro h P hP
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    by_contra hg1
    refine hP.ne_top (top_le_iff.mp ?_)
    rw [← h g hg1, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    exact AddSubgroup.mem_inertia.mp hg a
  · intro h g hg
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have : g ∈ P.inertia G :=
      AddSubgroup.mem_inertia.mpr fun a ↦ hle (Ideal.subset_span ⟨a, rfl⟩)
    rw [h P hP] at this
    exact hg this

theorem isFreeRingAction_iff_inertia_eq_bot_of_isPrime :
    IsFreeRingAction G A ↔ ∀ P : Ideal A, P.IsPrime → P.inertia G = ⊥ := by
  refine ⟨fun h P hP ↦ ?_, fun h ↦
    (isFreeRingAction_iff_inertia_eq_bot G A).mpr fun P hP ↦ h P hP.isPrime⟩
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hP.ne_top
  rw [eq_bot_iff, ← (isFreeRingAction_iff_inertia_eq_bot G A).mp h Q hQ]
  exact fun g hg ↦ AddSubgroup.mem_inertia.mpr fun a ↦ hle (AddSubgroup.mem_inertia.mp hg a)

theorem isFreeRingAction_of_field (K : Type*) [Field K] [MulSemiringAction G K]
    [FaithfulSMul G K] : IsFreeRingAction G K := by
  intro g hg
  rcases Ideal.eq_bot_or_top (Ideal.span (Set.range fun a : K ↦ g • a - a)) with h | h
  · refine absurd (eq_of_smul_eq_smul (α := K) fun a ↦ ?_) hg
    have : g • a - a ∈ Ideal.span (Set.range fun a : K ↦ g • a - a) := Ideal.subset_span ⟨a, rfl⟩
    rw [h, Ideal.mem_bot, sub_eq_zero] at this
    rw [this, one_smul]
  · exact h

variable (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]

noncomputable def galoisMap : A ⊗[B] A →ₐ[A] (G → A) :=
  Algebra.TensorProduct.lift (Algebra.ofId A (G → A))
    (Pi.algHom B _ fun g ↦ MulSemiringAction.toAlgHom B A g) fun _ _ ↦ Commute.all _ _

@[simp] theorem galoisMap_tmul (a b : A) (g : G) :
    galoisMap G A B (a ⊗ₜ b) g = a * g • b := rfl

variable {G A} in

theorem exists_galoisMap_separating [Finite G] (P : Ideal A) (H : Set G)
    (hH : ∀ h ∈ H, ∀ a : A, h • a - a ∈ P)
    (hH' : ∀ g ∉ H, P ⊔ Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    ∃ e : A ⊗[B] A, (∀ g ∉ H, galoisMap G A B e g = 0) ∧
      ∀ h ∈ H, galoisMap G A B e h - 1 ∈ P := by
  classical
  cases nonempty_fintype G
  have key : ∀ g : G, ∀ c ∈ Ideal.span (Set.range fun a : A ↦ g • a - a),
      ∃ e : A ⊗[B] A, galoisMap G A B e g = 0 ∧ ∀ h ∈ H, galoisMap G A B e h - c ∈ P := by
    intro g c hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨(g • a) ⊗ₜ 1 - 1 ⊗ₜ a, by simp, fun h hh ↦ ?_⟩
      have := P.neg_mem (hH h hh a)
      simp only [map_sub, Pi.sub_apply, galoisMap_tmul, smul_one, mul_one, one_mul]
      convert this using 1
      ring
    | zero => exact ⟨0, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨e, he, he'⟩ := hx
      obtain ⟨f, hf, hf'⟩ := hy
      refine ⟨e + f, by simp [he, hf], fun h hh ↦ ?_⟩
      have := P.add_mem (he' h hh) (hf' h hh)
      simp only [map_add, Pi.add_apply]
      convert this using 1
      ring
    | smul r x _ hx =>
      obtain ⟨e, he, he'⟩ := hx
      refine ⟨r • e, by simp [he], fun h hh ↦ ?_⟩
      have := P.mul_mem_left r (he' h hh)
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      convert this using 1
      ring
  have key2 : ∀ g ∉ H,
      ∃ e : A ⊗[B] A, galoisMap G A B e g = 0 ∧ ∀ h ∈ H, galoisMap G A B e h - 1 ∈ P := by
    intro g hg
    have h1 : (1 : A) ∈ P ⊔ Ideal.span (Set.range fun a : A ↦ g • a - a) := by
      rw [hH' g hg]; trivial
    obtain ⟨p, hp, c, hc, hpc⟩ := Submodule.mem_sup.mp h1
    obtain ⟨e, he, he'⟩ := key g c hc
    refine ⟨e, he, fun h hh ↦ ?_⟩
    have := P.sub_mem (he' h hh) hp
    rw [← hpc]
    convert this using 1
    ring
  choose! e he he' using key2
  refine ⟨∏ g ∈ Finset.univ.filter (· ∉ H), e g, fun g hg ↦ ?_, fun h hh ↦ ?_⟩
  · rw [map_prod, Finset.prod_apply]
    exact Finset.prod_eq_zero (i := g) (by simpa using hg) (he g hg)
  · rw [map_prod, Finset.prod_apply, ← Ideal.Quotient.eq, map_prod, map_one]
    refine Finset.prod_eq_one fun g hg ↦ ?_
    rw [← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq]
    exact he' g (by simpa using hg) h hh

variable {G A} in

theorem exists_finset_separating [Finite G] (P : Ideal A) (H : Set G)
    (hH : ∀ h ∈ H, ∀ a : A, h • a - a ∈ P)
    (hH' : ∀ g ∉ H, P ⊔ Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    ∃ s : Finset (A × A), (∀ g ∉ H, ∑ p ∈ s, p.1 * g • p.2 = 0) ∧
      ∀ h ∈ H, ∑ p ∈ s, p.1 * h • p.2 - 1 ∈ P := by
  obtain ⟨e, he, he'⟩ := exists_galoisMap_separating ℤ P H hH hH'
  obtain ⟨s, rfl⟩ := e.exists_finset
  refine ⟨s, fun g hg ↦ ?_, fun h hh ↦ ?_⟩
  · simpa [Finset.sum_apply] using he g hg
  · simpa [Finset.sum_apply] using he' h hh

variable {G A} in

theorem exists_galois_coordinates [Finite G] (h : IsFreeRingAction G A) :
    ∃ s : Finset (A × A), (∀ g : G, g ≠ 1 → ∑ p ∈ s, p.1 * g • p.2 = 0) ∧
      ∑ p ∈ s, p.1 * p.2 = 1 := by
  obtain ⟨s, hs, hs'⟩ := exists_finset_separating (G := G) (⊥ : Ideal A) {1}
    (by rintro _ rfl a; simp) (fun g hg ↦ by rw [h g hg, sup_top_eq])
  exact ⟨s, hs, by simpa [sub_eq_zero] using hs' 1 rfl⟩

variable {G A} in

theorem exists_finset_inertia [Finite G] (P : Ideal A) [hP : P.IsMaximal] :
    ∃ s : Finset (A × A), (∀ g ∉ P.inertia G, ∑ p ∈ s, p.1 * g • p.2 = 0) ∧
      ∀ h ∈ P.inertia G, ∑ p ∈ s, p.1 * h • p.2 - 1 ∈ P := by
  refine exists_finset_separating P (P.inertia G : Set G)
    (fun h hh ↦ AddSubgroup.mem_inertia.mp hh) fun g hg ↦ ?_
  by_contra hne
  refine hg (AddSubgroup.mem_inertia.mpr fun a ↦ ?_)
  have := hP.eq_of_le hne le_sup_left
  change g • a - a ∈ P
  rw [this]
  exact Ideal.mem_sup_right (Ideal.subset_span ⟨a, rfl⟩)

end Basic

instance smulDistribClass_self (G : Type*) [Group G] (A : Type*) [CommRing A]
    [MulSemiringAction G A] : SMulDistribClass G A A :=
  ⟨fun g a b ↦ smul_mul' g a b⟩

theorem smul_sum_smul {G : Type*} [Group G] [Fintype G] {M : Type*} [AddCommMonoid M]
    [DistribMulAction G M] (m : M) (g : G) : g • ∑ h : G, h • m = ∑ h : G, h • m := by
  simp only [Finset.smul_sum, smul_smul]
  exact Equiv.sum_comp (Equiv.mulLeft g) fun h ↦ h • m

section Trace

variable (G : Type*) [Group G] [Fintype G] (B : Type*) [CommRing B]
  (M : Type*) [AddCommGroup M] [Module B M] [DistribMulAction G M] [SMulCommClass G B M]

def moduleTrace : M →ₗ[B] (Representation.ofDistribMulAction B G M).invariants where
  toFun m := ⟨∑ g : G, g • m, fun g ↦ smul_sum_smul m g⟩
  map_add' x y := Subtype.ext (by simp [Finset.sum_add_distrib])
  map_smul' b x := Subtype.ext (by simp [Finset.smul_sum, smul_comm _ b])

@[simp] theorem coe_moduleTrace (m : M) : (moduleTrace G B M m : M) = ∑ g : G, g • m := rfl

variable (A : Type*) [CommRing A] [MulSemiringAction G A] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]

noncomputable def invariantsRingEquiv :
    B ≃ₗ[B] (Representation.ofDistribMulAction B G A).invariants :=
  LinearEquiv.ofBijective ((Algebra.linearMap B A).codRestrict
      (Representation.ofDistribMulAction B G A).invariants fun b g ↦ smul_algebraMap g b)
    ⟨fun a b hab ↦ FaithfulSMul.algebraMap_injective B A (congrArg Subtype.val hab),
      fun ⟨x, hx⟩ ↦ by
        obtain ⟨b, rfl⟩ := Algebra.IsInvariant.isInvariant (A := B) (G := G) x hx
        exact ⟨b, rfl⟩⟩

omit [Fintype G] in
theorem algebraMap_invariantsRingEquiv_symm
    (x : (Representation.ofDistribMulAction B G A).invariants) :
    algebraMap B A ((invariantsRingEquiv G B A).symm x) = x :=
  congrArg Subtype.val ((invariantsRingEquiv G B A).apply_symm_apply x)

noncomputable def ringTrace : A →ₗ[B] B :=
  (invariantsRingEquiv G B A).symm.toLinearMap ∘ₗ moduleTrace G B A

@[simp] theorem algebraMap_ringTrace (a : A) :
    algebraMap B A (ringTrace G B A a) = ∑ g : G, g • a :=
  algebraMap_invariantsRingEquiv_symm G B A _

end Trace

section Tame

variable {G : Type*} [Group G] [Fintype G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]

theorem sum_smul_sum_smul (s : Finset (A × A)) (m : M) :
    ∑ p ∈ s, p.1 • ∑ g : G, g • (p.2 • m) = ∑ g : G, (∑ p ∈ s, p.1 * g • p.2) • g • m := by
  simp only [Finset.smul_sum, Finset.sum_smul, smul_distrib_smul, mul_smul]
  exact Finset.sum_comm

theorem exists_sum_sub_card_smul_mem (P : Ideal A) [P.IsMaximal] (m : M)
    (hm : ∀ g ∈ P.inertia G, g • m - m ∈ P • (⊤ : Submodule A M)) :
    ∃ s : Finset (A × A), ∑ p ∈ s, p.1 • ∑ g : G, g • (p.2 • m) -
      (Nat.card (P.inertia G) : A) • m ∈ P • (⊤ : Submodule A M) := by
  classical
  obtain ⟨s, hs, hs'⟩ := exists_finset_inertia (G := G) P
  refine ⟨s, ?_⟩
  rw [sum_smul_sum_smul, ← Finset.sum_subset (Finset.filter_subset (· ∈ P.inertia G) _)
    (fun g _ hg ↦ by rw [hs g (by simpa using hg), zero_smul])]
  have : (Nat.card (P.inertia G) : A) • m =
      ∑ _g ∈ Finset.univ.filter (· ∈ P.inertia G), m := by
    rw [Finset.sum_const, Nat.cast_smul_eq_nsmul, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [this, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun g hg ↦ ?_
  have hg' : g ∈ P.inertia G := by simpa using hg
  have := add_mem (Submodule.smul_mem_smul (hs' g hg') (Submodule.mem_top (x := g • m)))
    (hm g hg')
  convert this using 1
  rw [sub_smul, one_smul]
  abel

variable (G A) in

theorem exists_sum_smul_eq_one
    (h : ∀ P : Ideal A, P.IsMaximal → (Nat.card (P.inertia G) : A) ∉ P) :
    ∃ c : A, ∑ g : G, g • c = 1 := by
  let B := FixedPoints.subring A G
  haveI := isIntegral_fixedSubring A G
  have : LinearMap.range (ringTrace G B A) = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨P, hP, rfl⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) Q
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective B A)]
          exact bot_le)
    obtain ⟨s, hs⟩ := exists_sum_sub_card_smul_mem (G := G) P (1 : A) (by simp)
    rw [smul_eq_mul, Ideal.mul_top, smul_eq_mul, mul_one] at hs
    refine h P hP ((Submodule.sub_mem_iff_right _ (Ideal.sum_mem _ fun p _ ↦ ?_)).mp hs)
    refine P.mul_mem_left _ ?_
    rw [← algebraMap_ringTrace G B A]
    exact hle ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := LinearMap.range_eq_top.mp this 1
  exact ⟨c, by rw [← algebraMap_ringTrace G B A, hc, map_one]⟩

theorem span_fixed_eq_top [Module.Finite A M]
    (h : ∀ P : Ideal A, P.IsMaximal → (Nat.card (P.inertia G) : A) ∉ P)
    (hM : ∀ P : Ideal A, P.IsMaximal → ∀ g ∈ P.inertia G, ∀ m : M,
      g • m - m ∈ P • (⊤ : Submodule A M)) :
    Submodule.span A {m : M | ∀ g : G, g • m = m} = ⊤ := by
  set N := Submodule.span A {m : M | ∀ g : G, g • m = m} with hN
  have : N.colon Set.univ = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have htop : (⊤ : Submodule A M) ≤ N ⊔ P • ⊤ := by
      intro m _
      obtain ⟨s, hs⟩ := exists_sum_sub_card_smul_mem (G := G) P m fun g hg ↦ hM P hP g hg m
      obtain ⟨u, p, hp, hup⟩ := hP.exists_inv (h P hP)
      have h1 : ∑ p ∈ s, p.1 • ∑ g : G, g • (p.2 • m) ∈ N :=
        Submodule.sum_mem _ fun p _ ↦ N.smul_mem _
          (Submodule.subset_span fun g ↦ smul_sum_smul _ g)
      have h2 : (Nat.card (P.inertia G) : A) • m ∈ N ⊔ P • ⊤ := by
        have := sub_mem (Submodule.mem_sup_left (T := P • ⊤) h1) (Submodule.mem_sup_right hs)
        simpa using this
      have := add_mem (Submodule.smul_mem _ u h2)
        (Submodule.mem_sup_right (Submodule.smul_mem_smul hp (Submodule.mem_top (x := m))))
      rwa [smul_smul, ← add_smul, hup, one_smul] at this
    obtain ⟨r, hr, hr'⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
      Module.Finite.fg_top le_rfl htop
    have : r ∈ P := hle (Submodule.mem_colon.mpr fun m _ ↦
      hr' (Submodule.smul_mem_pointwise_smul m r ⊤ trivial))
    exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using P.sub_mem this hr))
  rw [eq_top_iff]
  intro m _
  have h1 : (1 : A) ∈ N.colon Set.univ := by rw [this]; trivial
  simpa using Submodule.mem_colon.mp h1 m trivial

end Tame

section DualBasis

variable {G : Type*} [Group G] [Fintype G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  {N : Type*} [AddCommGroup N] [Module A N] [DistribMulAction G N] [SMulDistribClass G A N]

variable (G) in

def averageMap (f : M →ₗ[A] N) : M →ₗ[A] N where
  toFun m := ∑ g : G, g • f (g⁻¹ • m)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, smul_distrib_smul]

theorem averageMap_apply (f : M →ₗ[A] N) (m : M) :
    averageMap G f m = ∑ g : G, g • f (g⁻¹ • m) := rfl

theorem averageMap_smul (f : M →ₗ[A] N) (h : G) (m : M) :
    averageMap G f (h • m) = h • averageMap G f m := by
  simp only [averageMap_apply, Finset.smul_sum, smul_smul]
  rw [← Equiv.sum_comp (Equiv.mulLeft h)]
  simp

theorem exists_invariant_dual_basis [Module.Finite A M] [Module.Projective A M]
    {c : A} (hc : ∑ g : G, g • c = 1)
    (hM : Submodule.span A {m : M | ∀ g : G, g • m = m} = ⊤) :
    ∃ (n : ℕ) (v : Fin n → M) (f : Fin n → M →ₗ[A] A), (∀ i (g : G), g • v i = v i) ∧
      (∀ i (g : G) m, f i (g • m) = g • f i m) ∧ ∀ m, ∑ i, f i m • v i = m := by
  classical
  obtain ⟨t, ht, ht'⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    (R := A) {m : M | ∀ g : G, g • m = m}).mp (hM ▸ Module.Finite.fg_top)
  let v : Fin t.card → M := fun i ↦ t.equivFin.symm i
  have hv : ∀ i (g : G), g • v i = v i := fun i ↦ ht (t.equivFin.symm i).2
  have hsurj : Function.Surjective (Fintype.linearCombination A v) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff, ← hM, ht']
    exact Submodule.span_mono fun x hx ↦ ⟨t.equivFin ⟨x, hx⟩, by simp [v]⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hsurj
  have hs' : ∀ m, ∑ i, s m i • v i = m := fun m ↦ by
    simpa [Fintype.linearCombination_apply] using LinearMap.congr_fun hs m
  refine ⟨t.card, v, fun i ↦ averageMap G (c • (LinearMap.proj i ∘ₗ s)), hv,
    fun i g m ↦ averageMap_smul _ g m, fun m ↦ ?_⟩
  simp only [averageMap_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  have : ∀ g : G, ∑ i, (g • (c • (LinearMap.proj i ∘ₗ s : M →ₗ[A] A)) (g⁻¹ • m)) • v i =
      (g • c) • m := fun g ↦ by
    conv_rhs => rw [← smul_inv_smul g m, ← smul_distrib_smul, ← hs' (g⁻¹ • m)]
    simp only [Finset.smul_sum, smul_distrib_smul, hv]
    simp [mul_smul]
  simp only [this]
  rw [← Finset.sum_smul, hc, one_smul]

variable (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]

omit [Fintype G] [SMulDistribClass G A M] in

theorem descent_of_invariant_dual_basis {n : ℕ} (v : Fin n → M) (f : Fin n → M →ₗ[A] A)
    (hv : ∀ i (g : G), g • v i = v i) (hf : ∀ i (g : G) m, f i (g • m) = g • f i m)
    (hfv : ∀ m, ∑ i, f i m • v i = m) :
    IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype ∧
      Module.Finite B (Representation.ofDistribMulAction B G M).invariants ∧
      Module.Projective B (Representation.ofDistribMulAction B G M).invariants := by
  set I := (Representation.ofDistribMulAction B G M).invariants
  let v' : Fin n → I := fun i ↦ ⟨v i, hv i⟩
  let f' : Fin n → I →ₗ[B] B := fun i ↦ (invariantsRingEquiv G B A).symm.toLinearMap ∘ₗ
    invariantsMap _ _ ((f i).restrictScalars B) (hf i)
  have hf' : ∀ i x, algebraMap B A (f' i x) = f i x := fun i x ↦
    algebraMap_invariantsRingEquiv_symm G B A _
  have hfv' : ∀ x, ∑ i, f' i x • v' i = x := fun x ↦ Subtype.ext <| by
    conv_rhs => rw [← hfv x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, v', ← hf', algebraMap_smul]
  have hcomp : Fintype.linearCombination B v' ∘ₗ LinearMap.pi f' = LinearMap.id := by
    refine LinearMap.ext fun x ↦ ?_
    simpa [Fintype.linearCombination_apply] using hfv' x
  refine ⟨?_, ?_, .of_split _ _ hcomp⟩
  · let ψ : M →ₗ[A] A ⊗[B] I := ∑ i, (f i).smulRight (1 ⊗ₜ v' i)
    have hψ : ∀ m, ψ m = ∑ i, f i m • (1 : A) ⊗ₜ[B] v' i := fun m ↦ by
      simp [ψ, LinearMap.sum_apply]
    refine .of_equiv (LinearEquiv.ofLinear (I.subtype.liftBaseChange A) ψ ?_ ?_) fun x ↦
      (LinearMap.liftBaseChange_tmul A I.subtype 1 x).trans (one_smul _ _)
    · refine LinearMap.ext fun m ↦ ?_
      simpa [hψ, v'] using hfv m
    · ext x
      change ψ (I.subtype.liftBaseChange A (1 ⊗ₜ x)) = 1 ⊗ₜ x
      rw [LinearMap.liftBaseChange_tmul, one_smul, Submodule.subtype_apply, hψ]
      conv_rhs => rw [← hfv' x]
      simp [TensorProduct.tmul_sum, ← hf']
  · refine .of_surjective (Fintype.linearCombination B v') fun x ↦ ⟨_, LinearMap.congr_fun hcomp x⟩

end DualBasis

section TameDescent

variable {G : Type*} [Group G] [Finite G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]
  (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]

theorem tame_descent [Module.Finite A M] [Module.Projective A M]
    (h : ∀ P : Ideal A, P.IsMaximal → (Nat.card (P.inertia G) : A) ∉ P)
    (hM : ∀ P : Ideal A, P.IsMaximal → ∀ g ∈ P.inertia G, ∀ m : M,
      g • m - m ∈ P • (⊤ : Submodule A M)) :
    IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype ∧
      Module.Finite B (Representation.ofDistribMulAction B G M).invariants ∧
      Module.Projective B (Representation.ofDistribMulAction B G M).invariants := by
  cases nonempty_fintype G
  obtain ⟨c, hc⟩ := exists_sum_smul_eq_one G A h
  obtain ⟨n, v, f, hv, hf, hfv⟩ := exists_invariant_dual_basis hc (span_fixed_eq_top h hM)
  exact descent_of_invariant_dual_basis B v f hv hf hfv

open scoped Pointwise in

theorem tame_descent_of_stabilizer [Module.Finite A M] [Module.Projective A M]
    (h : ∀ P : Ideal A, P.IsMaximal → (Nat.card (MulAction.stabilizer G P) : A) ∉ P)
    (hM : ∀ P : Ideal A, P.IsMaximal → ∀ g ∈ MulAction.stabilizer G P, ∀ m : M,
      g • m - m ∈ P • (⊤ : Submodule A M)) :
    IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype ∧
      Module.Finite B (Representation.ofDistribMulAction B G M).invariants ∧
      Module.Projective B (Representation.ofDistribMulAction B G M).invariants := by
  refine tame_descent B M (fun P hP hmem ↦ h P hP ?_)
    fun P hP g hg ↦ hM P hP g (Ideal.inertia_le_stabilizer P hg)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (Ideal.inertia_le_stabilizer (M := G) P)
  rw [hk, Nat.cast_mul]
  exact P.mul_mem_right _ hmem

omit [Finite G] [MulSemiringAction G A] [SMulCommClass G B A] [FaithfulSMul B A]
  [Algebra.IsInvariant B A G] [SMulDistribClass G A M] in

theorem bijective_liftBaseChange_of_isBaseChange
    (h : IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype) :
    Function.Bijective
      ((Representation.ofDistribMulAction B G M).invariants.subtype.liftBaseChange A) := by
  have : (Representation.ofDistribMulAction B G M).invariants.subtype.liftBaseChange A =
      h.equiv.toLinearMap := by
    ext x
    simp
  rw [this]
  exact h.equiv.bijective

end TameDescent

section Free

variable {G : Type*} [Group G] {A : Type*} [CommRing A] [MulSemiringAction G A]

theorem sum_smul_sum_smul_eq [Fintype G] {M : Type*} [AddCommGroup M] [Module A M]
    [DistribMulAction G M] [SMulDistribClass G A M] {s : Finset (A × A)}
    (hs : ∀ g : G, g ≠ 1 → ∑ p ∈ s, p.1 * g • p.2 = 0) (hs' : ∑ p ∈ s, p.1 * p.2 = 1) (m : M) :
    ∑ p ∈ s, p.1 • ∑ g : G, g • (p.2 • m) = m := by
  rw [sum_smul_sum_smul, Finset.sum_eq_single 1 (fun g _ hg ↦ by rw [hs g hg, zero_smul])
    (by simp)]
  simp [hs']

theorem exists_sum_smul_eq_one_of_free [Fintype G] (h : IsFreeRingAction G A) :
    ∃ c : A, ∑ g : G, g • c = 1 :=
  exists_sum_smul_eq_one G A fun P hP ↦ by
    rw [(isFreeRingAction_iff_inertia_eq_bot G A).mp h P hP]
    simpa using (Ideal.ne_top_iff_one P).mp hP.ne_top

variable [Finite G] (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]

theorem finite_and_projective (h : IsFreeRingAction G A) :
    Module.Finite B A ∧ Module.Projective B A := by
  cases nonempty_fintype G
  obtain ⟨s, hs, hs'⟩ := exists_galois_coordinates h
  have hcomp : Fintype.linearCombination B (fun p : s ↦ p.1.1) ∘ₗ
      LinearMap.pi (fun p : s ↦ ringTrace G B A ∘ₗ LinearMap.mulLeft B p.1.2) = LinearMap.id := by
    refine LinearMap.ext fun a ↦ ?_
    have := sum_smul_sum_smul_eq hs hs' a
    rw [← Finset.sum_coe_sort] at this
    simpa [Fintype.linearCombination_apply, Algebra.smul_def, mul_comm] using this
  exact ⟨.of_surjective (Fintype.linearCombination B (fun p : s ↦ p.1.1)) fun x ↦ ⟨_, LinearMap.congr_fun hcomp x⟩, .of_split _ _ hcomp⟩

theorem faithfullyFlat (h : IsFreeRingAction G A) : Module.FaithfullyFlat B A :=
  haveI := (finite_and_projective B h).1
  haveI := (finite_and_projective B h).2
  .of_comap_surjective (Algebra.IsIntegral.comap_surjective B A)

theorem bijective_galoisMap (h : IsFreeRingAction G A) :
    Function.Bijective (galoisMap G A B) := by
  classical
  cases nonempty_fintype G
  obtain ⟨s, hs, hs'⟩ := exists_galois_coordinates h
  constructor
  · have key : ∀ z : A ⊗[B] A,
        ∑ p ∈ s, (∑ g : G, g • p.2 * galoisMap G A B z g) ⊗ₜ[B] p.1 = z := by
      intro z
      induction z with
      | zero => simp
      | add x y hx hy =>
        simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.add_tmul,
          hx, hy]
      | tmul a b =>
        conv_rhs => rw [← sum_smul_sum_smul_eq hs hs' b, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [← algebraMap_ringTrace G B A, smul_eq_mul, mul_comm, ← Algebra.smul_def,
          ← TensorProduct.smul_tmul, Algebra.smul_def, algebraMap_ringTrace, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun g _ ↦ ?_
        simp only [galoisMap_tmul, smul_eq_mul, smul_mul']
        ring
    intro x y hxy
    rw [← key x, ← key y, hxy]
  · intro f
    refine ⟨∑ k : G, f k • ∑ p ∈ s, p.1 ⊗ₜ (k⁻¹ • p.2), funext fun g ↦ ?_⟩
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, galoisMap_tmul, smul_smul,
      smul_eq_mul]
    rw [Finset.sum_eq_single g (fun k _ hk ↦ by
      rw [hs _ (fun h ↦ hk (mul_inv_eq_one.mp h).symm), mul_zero]) (by simp)]
    simp [hs']

noncomputable def galoisEquiv (h : IsFreeRingAction G A) : A ⊗[B] A ≃ₐ[A] (G → A) :=
  AlgEquiv.ofBijective _ (bijective_galoisMap B h)

@[simp] theorem galoisEquiv_tmul (h : IsFreeRingAction G A) (a b : A) (g : G) :
    galoisEquiv B h (a ⊗ₜ b) g = a * g • b := rfl

theorem etale (h : IsFreeRingAction G A) : Algebra.Etale B A :=
  haveI := faithfullyFlat B h
  haveI : Algebra.Etale A (A ⊗[B] A) := .of_equiv (galoisEquiv B h).symm
  Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat A

theorem rankAtStalk_eq_card (h : IsFreeRingAction G A) (p : PrimeSpectrum B) :
    Module.rankAtStalk A p = Nat.card G := by
  cases nonempty_fintype G
  haveI := (finite_and_projective B h).1
  haveI := (finite_and_projective B h).2
  obtain ⟨q, rfl⟩ := Algebra.IsIntegral.comap_surjective B A p
  haveI : Nontrivial A := q.nontrivial
  rw [← Module.rankAtStalk_baseChange,
    Module.rankAtStalk_eq_of_equiv (galoisEquiv B h).toLinearEquiv,
    Module.rankAtStalk_eq_finrank_of_free]
  simp

variable (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]

theorem isBaseChange_invariants (h : IsFreeRingAction G A) :
    IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype := by
  cases nonempty_fintype G
  obtain ⟨s, hs, hs'⟩ := exists_galois_coordinates h
  set I := (Representation.ofDistribMulAction B G M).invariants
  have hb : Function.Bijective (I.subtype.liftBaseChange A) := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun m ↦ ∑ p ∈ s, p.1 ⊗ₜ[B] moduleTrace G B M (p.2 • m), fun z ↦ ?_, fun m ↦ ?_⟩
    · induction z with
      | zero => simp
      | add x y hx hy =>
        simp only [map_add, smul_add, TensorProduct.tmul_add, Finset.sum_add_distrib] at hx hy ⊢
        rw [hx, hy]
      | tmul a x =>
        conv_rhs => rw [← sum_smul_sum_smul_eq hs hs' a, TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [← algebraMap_ringTrace G B A, smul_eq_mul, mul_comm, ← Algebra.smul_def,
          TensorProduct.smul_tmul]
        congr 1
        refine Subtype.ext ?_
        have hx : ∀ g : G, g • (x : M) = x := x.2
        rw [Submodule.coe_smul, ← algebraMap_smul A (ringTrace G B A _), algebraMap_ringTrace,
          Finset.sum_smul]
        simp [smul_distrib_smul, hx, mul_smul]
    · simpa using sum_smul_sum_smul_eq hs hs' m
  exact .of_equiv (LinearEquiv.ofBijective _ hb) fun x ↦
    (LinearMap.liftBaseChange_tmul A I.subtype 1 x).trans (one_smul _ _)

theorem finite_invariants_iff (h : IsFreeRingAction G A) :
    Module.Finite B (Representation.ofDistribMulAction B G M).invariants ↔ Module.Finite A M := by
  have hb := isBaseChange_invariants B M h
  haveI := faithfullyFlat B h
  refine ⟨fun _ ↦ .equiv hb.equiv, fun _ ↦ ?_⟩
  haveI := Module.Finite.equiv hb.equiv.symm
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat A

theorem finite_projective_invariants_iff (h : IsFreeRingAction G A) :
    (Module.Finite B (Representation.ofDistribMulAction B G M).invariants ∧
      Module.Projective B (Representation.ofDistribMulAction B G M).invariants) ↔
    (Module.Finite A M ∧ Module.Projective A M) := by
  have hb := isBaseChange_invariants B M h
  refine ⟨fun ⟨_, _⟩ ↦ ⟨.equiv hb.equiv, .of_equiv' hb.equiv⟩, fun ⟨_, _⟩ ↦ ?_⟩
  have hi := (isFreeRingAction_iff_inertia_eq_bot G A).mp h
  refine (tame_descent (A := A) B M (fun P hP ↦ ?_) fun P hP g hg m ↦ ?_).2
  · rw [hi P hP]
    simpa using (Ideal.ne_top_iff_one P).mp hP.ne_top
  · rw [hi P hP, Subgroup.mem_bot] at hg
    simp [hg]

end Free

section FullyFaithful

variable {G : Type*} [Group G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  {B : Type*} [CommRing B] [Algebra B A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]
  {N : Type*} [AddCommGroup N] [Module A N] [DistribMulAction G N] [SMulDistribClass G A N]
  [Module B N] [IsScalarTower B A N] [SMulCommClass G B N]

theorem existsUnique_equivariant_extension
    (hb : IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype)
    (φ : (Representation.ofDistribMulAction B G M).invariants →ₗ[B]
      (Representation.ofDistribMulAction B G N).invariants) :
    ∃! f : M →ₗ[A] N, (∀ (g : G) m, f (g • m) = g • f m) ∧
      ∀ x : (Representation.ofDistribMulAction B G M).invariants, f x = φ x := by
  have hf := hb.lift_eq ((Representation.ofDistribMulAction B G N).invariants.subtype ∘ₗ φ)
  refine ⟨hb.lift (Submodule.subtype _ ∘ₗ φ), ⟨fun g m ↦ ?_, hf⟩, fun f' hf' ↦
    hb.algHom_ext _ _ fun x ↦ (hf'.2 x).trans (hf x).symm⟩
  induction m using hb.inductionOn with
  | zero => simp
  | tmul x =>
    have hx : g • (Submodule.subtype _ x : M) = Submodule.subtype _ x := x.2 g
    rw [hx, hf]
    exact ((φ x).2 g).symm
  | smul a m hm => simp only [smul_distrib_smul g a, LinearMap.map_smul, hm]
  | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]

end FullyFaithful

section BaseChange

variable (G : Type*) [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
  (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass B G A]
  (N : Type*) [AddCommGroup N] [Module B N]

instance smulDistribClass_tensorProduct : SMulDistribClass G A (A ⊗[B] N) where
  smul_distrib_smul g a z := by
    induction z with
    | zero => simp
    | add x y hx hy => simp only [smul_add, hx, hy]
    | tmul b n => simp only [TensorProduct.smul_tmul', smul_eq_mul, smul_mul']

variable [SMulCommClass G B A]

noncomputable def toInvariantsTensor :
    N →ₗ[B] (Representation.ofDistribMulAction B G (A ⊗[B] N)).invariants :=
  (TensorProduct.mk B A N 1).codRestrict
    (Representation.ofDistribMulAction B G (A ⊗[B] N)).invariants fun n g ↦ by
      change g • ((1 : A) ⊗ₜ[B] n) = 1 ⊗ₜ[B] n
      rw [TensorProduct.smul_tmul', smul_one]

@[simp] theorem coe_toInvariantsTensor (n : N) :
    (toInvariantsTensor G A B N n : A ⊗[B] N) = 1 ⊗ₜ n := rfl

variable [FaithfulSMul B A] [Algebra.IsInvariant B A G]

variable {G A} in

theorem bijective_toInvariantsTensor_of_sum_eq_one [Fintype G] {c : A}
    (hc : ∑ g : G, g • c = 1) : Function.Bijective (toInvariantsTensor G A B N) := by
  let τ : A ⊗[B] N →ₗ[B] N := (TensorProduct.lid B N).toLinearMap ∘ₗ (ringTrace G B A).rTensor N
  have hτ : ∀ z : A ⊗[B] N, (1 : A) ⊗ₜ[B] τ z = ∑ g : G, g • z := by
    intro z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy, smul_add,
        Finset.sum_add_distrib]
    | tmul a n =>
      simp only [τ, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
        TensorProduct.lid_tmul, TensorProduct.smul_tmul']
      rw [← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, algebraMap_ringTrace,
        TensorProduct.sum_tmul]
  have h1 : ringTrace G B A c = 1 :=
    FaithfulSMul.algebraMap_injective B A (by rw [algebraMap_ringTrace, hc, map_one])
  refine Function.bijective_iff_has_inverse.mpr ⟨fun z ↦ τ (c • z.1), fun n ↦ ?_, fun z ↦ ?_⟩
  · simp [τ, TensorProduct.smul_tmul', h1]
  · refine Subtype.ext ?_
    have hz : ∀ g : G, g • z.1 = z.1 := z.2
    rw [coe_toInvariantsTensor, hτ]
    simp only [smul_distrib_smul, hz]
    rw [← Finset.sum_smul, hc, one_smul]

variable {G A} in

theorem bijective_toInvariantsTensor [Finite G] (h : IsFreeRingAction G A) :
    Function.Bijective (toInvariantsTensor G A B N) := by
  cases nonempty_fintype G
  obtain ⟨c, hc⟩ := exists_sum_smul_eq_one_of_free h
  exact bijective_toInvariantsTensor_of_sum_eq_one B N hc

end BaseChange

end FreeQuotient

universe w v u

open CategoryTheory

structure SemilinearModule (G : Type v) [Group G] (A : Type u) [CommRing A]
    [MulSemiringAction G A] where

  carrier : Type w
  [addCommGroup : AddCommGroup carrier]
  [module : Module A carrier]
  [action : DistribMulAction G carrier]
  [semilinear : SMulDistribClass G A carrier]

namespace SemilinearModule

attribute [instance] addCommGroup module action semilinear

variable (G : Type v) [Group G] (A : Type u) [CommRing A] [MulSemiringAction G A]

def self : SemilinearModule.{u} G A := ⟨A⟩

instance : Category (SemilinearModule.{w} G A) where
  Hom M N := {f : M.carrier →ₗ[A] N.carrier // ∀ (g : G) m, f (g • m) = g • f m}
  id _ := ⟨LinearMap.id, fun _ _ ↦ rfl⟩
  comp f f' := ⟨f'.1 ∘ₗ f.1, fun g m ↦ by
    rw [LinearMap.comp_apply, f.2, f'.2, LinearMap.comp_apply]⟩

instance smulCommClass_fixedSubring' : SMulCommClass (FixedPoints.subring A G) G A :=
  .symm _ _ _

noncomputable def baseChange (N : Type w) [AddCommGroup N] [Module (FixedPoints.subring A G) N] :
    SemilinearModule.{max w u} G A :=
  ⟨A ⊗[FixedPoints.subring A G] N⟩

noncomputable def invariantsFunctor :
    SemilinearModule.{w} G A ⥤ ModuleCat.{w} (FixedPoints.subring A G) where
  obj M := ModuleCat.of _
    (Representation.ofDistribMulAction (FixedPoints.subring A G) G M.carrier).invariants
  map f := ModuleCat.ofHom (invariantsMap _ _ (f.1.restrictScalars _) f.2)

variable {G A}

theorem invariantsFunctor_faithful [Finite G] (h : IsFreeRingAction G A) :
    (invariantsFunctor.{w} G A).Faithful where
  map_injective {M N} f f' hff' := Subtype.ext <|
    (FreeQuotient.isBaseChange_invariants (FixedPoints.subring A G) M.carrier h).algHom_ext _ _
      fun x ↦ congrArg Subtype.val (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hff') x)

theorem invariantsFunctor_full [Finite G] (h : IsFreeRingAction G A) :
    (invariantsFunctor.{w} G A).Full where
  map_surjective {M N} φ := by
    obtain ⟨f, ⟨hf, hf'⟩, -⟩ := FreeQuotient.existsUnique_equivariant_extension
      (FreeQuotient.isBaseChange_invariants (FixedPoints.subring A G) M.carrier h) φ.hom
    exact ⟨⟨f, hf⟩, ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext (hf' x))⟩

theorem invariantsFunctor_essSurj [Finite G] (h : IsFreeRingAction G A) :
    (invariantsFunctor.{max w u} G A).EssSurj where
  mem_essImage N := ⟨baseChange.{max w u} G A N, ⟨(LinearEquiv.ofBijective _
    (FreeQuotient.bijective_toInvariantsTensor (FixedPoints.subring A G) N h)).symm.toModuleIso⟩⟩

theorem invariantsFunctor_isEquivalence [Finite G] (h : IsFreeRingAction G A) :
    (invariantsFunctor.{max w u} G A).IsEquivalence where
  faithful := invariantsFunctor_faithful h
  full := invariantsFunctor_full h
  essSurj := invariantsFunctor_essSurj.{w} h

end SemilinearModule

theorem isFreeRingAction_arrow (G R : Type*) [Group G] [Finite G] [CommRing R]
    [MulSemiringAction G (G → R)] (hact : ∀ (g : G) (f : G → R) (x : G), (g • f) x = f (g⁻¹ * x)) :
    IsFreeRingAction G (G → R) := by
  classical
  cases nonempty_fintype G
  intro g hg
  rw [Ideal.eq_top_iff_one, ← Finset.univ_sum_single (1 : G → R)]
  refine Ideal.sum_mem _ fun x _ ↦ ?_
  have : (Pi.single x ((1 : G → R) x) : G → R) =
      Pi.single x 1 * (g • (Pi.single (g⁻¹ * x) 1 : G → R) - Pi.single (g⁻¹ * x) 1) := by
    funext y
    by_cases hy : y = x
    · subst hy
      have : y ≠ g⁻¹ * y := fun h ↦ hg (by simpa using h)
      simp [hact, this]
    · simp [hy]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

@[instance_reducible]
def translationAction (G R : Type*) [Group G] [CommRing R] : MulSemiringAction G (G → R) where
  smul g f := fun x ↦ f (g⁻¹ * x)
  one_smul f := funext fun x ↦ by
    change f (1⁻¹ * x) = f x
    rw [inv_one, one_mul]
  mul_smul g h f := funext fun x ↦ by
    change f ((g * h)⁻¹ * x) = f (h⁻¹ * (g⁻¹ * x))
    rw [mul_inv_rev, mul_assoc]
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

theorem isFreeRingAction_translationAction (G R : Type*) [Group G] [Finite G] [CommRing R] :
    letI := translationAction G R
    IsFreeRingAction G (G → R) :=
  letI := translationAction G R
  isFreeRingAction_arrow G R fun _ _ _ ↦ rfl

theorem free_action_etale_and_descent (G : Type v) [Group G] [Finite G]
    (A : Type u) [CommRing A] [MulSemiringAction G A] :
    (IsFreeRingAction G A →
      Module.Finite (FixedPoints.subring A G) A ∧ Algebra.Etale (FixedPoints.subring A G) A ∧
      Module.Projective (FixedPoints.subring A G) A ∧
      Module.FaithfullyFlat (FixedPoints.subring A G) A ∧
      (∀ p : PrimeSpectrum (FixedPoints.subring A G), Module.rankAtStalk A p = Nat.card G) ∧
      (∃ e : A ⊗[FixedPoints.subring A G] A ≃ₐ[A] (G → A),
        ∀ (a b : A) (g : G), e (a ⊗ₜ b) g = a * g • b) ∧
      (SemilinearModule.invariantsFunctor.{max w u} G A).IsEquivalence ∧
      (∀ (M : Type w) [AddCommGroup M] [Module A M] [DistribMulAction G M]
        [SMulDistribClass G A M],
        Function.Bijective ((Representation.ofDistribMulAction
          (FixedPoints.subring A G) G M).invariants.subtype.liftBaseChange A) ∧
        ((Module.Finite (FixedPoints.subring A G)
            (Representation.ofDistribMulAction (FixedPoints.subring A G) G M).invariants ∧
          Module.Projective (FixedPoints.subring A G)
            (Representation.ofDistribMulAction (FixedPoints.subring A G) G M).invariants) ↔
          (Module.Finite A M ∧ Module.Projective A M))) ∧
      ∀ (N : Type w) [AddCommGroup N] [Module (FixedPoints.subring A G) N],
        Function.Bijective (FreeQuotient.toInvariantsTensor G A (FixedPoints.subring A G) N)) ∧
    ∀ (M : Type w) [AddCommGroup M] [Module A M] [DistribMulAction G M]
      [SMulDistribClass G A M] [Module.Finite A M] [Module.Projective A M],
      (∀ P : Ideal A, P.IsMaximal → (Nat.card (P.inertia G) : A) ∉ P) →
      (∀ P : Ideal A, P.IsMaximal → ∀ g ∈ P.inertia G, ∀ m : M,
        g • m - m ∈ P • (⊤ : Submodule A M)) →
      Function.Bijective ((Representation.ofDistribMulAction
        (FixedPoints.subring A G) G M).invariants.subtype.liftBaseChange A) ∧
      Module.Finite (FixedPoints.subring A G)
        (Representation.ofDistribMulAction (FixedPoints.subring A G) G M).invariants ∧
      Module.Projective (FixedPoints.subring A G)
        (Representation.ofDistribMulAction (FixedPoints.subring A G) G M).invariants := by
  refine ⟨fun h ↦ ⟨(FreeQuotient.finite_and_projective _ h).1, FreeQuotient.etale _ h,
    (FreeQuotient.finite_and_projective _ h).2, FreeQuotient.faithfullyFlat _ h,
    FreeQuotient.rankAtStalk_eq_card _ h,
    ⟨FreeQuotient.galoisEquiv _ h, FreeQuotient.galoisEquiv_tmul _ h⟩,
    SemilinearModule.invariantsFunctor_isEquivalence.{w} h,
    fun M _ _ _ _ ↦ ⟨FreeQuotient.bijective_liftBaseChange_of_isBaseChange _ M
      (FreeQuotient.isBaseChange_invariants _ M h),
      FreeQuotient.finite_projective_invariants_iff _ M h⟩,
    fun N _ _ ↦ FreeQuotient.bijective_toInvariantsTensor _ N h⟩, fun M _ _ _ _ _ _ h hM ↦ ?_⟩
  obtain ⟨h1, h2⟩ := FreeQuotient.tame_descent (FixedPoints.subring A G) M h hM
  exact ⟨FreeQuotient.bijective_liftBaseChange_of_isBaseChange _ M h1, h2⟩

end GlobalTheory

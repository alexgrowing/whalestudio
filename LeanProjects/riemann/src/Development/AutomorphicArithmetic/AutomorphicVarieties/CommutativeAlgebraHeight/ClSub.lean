import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsNoetherianRingOfIsAdicComplete

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem exists_subalgebra_of_residue_constants (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R]
    [IsLocalRing R] :
    ∃ S : Subalgebra O R, ∀ c, c ∈ S ↔ ∃ a : O, c - algebraMap O R a ∈ maximalIdeal R := by
  refine ⟨{ carrier := {c | ∃ a : O, c - algebraMap O R a ∈ maximalIdeal R}
            mul_mem' := ?_, one_mem' := ?_, add_mem' := ?_, zero_mem' := ?_,
            algebraMap_mem' := ?_ }, fun c => Iff.rfl⟩
  · rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    have e : x * y - algebraMap O R (a * b)
        = (x - algebraMap O R a) * y + algebraMap O R a * (y - algebraMap O R b) := by
      rw [map_mul]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb)
  · exact ⟨1, by simp⟩
  · rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have e : x + y - algebraMap O R (a + b)
        = (x - algebraMap O R a) + (y - algebraMap O R b) := by
      rw [map_add]; ring
    rw [e]
    exact Ideal.add_mem _ ha hb
  · exact ⟨0, by simp⟩
  · intro a
    exact ⟨a, by simp⟩

private theorem maximalIdeal_mem_residue_constant_subalgebra (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R]
    [IsLocalRing R] (S : Subalgebra O R)
    (hS : ∀ c, c ∈ S ↔ ∃ a : O, c - algebraMap O R a ∈ maximalIdeal R)
    (x : R) (hx : x ∈ maximalIdeal R) : x ∈ S :=
  (hS x).2 ⟨0, by simpa using hx⟩

private theorem residue_constant_subalgebra_isUnit_iff (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R]
    [IsLocalRing R] [IsLocalHom (algebraMap O R)] (S : Subalgebra O R)
    (hS : ∀ c, c ∈ S ↔ ∃ a : O, c - algebraMap O R a ∈ maximalIdeal R)
    (c : S) : IsUnit c ↔ (c : R) ∉ maximalIdeal R := by
  constructor
  · intro hc hm
    have : IsUnit (c : R) := hc.map S.val
    exact (IsLocalRing.mem_maximalIdeal _).1 hm this
  · intro hc
    obtain ⟨a, ha⟩ := (hS c).1 c.2
    have hu : IsUnit (c : R) := by
      by_contra h
      exact hc ((IsLocalRing.mem_maximalIdeal _).2 h)
    have ha' : IsUnit (algebraMap O R a) := by
      by_contra h
      have h1 : algebraMap O R a ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h
      apply hc
      have e : (c : R) = (c - algebraMap O R a) + algebraMap O R a := by ring
      rw [e]
      exact Ideal.add_mem _ ha h1
    have hau : IsUnit a := IsUnit.of_map (algebraMap O R) a ha'
    obtain ⟨u, hu'⟩ := hu
    obtain ⟨v, hv⟩ := hau
    have hmem : (↑u⁻¹ : R) ∈ S := by
      refine (hS _).2 ⟨↑v⁻¹, ?_⟩
      have e : (↑u⁻¹ : R) - algebraMap O R ↑v⁻¹
          = (↑u⁻¹ : R) * algebraMap O R ↑v⁻¹ * (algebraMap O R a - (c : R)) := by
        have h1 : (↑u⁻¹ : R) * (c : R) = 1 := by rw [← hu']; simp
        have h2 : algebraMap O R ↑v⁻¹ * algebraMap O R a = 1 := by
          rw [← map_mul, ← hv]; simp
        linear_combination algebraMap O R ↑v⁻¹ * h1 - (↑u⁻¹ : R) * h2
      rw [e]
      apply Ideal.mul_mem_left
      have : algebraMap O R a - (c : R) = -((c : R) - algebraMap O R a) := by ring
      rw [this]
      exact (Ideal.neg_mem_iff _).2 ha
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    simp [← hu']

private theorem residue_constant_subalgebra_isLocalRing (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R]
    [IsLocalRing R] [IsLocalHom (algebraMap O R)] (S : Subalgebra O R)
    (hS : ∀ c, c ∈ S ↔ ∃ a : O, c - algebraMap O R a ∈ maximalIdeal R) :
    IsLocalRing S := by
  haveI : Nontrivial S := ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff, residue_constant_subalgebra_isUnit_iff O R S hS, not_not] at ha hb ⊢
  simpa using Ideal.add_mem _ ha hb

private theorem residue_constant_subalgebra_mem_maximalIdeal_iff (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R]
    [IsLocalRing R] [IsLocalHom (algebraMap O R)] (S : Subalgebra O R)
    (hS : ∀ c, c ∈ S ↔ ∃ a : O, c - algebraMap O R a ∈ maximalIdeal R) [IsLocalRing S]
    (c : S) : c ∈ maximalIdeal S ↔ (c : R) ∈ maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, residue_constant_subalgebra_isUnit_iff O R S hS, not_not]

private theorem residue_constant_subalgebra_mem_maximalIdeal_pow_iff (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R]
    [IsLocalRing R] [IsLocalHom (algebraMap O R)] (S : Subalgebra O R)
    (hS : ∀ c, c ∈ S ↔ ∃ a : O, c - algebraMap O R a ∈ maximalIdeal R) [IsLocalRing S]
    (N : ℕ) (c : S) : c ∈ maximalIdeal S ^ N ↔ (c : R) ∈ maximalIdeal R ^ N := by
  constructor
  · intro hc
    have h1 : Ideal.map S.val.toRingHom (maximalIdeal S) ≤ maximalIdeal R := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact (residue_constant_subalgebra_mem_maximalIdeal_iff O R S hS x).1 hx
    have h2 := Ideal.mem_map_of_mem S.val.toRingHom hc
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 N h2
  · induction N generalizing c with
    | zero => intro _; simp
    | succ n ih =>
      intro hc
      rcases n with _ | n
      · simpa [residue_constant_subalgebra_mem_maximalIdeal_iff O R S hS] using hc
      · rw [pow_succ'] at hc ⊢
        have key : ∀ x : R, x ∈ maximalIdeal R * maximalIdeal R ^ (n + 1) →
            ∃ hx : x ∈ S, (⟨x, hx⟩ : S) ∈ maximalIdeal S * maximalIdeal S ^ (n + 1) := by
          intro x hx
          refine Submodule.mul_induction_on hx ?_ ?_
          · intro i hi j hj
            have hjm : j ∈ maximalIdeal R := Ideal.pow_le_self (Nat.succ_ne_zero n) hj
            have hiS := maximalIdeal_mem_residue_constant_subalgebra O R S hS i hi
            have hjS := maximalIdeal_mem_residue_constant_subalgebra O R S hS j hjm
            refine ⟨S.mul_mem hiS hjS, ?_⟩
            have : (⟨i * j, S.mul_mem hiS hjS⟩ : S) = ⟨i, hiS⟩ * ⟨j, hjS⟩ := rfl
            rw [this]
            exact Ideal.mul_mem_mul ((residue_constant_subalgebra_mem_maximalIdeal_iff O R S hS _).2 hi) (ih ⟨j, hjS⟩ hj)
          · rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
            exact ⟨S.add_mem hx hy, Ideal.add_mem _ hx' hy'⟩
        obtain ⟨_, h⟩ := key _ hc
        exact h

private theorem residue_constant_subalgebra_module_finite (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R]
    [IsLocalRing R] [Module.Finite O (ResidueField R)] (S : Subalgebra O R)
    (hS : ∀ c, c ∈ S ↔ ∃ a : O, c - algebraMap O R a ∈ maximalIdeal R) :
    Module.Finite S R := by
  classical
  obtain ⟨s, hs⟩ := Module.finite_def.1 (inferInstance : Module.Finite O (ResidueField R))
  let g := Function.surjInv (IsLocalRing.residue_surjective (R := R))
  have hg : ∀ z, IsLocalRing.residue R (g z) = z := Function.surjInv_eq _
  refine ⟨⟨insert 1 (s.image g), ?_⟩⟩
  rw [eq_top_iff]
  intro x _
  let f := (IsScalarTower.toAlgHom O R (ResidueField R)).toLinearMap
  have hf : ∀ r, f r = IsLocalRing.residue R r := fun r => rfl
  have hx : IsLocalRing.residue R x ∈ Submodule.map f (Submodule.span O (g '' (s : Set _))) := by
    rw [Submodule.map_span, ← Set.image_comp]
    have : (f ∘ g) '' (s : Set _) = s := by
      ext z; simp [Function.comp, hf, hg]
    rw [this, hs]; trivial
  obtain ⟨y, hy, hxy⟩ := hx
  rw [hf] at hxy
  have hm : x - y ∈ maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hxy, sub_self]
  have hmS := maximalIdeal_mem_residue_constant_subalgebra O R S hS _ hm
  have e : x = (⟨x - y, hmS⟩ : S) • (1 : R) + y := by
    rw [Subalgebra.smul_def]; simp
  rw [e]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))) ?_
  have hle : Submodule.span O (g '' (s : Set _))
      ≤ (Submodule.span S (↑(insert 1 (s.image g)) : Set R)).restrictScalars O := by
    refine le_trans (Submodule.span_le_restrictScalars O S _) ?_
    exact Submodule.restrictScalars_mono O (Submodule.span_mono (by simp [Set.subset_insert]))
  exact hle hy

private theorem isNoetherian_of_finite_torsion_by_maximalIdeal (A : Type) [CommRing A] [IsLocalRing A] (P : Type) [AddCommGroup P]
    [Module A P] [Module.Finite A P]
    (h : Module.IsTorsionBySet A P (maximalIdeal A : Set A)) : IsNoetherian A P := by
  letI : Module (A ⧸ maximalIdeal A) P := h.module
  haveI : IsScalarTower A (A ⧸ maximalIdeal A) P := h.isScalarTower
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  haveI : Module.Finite (A ⧸ maximalIdeal A) P := Module.Finite.of_restrictScalars_finite A _ _
  haveI : IsNoetherian (A ⧸ maximalIdeal A) P := inferInstance
  refine ⟨fun N => ?_⟩
  let N' : Submodule (A ⧸ maximalIdeal A) P :=
    { carrier := N
      add_mem' := fun hx hy => N.add_mem hx hy
      zero_mem' := N.zero_mem
      smul_mem' := by
        intro c x hx
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        have : (Ideal.Quotient.mk (maximalIdeal A) a) • x = a • x := by
          rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
        rw [this]
        exact N.smul_mem a hx }
  obtain ⟨t, ht⟩ := IsNoetherian.noetherian N'
  refine ⟨t, ?_⟩
  rw [← Submodule.restrictScalars_span A (A ⧸ maximalIdeal A) Ideal.Quotient.mk_surjective, ht]
  rfl

private theorem residue_constant_subalgebra_isNoetherian (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R]
    [IsLocalRing R] [IsLocalHom (algebraMap O R)] [IsNoetherianRing R] (S : Subalgebra O R)
    (hS : ∀ c, c ∈ S ↔ ∃ a : O, c - algebraMap O R a ∈ maximalIdeal R) [IsLocalRing S]
    [Module.Finite S R] : IsNoetherian S R := by
  refine ⟨fun N => ?_⟩
  let J : Submodule R R := Submodule.span R (N : Set R)
  let J' : Submodule S R := J.restrictScalars S
  let L' : Submodule S R := (maximalIdeal R • J).restrictScalars S
  have hJfg : J'.FG := Submodule.FG.restrictScalars (IsNoetherian.noetherian J)
  have hLfg : L'.FG := Submodule.FG.restrictScalars (IsNoetherian.noetherian (maximalIdeal R • J))
  have hNJ : N ≤ J' := by
    intro x hx
    rw [Submodule.restrictScalars_mem]
    exact Submodule.subset_span hx
  have hLJ : L' ≤ J' := by
    intro x hx
    rw [Submodule.restrictScalars_mem] at hx ⊢
    exact Submodule.smul_le_right hx
  have hJm : ∀ j ∈ J, ∀ y ∈ maximalIdeal R, y * j ∈ N := by
    intro j hj
    induction hj using Submodule.span_induction with
    | mem x hx =>
      intro y hy
      have : y * x = (⟨y, maximalIdeal_mem_residue_constant_subalgebra O R S hS y hy⟩ : S) • x := by
        rw [Subalgebra.smul_def, smul_eq_mul]
      rw [this]
      exact N.smul_mem _ hx
    | zero => intro y _; simp
    | add x z _ _ hx hz =>
      intro y hy
      rw [mul_add]
      exact N.add_mem (hx y hy) (hz y hy)
    | smul r x _ hx =>
      intro y hy
      have : y * (r • x) = (y * r) * x := by rw [smul_eq_mul]; ring
      rw [this]
      exact hx _ (Ideal.mul_mem_right _ _ hy)
  have hLN : L' ≤ N := by
    intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro y hy j hj
      rw [smul_eq_mul]
      exact hJm j hj y hy
    · intro x z hx hz
      exact N.add_mem hx hz
  obtain ⟨t, ht⟩ := hJfg
  let K : Submodule S R := Submodule.span S (t : Set R)
  have hKJ : ∀ x ∈ K, x ∈ J := by
    intro x hx
    have : x ∈ J' := by rw [← ht]; exact hx
    rwa [Submodule.restrictScalars_mem] at this
  have hNK : N ≤ K := by
    intro x hx
    have := hNJ hx
    rw [← ht] at this
    exact this
  have hLK : L' ≤ K := by
    intro x hx
    have := hLJ hx
    rw [← ht] at this
    exact this
  haveI : Module.Finite S K := Module.Finite.iff_fg.2 ⟨t, rfl⟩
  let L0 : Submodule S K := L'.comap K.subtype
  let N0 : Submodule S K := N.comap K.subtype
  have hL0fg : L0.FG := by
    refine Submodule.fg_of_fg_map_injective K.subtype Subtype.val_injective ?_
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hLK]
    exact hLfg
  have tors : Module.IsTorsionBySet S (K ⧸ L0) (maximalIdeal S : Set S) := by
    intro p x
    induction p using Submodule.Quotient.induction_on with
    | H j =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      change ((x : S) : R) • (j : R) ∈ (maximalIdeal R • J).restrictScalars S
      rw [Submodule.restrictScalars_mem]
      exact Submodule.smul_mem_smul ((residue_constant_subalgebra_mem_maximalIdeal_iff O R S hS _).1 x.2) (hKJ _ j.2)
  haveI : IsNoetherian S (K ⧸ L0) := isNoetherian_of_finite_torsion_by_maximalIdeal S (K ⧸ L0) tors
  have hN0 : N0.FG := by
    refine Submodule.fg_of_fg_map_of_fg_inf_ker L0.mkQ (IsNoetherian.noetherian _) ?_
    rw [Submodule.ker_mkQ, inf_eq_right.2]
    · exact hL0fg
    · intro x hx
      exact hLN hx
  have e : Submodule.map K.subtype N0 = N := by
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hNK]
  rw [← e]
  exact hN0.map _

private theorem smodEq_ideal_smul_univ_iff_sub_mem (A : Type) [CommRing A] (I : Ideal A) (x y : A) :
    x ≡ y [SMOD I • (⊤ : Submodule A A)] ↔ x - y ∈ I := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

private theorem isAdicComplete_residue_constant_subalgebra (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R]
    [IsLocalRing R] [IsLocalHom (algebraMap O R)] [IsAdicComplete (maximalIdeal R) R]
    (S : Subalgebra O R)
    (hS : ∀ c, c ∈ S ↔ ∃ a : O, c - algebraMap O R a ∈ maximalIdeal R) [IsLocalRing S] :
    IsAdicComplete (maximalIdeal S) S := by
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply Subtype.ext
    refine IsHausdorff.haus' (I := maximalIdeal R) (x : R) (fun n => ?_)
    rw [smodEq_ideal_smul_univ_iff_sub_mem]
    have := hx n
    rw [smodEq_ideal_smul_univ_iff_sub_mem, residue_constant_subalgebra_mem_maximalIdeal_pow_iff O R S hS] at this
    simpa using this
  · intro f hf
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal R) (fun n => (f n : R)) (by
      intro m n hmn
      rw [smodEq_ideal_smul_univ_iff_sub_mem]
      have := hf hmn
      rw [smodEq_ideal_smul_univ_iff_sub_mem, residue_constant_subalgebra_mem_maximalIdeal_pow_iff O R S hS] at this
      simpa using this)
    have h1 : (f 1 : R) - L ∈ maximalIdeal R := by
      have := hL 1
      rw [smodEq_ideal_smul_univ_iff_sub_mem, pow_one] at this
      exact this
    have hLS : L ∈ S := by
      have e : L = (f 1 : R) - ((f 1 : R) - L) := by ring
      rw [e]
      exact S.sub_mem (f 1).2 (maximalIdeal_mem_residue_constant_subalgebra O R S hS _ h1)
    refine ⟨⟨L, hLS⟩, fun n => ?_⟩
    rw [smodEq_ideal_smul_univ_iff_sub_mem, residue_constant_subalgebra_mem_maximalIdeal_pow_iff O R S hS]
    have := hL n
    rw [smodEq_ideal_smul_univ_iff_sub_mem] at this
    simpa using this

theorem UpperTheory.V.CA.cl_sub :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R], IsCL O R → ∃ S : Subalgebra O R, (∀ c, c ∈ S ↔ ∃ a : O, c - algebraMap O R a ∈ maximalIdeal R) ∧ Module.Finite S R ∧ ∃ _ : IsCO O S, ∀ (N : ℕ) (c : S), c ∈ maximalIdeal S ^ N ↔ (c : R) ∈ maximalIdeal R ^ N := by
  intro O _ _ _ _ R _ _ _ hR
  haveI := hR.noeth
  haveI := hR.complete
  haveI := hR.isLocalHom
  haveI := hR.res_fin
  obtain ⟨S, hS⟩ := exists_subalgebra_of_residue_constants O R
  haveI : IsLocalRing S := residue_constant_subalgebra_isLocalRing O R S hS
  haveI : Module.Finite S R := residue_constant_subalgebra_module_finite O R S hS
  haveI : IsNoetherian S R := residue_constant_subalgebra_isNoetherian O R S hS
  haveI : IsNoetherian S S :=
    isNoetherian_of_injective (Algebra.linearMap S R) Subtype.val_injective
  haveI : IsAdicComplete (maximalIdeal S) S := isAdicComplete_residue_constant_subalgebra O R S hS
  refine ⟨S, hS, inferInstance,
    { complete := inferInstance, isLocalHom := ?_, res_surj := ?_ },
    fun N c => residue_constant_subalgebra_mem_maximalIdeal_pow_iff O R S hS N c⟩
  · refine ⟨fun a ha => ?_⟩
    have h1 : IsUnit (algebraMap O R a) := by
      have := ha.map S.val
      simpa using this
    exact IsUnit.of_map _ _ h1
  · intro x
    obtain ⟨a, ha⟩ := (hS x).1 x.2
    exact ⟨a, (residue_constant_subalgebra_mem_maximalIdeal_iff O R S hS _).2 (by simpa using ha)⟩

import Mathlib

open Module

set_option linter.deprecated false

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.MeanA

theorem exists_mul_sub_one_mem_pow {R : Type*} [CommRing R] {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) {t : R}
    (ht : t ∉ 𝔭) (k : ℕ) : ∃ u : R, u * t - 1 ∈ 𝔭 ^ k := by
  obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv ht
  refine ⟨(∑ j ∈ Finset.range k, i ^ j) * y, ?_⟩
  have h1 : (∑ j ∈ Finset.range k, i ^ j) * (i - 1) = i ^ k - 1 := geom_sum_mul i k
  have h2 : (∑ j ∈ Finset.range k, i ^ j) * y * t - 1 = -(i ^ k) := by
    linear_combination (∑ j ∈ Finset.range k, i ^ j) * hyi - h1
  rw [h2]
  exact (𝔭 ^ k).neg_mem (Ideal.pow_mem_pow hi k)

theorem mem_pow_of_mul_mem {R : Type*} [CommRing R] {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) {t c : R}
    (ht : t ∉ 𝔭) {k : ℕ} (h : t * c ∈ 𝔭 ^ k) : c ∈ 𝔭 ^ k := by
  obtain ⟨u, hu⟩ := exists_mul_sub_one_mem_pow h𝔭 ht k
  have e : c = u * (t * c) - (u * t - 1) * c := by ring
  rw [e]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ u h) (Ideal.mul_mem_right c _ hu)

variable {R F V : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F] [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
  [FiniteDimensional F V]

theorem exists_local_basis (M : Submodule R V) (hfg : M.FG)
    (hspan : Submodule.span F (M : Set V) = ⊤) {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) :
    ∃ (x : Fin (finrank F V) → M) (s : R), s ∉ 𝔭 ∧ LinearIndependent R x ∧
      ∀ v : M, s • v ∈ Submodule.span R (Set.range x) := by
  have := h𝔭
  let : Field (R ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have : Module.Finite R M := Module.Finite.iff_fg.2 hfg
  let Q := M ⧸ (𝔭 • ⊤ : Submodule R M)
  have : Module.Finite (R ⧸ 𝔭) Q := Module.Finite.of_restrictScalars_finite R _ _
  let b := Module.finBasis (R ⧸ 𝔭) Q
  choose x hx using fun i => Submodule.Quotient.mk_surjective _ (b i)
  have hli : LinearIndependent F (M.subtype ∘ x) := by
    refine Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial (S := R ⧸ 𝔭) F ?_ M.subtype
      M.injective_subtype (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) ?_
    · rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]; exact h𝔭.ne_top
    · have : (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) ∘ x = b := by
        funext i; exact hx i
      rw [this]; exact b.linearIndependent
  have hsup : (⊤ : Submodule R M) ≤ Submodule.span R (Set.range x) ⊔ 𝔭 • ⊤ := by
    intro v _
    have hv : (Submodule.Quotient.mk v : Q) ∈ Submodule.span (R ⧸ 𝔭) (Set.range b) := b.mem_span _
    rw [← @Submodule.restrictScalars_mem R,
      Submodule.restrictScalars_span R (R ⧸ 𝔭) Ideal.Quotient.mk_surjective] at hv
    have hb : Set.range b = (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) '' Set.range x := by
      rw [← Set.range_comp]; congr 1; funext i; exact (hx i).symm
    rw [hb, ← Submodule.map_span] at hv
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 hv
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq] at e
    have : v = y - (y - v) := by abel
    rw [this]
    exact sub_mem (Submodule.mem_sup_left hy) (Submodule.mem_sup_right e)
  obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (Module.Finite.fg_top (R := R) (M := M)) le_rfl hsup
  have hs𝔭 : s ∉ 𝔭 := fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := sub_mem h hs1; simpa using this))
  have hsv : ∀ v : M, s • v ∈ Submodule.span R (Set.range x) := fun v =>
    hs (Submodule.smul_mem_pointwise_smul v s ⊤ trivial)
  have hs0 : algebraMap R F s ≠ 0 := by
    intro h0
    have : s = 0 := (IsFractionRing.injective R F) (by rw [h0, map_zero])
    exact hs𝔭 (this ▸ 𝔭.zero_mem)
  have hsp : ⊤ ≤ Submodule.span F (Set.range (M.subtype ∘ x)) := by
    rw [← hspan, Submodule.span_le]
    intro v hv
    have h1 := hsv ⟨v, hv⟩
    have h2 : (s • v : V) ∈ Submodule.span F (Set.range (M.subtype ∘ x)) := by
      have h3 : M.subtype (s • ⟨v, hv⟩) ∈ (Submodule.span R (Set.range x)).map M.subtype :=
        Submodule.mem_map_of_mem h1
      rw [Submodule.map_span, ← Set.range_comp] at h3
      exact Submodule.span_le_restrictScalars R F _ h3
    have h4 : v = (algebraMap R F s)⁻¹ • (s • v) := by
      rw [← algebraMap_smul F s v, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [h4]
    exact Submodule.smul_mem _ _ h2
  have hcard : finrank (R ⧸ 𝔭) Q = finrank F V := by
    have := finrank_eq_card_basis (Basis.mk hli hsp)
    simpa using this.symm
  have hliR : LinearIndependent R x := by
    have := hli.restrict_scalars (R := R) (by
      intro a b hab
      simpa [Algebra.smul_def] using hab |> fun h => (IsFractionRing.injective R F) (by simpa [Algebra.smul_def] using h))
    exact LinearIndependent.of_comp M.subtype this
  refine ⟨x ∘ Fin.cast hcard.symm, s, hs𝔭, hliR.comp _ (Fin.cast_injective _), fun v => ?_⟩
  have : Set.range (x ∘ Fin.cast hcard.symm) = Set.range x :=
    (Fin.castOrderIso hcard.symm).surjective.range_comp x
  rw [this]; exact hsv v

theorem card_quot_pow_smul_top (M : Submodule R V) (hfg : M.FG)
    (hspan : Submodule.span F (M : Set V) = ⊤) {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Nat.card (M ⧸ (𝔭 ^ k • ⊤ : Submodule R M)) = Nat.card (R ⧸ 𝔭 ^ k) ^ finrank F V := by
  obtain ⟨x, s, hs, hli, hsx⟩ := exists_local_basis M hfg hspan h𝔭
  let φ : (Fin (finrank F V) → R) →ₗ[R] M :=
    { toFun := fun c => ∑ i, c i • x i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }
  have hφ : ∀ c, φ c = ∑ i, c i • x i := fun c => rfl
  let ψ := (𝔭 ^ k • ⊤ : Submodule R M).mkQ ∘ₗ φ
  have hP : ∀ v ∈ (𝔭 ^ k • ⊤ : Submodule R M), ∃ d : Fin (finrank F V) → R,
      (∀ i, d i ∈ 𝔭 ^ k) ∧ s • v = ∑ i, d i • x i := by
    intro v hv
    refine Submodule.smul_induction_on hv ?_ ?_
    · intro a ha m _
      obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp (hsx m)
      refine ⟨fun i => a * r i, fun i => Ideal.mul_mem_right _ _ ha, ?_⟩
      rw [smul_comm s a m, ← hr, Finset.smul_sum]
      simp only [smul_smul]
    · intro v w hv hw
      obtain ⟨d, hd, hd'⟩ := hv
      obtain ⟨d', hd2, hd2'⟩ := hw
      refine ⟨d + d', fun i => Ideal.add_mem _ (hd i) (hd2 i), ?_⟩
      rw [smul_add, hd', hd2']
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨u, hu⟩ := exists_mul_sub_one_mem_pow h𝔭 hs k
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp (hsx m)
    refine ⟨fun i => u * r i, ?_⟩
    show Submodule.Quotient.mk (φ (fun i => u * r i)) = Submodule.Quotient.mk m
    rw [hφ, Submodule.Quotient.eq]
    have e : ∑ i, (u * r i) • x i - m = (u * s - 1) • m := by
      simp only [mul_smul, ← Finset.smul_sum, hr, sub_smul, one_smul]
    rw [e]
    exact Submodule.smul_mem_smul hu Submodule.mem_top
  have hker : LinearMap.ker ψ = Submodule.pi Set.univ (fun _ => 𝔭 ^ k) := by
    ext c
    rw [LinearMap.mem_ker, Submodule.mem_pi]
    show Submodule.Quotient.mk (φ c) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, hφ]
    constructor
    · intro hc i _
      obtain ⟨d, hd, hsd⟩ := hP _ hc
      have h0 : ∑ i, (s * c i - d i) • x i = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, ← hsd, sub_self]
      have h1 := Fintype.linearIndependent_iff.mp hli _ h0 i
      exact mem_pow_of_mul_mem h𝔭 hs (by rw [sub_eq_zero.mp h1]; exact hd i)
    · intro hc
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem_smul (hc i (Set.mem_univ i)) Submodule.mem_top
  have e := ((LinearMap.quotKerEquivOfSurjective ψ hsurj).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (Submodule.quotientPi (fun _ => 𝔭 ^ k))))
  rw [Nat.card_congr e.toEquiv, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Formalism.HermitianLattices.Ext.L3.MeanA

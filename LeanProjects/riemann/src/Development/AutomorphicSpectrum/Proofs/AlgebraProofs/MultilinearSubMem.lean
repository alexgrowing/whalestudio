import Mathlib

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp.DetMod

theorem multilinear_sub_mem {O V W ι : Type*} [CommRing O] [AddCommGroup V] [Module O V]
    [AddCommGroup W] [Module O W] [Fintype ι] [DecidableEq ι]
    (f : MultilinearMap O (fun _ : ι => V) W) (Λ : Submodule O V) (I : Submodule O W)
    (𝔞 : Ideal O) (hI : ∀ z : ι → V, (∀ i, z i ∈ Λ) → f z ∈ I)
    (x y : ι → V) (hx : ∀ i, x i ∈ Λ) (hxy : ∀ i, y i - x i ∈ 𝔞 • Λ) :
    f y - f x ∈ 𝔞 • I := by
  have hy : ∀ i, y i ∈ Λ := fun i => by
    have h1 : y i - x i ∈ Λ := Submodule.smul_le_right (hxy i)
    simpa using Λ.add_mem h1 (hx i)
  have hupd : ∀ (z : ι → V), (∀ i, z i ∈ Λ) → ∀ i, ∀ w ∈ 𝔞 • Λ,
      f (Function.update z i w) ∈ 𝔞 • I := by
    intro z hz i w hw
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro r hr n hn
      rw [f.map_update_smul]
      refine Submodule.smul_mem_smul hr (hI _ fun j => ?_)
      by_cases h : j = i
      · subst h; simpa using hn
      · simpa [Function.update_of_ne h] using hz j
    · intro a b ha hb
      rw [f.map_update_add]
      exact Submodule.add_mem _ ha hb
  have key : ∀ s : Finset ι, f (s.piecewise y x) - f x ∈ 𝔞 • I := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s his ih =>
      have hz : ∀ j, s.piecewise y x j ∈ Λ := fun j => by
        by_cases h : j ∈ s
        · simpa [h] using hy j
        · simpa [h] using hx j
      have h1 := hupd _ hz i _ (hxy i)
      rw [f.map_update_sub] at h1
      have h2 : Function.update (s.piecewise y x) i (x i) = s.piecewise y x := by
        rw [Function.update_eq_self_iff]; simp [his]
      rw [h2] at h1
      rw [Finset.piecewise_insert]
      simpa using Submodule.add_mem _ h1 ih
  simpa using key Finset.univ

theorem mem_of_smul_le {O K : Type*} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] (I : Submodule O K) (hI : IsFractional (nonZeroDivisors O) I)
    (hI0 : I ≠ ⊥) (𝔞 : Ideal O) (δ : K) (h : ∀ t ∈ I, δ * t ∈ 𝔞 • I) :
    ∃ a ∈ 𝔞, δ = algebraMap O K a := by
  let J : FractionalIdeal (nonZeroDivisors O) K := ⟨I, hI⟩
  have hJ : J ≠ 0 := by
    intro h0
    apply hI0
    have : (J : Submodule O K) = ((0 : FractionalIdeal (nonZeroDivisors O) K) : Submodule O K) := by
      rw [h0]
    rw [FractionalIdeal.coe_zero] at this
    exact this
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors O) δ * J
      ≤ (𝔞 : FractionalIdeal (nonZeroDivisors O) K) * J := by
    rw [FractionalIdeal.spanSingleton_mul_le_iff]
    intro t ht
    refine Submodule.smul_induction_on (p := fun w => w ∈ (𝔞 : FractionalIdeal (nonZeroDivisors O) K) * J) (h t ht) ?_ ?_
    · intro r hr n hn
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hr) hn
    · intro a b ha hb
      exact Submodule.add_mem (((𝔞 : FractionalIdeal (nonZeroDivisors O) K) * J : FractionalIdeal _ _) : Submodule O K) ha hb
  have hle2 := mul_le_mul_left hle J⁻¹
  rw [mul_assoc, mul_assoc, mul_inv_cancel₀ hJ, mul_one, mul_one,
    FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_coeIdeal] at hle2
  obtain ⟨a, ha, rfl⟩ := hle2
  exact ⟨a, ha, rfl⟩

theorem main : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (N : ℕ) (Λ : Submodule O (Fin N → K)) (𝔞 : Ideal O) (γ : Matrix (Fin N) (Fin N) K), Λ.FG → Submodule.span K (Λ : Set (Fin N → K)) = ⊤ → (∀ x ∈ Λ, γ *ᵥ x - x ∈ 𝔞 • Λ) → ∃ a ∈ 𝔞, γ.det = 1 + algebraMap O K a := by
  intro O K _ _ _ _ _ N Λ 𝔞 γ hfg hsp hγ
  let f : MultilinearMap O (fun _ : Fin N => (Fin N → K)) K :=
    (Matrix.detRowAlternating (n := Fin N) (R := K)).toMultilinearMap.restrictScalars O
  have hf : ∀ z, f z = (Matrix.of z).det := fun z => rfl
  let I : Submodule O K := Submodule.span O {t | ∃ z : Fin N → Fin N → K, (∀ i, z i ∈ Λ) ∧ f z = t}
  have hI : ∀ z : Fin N → Fin N → K, (∀ i, z i ∈ Λ) → f z ∈ I :=
    fun z hz => Submodule.subset_span ⟨z, hz, rfl⟩

  obtain ⟨d, hd⟩ : ∃ d : nonZeroDivisors O, ∀ x ∈ Λ, ∀ j,
      IsLocalization.IsInteger O ((d : O) • x j) := by
    obtain ⟨S, rfl⟩ := hfg
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
      (fun p : S × Fin N => (p.1 : Fin N → K) p.2)
    refine ⟨d, fun x hx j => ?_⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact hd (⟨x, hx⟩, j)
    | zero => simpa using IsLocalization.isInteger_zero
    | add x y _ _ hx hy =>
      rw [Pi.add_apply, smul_add]; exact IsLocalization.isInteger_add hx hy
    | smul a x _ hx =>
      rw [Pi.smul_apply, smul_comm]; exact IsLocalization.isInteger_smul hx
  have hfrac : IsFractional (nonZeroDivisors O) I := by
    rw [FractionalIdeal.isFractional_span_iff]
    refine ⟨(d : O) ^ N, pow_mem d.2 N, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    choose m hm using fun i j => hd _ (hz i) j
    refine ⟨(Matrix.of m).det, ?_⟩
    rw [RingHom.map_det, hf, Algebra.smul_def, map_pow]
    have : (algebraMap O K).mapMatrix (Matrix.of m) = algebraMap O K d • Matrix.of z := by
      ext i j
      simp [hm, Algebra.smul_def]
    rw [this, Matrix.det_smul]
    simp
  have hI0 : I ≠ ⊥ := by
    intro h0
    obtain ⟨s, hs, hsp', hli⟩ := exists_linearIndependent K (Λ : Set (Fin N → K))
    rw [hsp] at hsp'
    let b : Module.Basis s K (Fin N → K) := Module.Basis.mk hli (by simp [hsp'])
    let e : s ≃ Fin N := b.indexEquiv (Pi.basisFun K (Fin N))
    let b' := b.reindex e
    have hb' : ∀ i, b' i ∈ Λ := fun i => by
      simp only [b', b, Module.Basis.reindex_apply, Module.Basis.mk_apply]
      exact hs (e.symm i).2
    have h1 := hI b' hb'
    rw [h0, Submodule.mem_bot, hf] at h1
    have h2 : IsUnit (Matrix.of (b' : Fin N → Fin N → K)) :=
      Matrix.linearIndependent_rows_iff_isUnit.mp b'.linearIndependent
    rw [Matrix.isUnit_iff_isUnit_det, h1] at h2
    exact not_isUnit_zero h2
  obtain ⟨a, ha, hδ⟩ := mem_of_smul_le I hfrac hI0 𝔞 (γ.det - 1) (by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      have h1 := multilinear_sub_mem f Λ I 𝔞 hI z (fun i => γ *ᵥ z i) hz (fun i => hγ _ (hz i))
      have h2 : Matrix.of (fun i => γ *ᵥ z i) = Matrix.of z * γᵀ := by
        ext i j
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
      rw [hf, h2, Matrix.det_mul, Matrix.det_transpose, ← hf] at h1
      convert h1 using 1
      ring
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx)
  exact ⟨a, ha, by rw [← hδ]; ring⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.DetMod

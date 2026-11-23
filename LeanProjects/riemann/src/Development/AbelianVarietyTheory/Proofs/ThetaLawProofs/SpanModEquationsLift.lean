import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd

open GlobalTheory.KeyKa

namespace GlobalTheory.SeriesNakayama

theorem mem_pow_smul_top_iff {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] (π : O)
    (n : ℕ) (x : M) :
    x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O M) ↔ ∃ y : M, π ^ n • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem mem_pow_smul_top_pi {O ι : Type*} [CommRing O] (π : O) (n : ℕ) (x : ι → O) :
    x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O (ι → O)) ↔
      ∀ i, x i ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O O) := by
  simp only [mem_pow_smul_top_iff]
  refine ⟨fun ⟨y, hy⟩ i => ⟨y i, congrFun hy i⟩, fun h => ?_⟩
  choose y hy using h
  exact ⟨y, funext hy⟩

theorem surjective_of_mod {O ι κ : Type*} [CommRing O] (π : O)
    [IsAdicComplete (Ideal.span {π}) O] (Φ : (ι → O) →ₗ[O] (κ → O))
    (h : ∀ G : κ → O, ∃ x, ∀ j, G j - Φ x j ∈ Ideal.span {π}) : Function.Surjective Φ := by
  have : IsPrecomplete (Ideal.span {π}) (ι → O) := by
    refine ⟨fun u hu => ?_⟩
    have h1 : ∀ i, ∃ L : O, ∀ k, u k i ≡ L [SMOD (Ideal.span {π} ^ k • ⊤ : Submodule O O)] :=
      fun i => IsPrecomplete.prec' (fun k => u k i) fun {a b} hab =>
        SModEq.sub_mem.2 ((mem_pow_smul_top_pi π a _).1 (SModEq.sub_mem.1 (hu hab)) i)
    choose L hL using h1
    exact ⟨L, fun k => SModEq.sub_mem.2
      ((mem_pow_smul_top_pi π k _).2 fun i => SModEq.sub_mem.1 (hL i k))⟩
  have : IsHausdorff (Ideal.span {π}) (κ → O) := by
    refine ⟨fun x hx => funext fun j => IsHausdorff.haus' (I := Ideal.span {π}) (x j) fun n => ?_⟩
    exact SModEq.sub_mem.2 ((mem_pow_smul_top_pi π n _).1 (SModEq.sub_mem.1 (hx n)) j)
  refine surjective_of_mkQ_comp_surjective (I := Ideal.span {π}) fun G => ?_
  obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective _ G
  obtain ⟨x, hx⟩ := h G
  refine ⟨x, ((Submodule.Quotient.eq _).2 ?_).symm⟩
  have := (mem_pow_smul_top_pi π 1 (G - Φ x)).2 fun j => by simpa using hx j
  rwa [pow_one] at this

theorem exists_projection {O K : Type*} [CommRing O] [IsLocalRing O] [Field K] (f : O →+* K)
    (hf : RingHom.ker f = IsLocalRing.maximalIdeal O) :
    ∃ (μ : K →+ K) (l : K → O), (∀ a, f (l a) = μ a) ∧ (∀ a o, μ (a * f o) = μ a * f o) ∧
      ∀ o, μ (f o) = f o := by
  let φ : IsLocalRing.ResidueField O →+* K :=
    Ideal.Quotient.lift _ f fun a ha => by rwa [← hf] at ha
  have hφ : ∀ o, φ (IsLocalRing.residue O o) = f o := fun _ => rfl
  letI := φ.toAlgebra
  obtain ⟨r, hr⟩ := (Algebra.linearMap (IsLocalRing.ResidueField O) K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 φ.injective)
  choose l hl using fun a => IsLocalRing.residue_surjective (R := O) (r a)
  refine ⟨φ.toAddMonoidHom.comp r.toAddMonoidHom, l, fun a => ?_, fun a o => ?_, fun o => ?_⟩
  · change _ = φ (r a)
    rw [← hl, hφ]
  · change φ (r _) = φ (r a) * _
    have : a * f o = IsLocalRing.residue O o • a := mul_comm _ _
    rw [this, map_smul, smul_eq_mul, map_mul, hφ, mul_comm]
  · change φ (r _) = _
    have : r (f o) = IsLocalRing.residue O o := LinearMap.congr_fun hr (IsLocalRing.residue O o)
    rw [this, hφ]

theorem span_mod_equations_lift (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (K : Type) [Field K] (f : O →+* K) (g N : ℕ)
    (Y : Type) (F : Y → Fin g → (MvPowerSeries (Fin g) O))
    (ρ : Y → Fin N → (MvPowerSeries (Fin g) O))
    (hf : RingHom.ker f = IsLocalRing.maximalIdeal O)
    (h : ∀ G : Y → MvPowerSeries (Fin g) K, ∃ v : Fin N → K, ∀ y,
      G y - ∑ k, v k • MvPowerSeries.map f (ρ y k) ∈
        Ideal.span (Set.range fun i => MvPowerSeries.map f (F y i)))
    (G : Y → (MvPowerSeries (Fin g) O)) :
    ∃ v : Fin N → O, ∀ y, G y - ∑ k, v k • ρ y k ∈ Ideal.span (Set.range (F y)) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm := hπ.maximalIdeal_eq
  have : IsAdicComplete (Ideal.span {π}) O := hm ▸ ‹_›
  obtain ⟨μ, l, hl, hμ, hμ1⟩ := exists_projection f hf
  let Φ : (Fin N ⊕ (Y × Fin g × (Fin g →₀ ℕ)) → O) →ₗ[O] (Y × (Fin g →₀ ℕ) → O) :=
    { toFun := fun x j => ∑ k, x (.inl k) * MvPowerSeries.coeff j.2 (ρ j.1 k) +
        ∑ i, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j.2,
          x (.inr (j.1, i, p.1)) * MvPowerSeries.coeff p.2 (F j.1 i)
      map_add' := fun x x' => funext fun j => by
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := fun c x => funext fun j => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add, Finset.mul_sum,
          mul_assoc] }
  have hΦ : Function.Surjective Φ := by
    refine surjective_of_mod π Φ fun G => ?_
    let G' : Y → MvPowerSeries (Fin g) K := fun y d => f (G (y, d))
    obtain ⟨v, hv⟩ := h G'
    choose H hH using fun y => (Ideal.mem_span_range_iff_exists_fun).1 (hv y)
    refine ⟨Sum.elim (fun k => l (v k)) fun q => l (MvPowerSeries.coeff q.2.2 (H q.1 q.2.1)), ?_⟩
    rintro ⟨y, d⟩
    rw [← hm, ← hf, RingHom.mem_ker]
    have h1 := congrArg (fun s => μ (MvPowerSeries.coeff d s)) (eq_sub_iff_add_eq.1 (hH y))
    have h2 : MvPowerSeries.coeff d (G' y) = f (G (y, d)) := rfl
    simp only [map_add, map_sum, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_smul, hμ, hμ1, h2] at h1
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, map_sub, map_add, map_sum, map_mul, Sum.elim_inl,
      Sum.elim_inr, hl]
    rw [← h1, add_comm, sub_self]
  obtain ⟨x, hx⟩ := hΦ fun j => MvPowerSeries.coeff j.2 (G j.1)
  refine ⟨fun k => x (.inl k), fun y => Ideal.mem_span_range_iff_exists_fun.2
    ⟨fun i => (show MvPowerSeries (Fin g) O from fun d => x (.inr (y, i, d))), ?_⟩⟩
  ext d
  have h1 : _ = MvPowerSeries.coeff d (G y) := congrFun hx (y, d)
  simp only [map_sub, map_sum, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_smul, ← h1, Φ,
    LinearMap.coe_mk, AddHom.coe_mk, add_sub_cancel_left]
  exact Finset.sum_congr rfl fun i _ => MvPowerSeries.coeff_mul d _ _

end GlobalTheory.SeriesNakayama

import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.WeilBound.CoreStatements.HodgeTatePoints.RbFund

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rb

section general

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {F : Type} [Field F] [Fintype F] [DecidableEq F] {N : Type} [AddCommGroup N] [Module F N]

theorem f_ne_zero {p f : ℕ} (hc : Fintype.card F = p ^ f) : f ≠ 0 := by
  rintro rfl
  have := Fintype.one_lt_card (α := F)
  simp [hc] at this

theorem exists_inv_card {p f : ℕ} {v : Valuation C NNReal} (hv : v.Integers R)
    (hp : v (p : C) < 1) (hc : Fintype.card F = p ^ f) :
    (Fintype.card Fˣ : C) ≠ 0 ∧ ∃ w : R, algebraMap R C w = (Fintype.card Fˣ : C)⁻¹ := by
  have hf := f_ne_zero (F := F) hc
  have h1 : 1 ≤ p ^ f := hc ▸ Fintype.card_pos
  have hcard : (Fintype.card Fˣ : C) = (p : C) ^ f - 1 := by
    rw [Fintype.card_units, hc, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one]
  have hlt : v ((p : C) ^ f) < v (1 : C) := by
    rw [map_pow, map_one]
    exact pow_lt_one₀ zero_le hp hf
  have hval : v (Fintype.card Fˣ : C) = 1 := by
    rw [hcard, Valuation.map_sub_eq_of_lt_right _ hlt, map_one]
  have h0 : (Fintype.card Fˣ : C) ≠ 0 := fun h => by simp [h] at hval
  refine ⟨h0, hv.exists_of_le_one ?_⟩
  rw [map_inv₀, hval, inv_one]

theorem proj_eq_smul {w : R} (hw : algebraMap R C w = (Fintype.card Fˣ : C)⁻¹)
    (χ : MulChar F R) (g : N → C) :
    proj χ g = w • ∑ a : Fˣ, χ⁻¹ (a : F) • fun x => g ((a : F) • x) := by
  funext x
  simp [proj, Algebra.smul_def, hw, Finset.sum_apply]

theorem proj_mem {w : R} (hw : algebraMap R C w = (Fintype.card Fˣ : C)⁻¹)
    (S : Submodule R (N → C)) (χ : MulChar F R) (g : N → C)
    (h : ∀ a : F, (fun x => g (a • x)) ∈ S) : proj χ g ∈ S := by
  rw [proj_eq_smul hw]
  exact S.smul_mem _ (S.sum_mem fun a _ => S.smul_mem _ (h a))

noncomputable def projL (χ : MulChar F R) : (N → C) →ₗ[R] (N → C) where
  toFun := proj χ
  map_add' g h := by
    funext x
    simp [proj, mul_add, Finset.sum_add_distrib]
  map_smul' c g := by
    funext x
    simp only [proj, Pi.smul_apply, Algebra.smul_def, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

theorem projL_apply (χ : MulChar F R) (g : N → C) : projL χ g = proj χ g := rfl

theorem sum_units_eq (ψ : MulChar F R) : ∑ a : Fˣ, ψ (a : F) = ∑ a : F, ψ a := by
  have h := Finset.sum_map (Finset.univ : Finset Fˣ) ⟨((↑) : Fˣ → F), Units.val_injective⟩ (fun a => ψ a)
  simp only [Function.Embedding.coeFn_mk] at h
  rw [← h]
  refine Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_
  refine MulChar.map_nonunit ψ fun hu => ha ?_
  exact Finset.mem_map.2 ⟨hu.unit, Finset.mem_univ _, rfl⟩

theorem orth_ne [IsDomain R] {χ ψ : MulChar F R} (h : χ ≠ ψ) :
    ∑ a : Fˣ, χ⁻¹ (a : F) * ψ (a : F) = 0 := by
  have hne : χ⁻¹ * ψ ≠ 1 := fun h' => h (inv_mul_eq_one.1 h')
  calc ∑ a : Fˣ, χ⁻¹ (a : F) * ψ (a : F) = ∑ a : Fˣ, (χ⁻¹ * ψ) (a : F) := by
        simp only [MulChar.mul_apply]
    _ = 0 := by
        rw [sum_units_eq]
        exact MulChar.sum_eq_zero_of_ne_one hne

theorem inv_mul_apply (χ : MulChar F R) (a : Fˣ) : χ⁻¹ (a : F) * χ (a : F) = 1 := by
  rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply_coe]

theorem proj_eigen_ne [IsDomain R] {χ ψ : MulChar F R} (h : χ ≠ ψ) (e : N → C)
    (he : ∀ (a : F) x, e (a • x) = algebraMap R C (ψ a) * e x) : proj χ e = 0 := by
  funext x
  simp only [proj, he, Pi.zero_apply]
  have hs : ∑ a : Fˣ, algebraMap R C (χ⁻¹ (a : F)) * (algebraMap R C (ψ (a : F)) * e x) =
      algebraMap R C (∑ a : Fˣ, χ⁻¹ (a : F) * ψ (a : F)) * e x := by
    rw [map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by rw [map_mul, mul_assoc]
  rw [hs, orth_ne h, map_zero, zero_mul, mul_zero]

theorem proj_eigen_self (h0 : (Fintype.card Fˣ : C) ≠ 0) (χ : MulChar F R) (e : N → C)
    (he : ∀ (a : F) x, e (a • x) = algebraMap R C (χ a) * e x) : proj χ e = e := by
  funext x
  simp only [proj, he]
  have hterm : ∀ a : Fˣ, algebraMap R C (χ⁻¹ (a : F)) * (algebraMap R C (χ (a : F)) * e x) = e x :=
    fun a => by rw [← mul_assoc, ← map_mul, inv_mul_apply, map_one, one_mul]
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]

theorem proj_smul_apply (χ : MulChar F R) (g : N → C) (hg : g 0 = 0) (a : F) (x : N) :
    proj χ g (a • x) = algebraMap R C (χ a) * proj χ g x := by
  by_cases ha : a = 0
  · subst ha
    simp only [proj, zero_smul, smul_zero, hg, mul_zero, Finset.sum_const_zero, MulChar.map_zero,
      map_zero, zero_mul]
  · obtain ⟨u, rfl⟩ := (Ne.isUnit ha)
    simp only [proj]
    rw [mul_left_comm]
    congr 1
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight u) _ _ fun b => ?_
    simp only [Equiv.coe_mulRight, Units.val_mul, mul_smul, map_mul]
    have key : algebraMap R C (χ (u : F)) * algebraMap R C (χ⁻¹ (u : F)) = 1 := by
      rw [← map_mul, mul_comm, inv_mul_apply, map_one]
    linear_combination (-(algebraMap R C (χ⁻¹ (b : F)) * g ((b : F) • (u : F) • x))) * key

theorem mem_pInt_iff (hinj : Function.Injective (algebraMap R C)) (p : ℕ) (r : R) :
    algebraMap R C r ∈ pInt (C := C) R p ↔ r ∈ Ideal.span {(p : R)} := by
  rw [pInt, Submodule.mem_span_singleton, Ideal.mem_span_singleton']
  refine exists_congr fun a => ?_
  rw [Algebra.smul_def, ← map_natCast (algebraMap R C) p, ← map_mul]
  exact hinj.eq_iff

theorem mem_pFun {p : ℕ} {X : Type} {g : X → C} :
    g ∈ pFun R p X ↔ ∀ x, g x ∈ pInt (C := C) R p := by
  simp [pFun, Submodule.mem_pi]

end general

private theorem sum_Icc_pow_eq_mul_sum_range {R : Type} [CommRing R] (ζ : R) (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, ζ ^ m = ζ * ∑ m ∈ Finset.range n, ζ ^ m := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, mul_add, pow_succ']

private theorem sum_Icc_pow_eq_zero_of_root_of_unity_ne_one {R : Type} [CommRing R] [IsDomain R] (ζ : R) (n : ℕ)
    (hn : ζ ^ n = 1) (h1 : ζ ≠ 1) : ∑ m ∈ Finset.Icc 1 n, ζ ^ m = 0 := by
  rw [sum_Icc_pow_eq_mul_sum_range]
  have h := geom_sum_mul ζ n
  rw [hn, sub_self] at h
  rw [(mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 h1), mul_zero]

private theorem comp_smul_mem_augIdeal_of_fStable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N] (A : Submodule R (N → C))
    (hA : FStable F A) (a : F) : ∀ f ∈ augIdeal A, (fun x => f (a • x)) ∈ augIdeal A := by
  intro f hf
  have h1 := (Submodule.mem_inf.1 hf).1
  have h2 : f 0 = 0 := by simpa using LinearMap.mem_ker.1 (Submodule.mem_inf.1 hf).2
  refine Submodule.mem_inf.2 ⟨hA a f h1, LinearMap.mem_ker.2 ?_⟩
  simpa [smul_zero] using h2

private theorem comp_smul_mem_sqIdeal_of_fStable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N] (A : Submodule R (N → C))
    (hA : FStable F A) (a : F) (g : N → C) (hg : g ∈ sqIdeal (augIdeal A)) :
    (fun x => g (a • x)) ∈ sqIdeal (augIdeal A) := by
  let L : (N → C) →ₗ[R] (N → C) := LinearMap.funLeft R C (fun x : N => a • x)
  have hle : sqIdeal (augIdeal A) ≤ (sqIdeal (augIdeal A)).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, f', hf', rfl⟩
    exact Submodule.subset_span
      ⟨L f, comp_smul_mem_augIdeal_of_fStable A hA a f hf, L f', comp_smul_mem_augIdeal_of_fStable A hA a f' hf', rfl⟩
  exact hle hg

theorem proj_props : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ g ∈ augIdeal AA.carrier, (∀ χ : MulChar F R, proj χ g ∈ eig AA.carrier χ) ∧ g = ∑ m ∈ Finset.Icc 1 (p ^ f - 1), proj (σ ^ m) g ∧ (g ∈ afFun p AA.carrier → ∀ χ : MulChar F R, proj χ g ∈ afFun p AA.carrier) ∧ (∀ K : Submodule F N, g ∈ invFun AA.carrier K.toAddSubgroup → ∀ χ : MulChar F R, proj χ g ∈ invFun AA.carrier K.toAddSubgroup) ∧ (g ∈ sqIdeal (augIdeal AA.carrier) → ∀ χ : MulChar F R, proj χ g ∈ sqIdeal (augIdeal AA.carrier)) := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc N _ _ _ _ AA hFS σ hσ g hg
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hinj
  obtain ⟨h0, w, hw⟩ := exists_inv_card (F := F) hv hp hc
  have hgA : g ∈ AA.carrier := (Submodule.mem_inf.1 hg).1
  have hg0 : g 0 = 0 := by simpa using LinearMap.mem_ker.1 (Submodule.mem_inf.1 hg).2
  refine ⟨fun χ => ⟨proj_mem hw AA.carrier χ g (fun a => hFS a g hgA),
      fun a x => proj_smul_apply χ g hg0 a x⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hord, -, -, -, hsep⟩ := FundGen.main p C v R hv hp F f hc σ hσ
    have hcardU : Fintype.card Fˣ = p ^ f - 1 := by rw [Fintype.card_units, hc]
    have hσq : σ ^ (p ^ f - 1) = 1 := hord ▸ pow_orderOf_eq_one σ
    have hz : ∀ a : Fˣ, ∑ m ∈ Finset.Icc 1 (p ^ f - 1), (σ ^ m)⁻¹ (a : F) =
        if a = 1 then ((p ^ f - 1 : ℕ) : R) else 0 := by
      intro a
      have hpow : ∀ m : ℕ, (σ ^ m)⁻¹ (a : F) = (σ⁻¹ (a : F)) ^ m := fun m => by
        rw [← inv_pow, MulChar.pow_apply_coe]
      simp only [hpow]
      split_ifs with ha
      · subst ha
        simp
      · refine sum_Icc_pow_eq_zero_of_root_of_unity_ne_one _ _ ?_ ?_
        · rw [← MulChar.pow_apply_coe, inv_pow, hσq, inv_one, MulChar.one_apply_coe]
        · intro h1
          have hne : (a : F) ≠ 1 := fun h => ha (Units.val_eq_one.1 h)
          have hs := hsep (a : F) 1 hne
          have hsa : σ (a : F) = 1 := by
            have := inv_mul_apply σ a
            rwa [h1, one_mul] at this
          rw [hsa, MulChar.map_one, sub_self, map_zero, map_zero] at hs
          exact zero_ne_one hs
    funext x
    have hsum : (∑ m ∈ Finset.Icc 1 (p ^ f - 1), proj (σ ^ m) g) x =
        ((Fintype.card Fˣ : C))⁻¹ * ∑ a : Fˣ, algebraMap R C
          (∑ m ∈ Finset.Icc 1 (p ^ f - 1), (σ ^ m)⁻¹ (a : F)) * g ((a : F) • x) := by
      rw [Finset.sum_apply]
      simp only [proj]
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_sum, Finset.sum_mul]
    rw [hsum]
    simp only [hz, apply_ite (algebraMap R C), ite_mul, map_zero, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Units.val_one, one_smul, map_natCast]
    rw [← hcardU, inv_mul_cancel_left₀ h0]
  · intro haf χ
    have hA : g ∈ AA.carrier := (Submodule.mem_inf.1 haf).1
    have hadd : ∀ x y, g (x + y) - g x - g y ∈ pInt (C := C) R p := (Submodule.mem_inf.1 haf).2
    refine proj_mem hw _ χ g fun a => Submodule.mem_inf.2 ⟨hFS a g hA, fun x y => ?_⟩
    simpa [smul_add] using hadd (a • x) (a • y)
  · intro K hK χ
    obtain ⟨hA, hinv⟩ := hK
    refine proj_mem hw _ χ g fun a => ⟨hFS a g hA, fun y k hk => ?_⟩
    simp only [smul_add]
    exact hinv (a • y) (a • k) (K.smul_mem a hk)
  · intro hsq χ
    exact proj_mem hw _ χ g fun a => comp_smul_mem_sqIdeal_of_fStable AA.carrier hFS a g hsq

theorem proj_nf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ g ∈ afFun p AA.carrier, ∀ χ : MulChar F R, ¬ IsFund p χ → proj χ g ∈ pFun R p N := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc N _ _ _ _ AA hFS g hg χ hχ
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hinj
  obtain ⟨σ, hσ⟩ := fund_ex p C v R hv hp F f hc
  obtain ⟨-, -, hfrob, -, -⟩ := FundGen.main p C v R hv hp F f hc σ hσ
  obtain ⟨-, w, hw⟩ := exists_inv_card (F := F) hv hp hc
  have hgA : g ∈ AA.carrier := (Submodule.mem_inf.1 hg).1
  have hadd : ∀ x y, g (x + y) - g x - g y ∈ pInt (C := C) R p := (Submodule.mem_inf.1 hg).2
  have hint : ∀ y, ∃ r : R, algebraMap R C r = g y := AA.le_int hgA
  rw [mem_pFun]
  intro x
  choose l hl using fun a : F => hint (a • x)
  have hladd : ∀ a b : F, l (a + b) - l a - l b ∈ Ideal.span {(p : R)} := by
    intro a b
    rw [← mem_pInt_iff hinj, map_sub, map_sub, hl, hl, hl, add_smul]
    exact hadd _ _
  obtain ⟨β, hβ, -⟩ := moore p C v R hv hp F f hc σ hσ l hladd
  have key : ∑ a : Fˣ, χ⁻¹ (a : F) * l a ∈ Ideal.span {(p : R)} := by
    have hsplit : ∀ a : Fˣ, χ⁻¹ (a : F) * l a =
        χ⁻¹ (a : F) * (l a - ∑ n : Fin f, β n * (σ ^ p ^ (n : ℕ)) (a : F)) +
          ∑ n : Fin f, χ⁻¹ (a : F) * (β n * (σ ^ p ^ (n : ℕ)) (a : F)) := fun a => by
      rw [← Finset.mul_sum, ← mul_add, sub_add_cancel]
    rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_add_distrib]
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hβ a)) ?_
    rw [Finset.sum_comm]
    refine Ideal.sum_mem _ fun n _ => ?_
    have hne : χ ≠ σ ^ p ^ (n : ℕ) := by
      rintro rfl
      exact hχ (hfrob n)
    have hpull : ∑ a : Fˣ, χ⁻¹ (a : F) * (β n * (σ ^ p ^ (n : ℕ)) (a : F)) =
        β n * ∑ a : Fˣ, χ⁻¹ (a : F) * (σ ^ p ^ (n : ℕ)) (a : F) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => mul_left_comm _ _ _
    rw [hpull, orth_ne hne, mul_zero]
    exact Ideal.zero_mem _
  have hval : proj χ g x = algebraMap R C (w * ∑ a : Fˣ, χ⁻¹ (a : F) * l a) := by
    simp only [proj]
    rw [← hw, map_mul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, hl]
  rw [hval, mem_pInt_iff hinj]
  exact Ideal.mul_mem_left _ _ key

end PositivityTheory.HtPt.Rb

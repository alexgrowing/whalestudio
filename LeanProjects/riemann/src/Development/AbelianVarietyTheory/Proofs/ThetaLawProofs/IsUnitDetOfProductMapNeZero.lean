import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CoeffEqZeroOfMemSpanPow
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DiscrMulDetEqNormOfAnnihilator

namespace GlobalTheory.DiscrJacobian

open scoped TensorProduct

section Diagonal

variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B]

variable (R S B) in

noncomputable def mu : S ⊗[R] B →ₐ[S] B :=
  Algebra.TensorProduct.lift (Algebra.ofId S B) (AlgHom.id R B) fun _ _ => Commute.all _ _

open scoped TensorProduct in
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B] in
@[simp] theorem _root_.GlobalTheory.DiscrJacobian.mu_tmul (s : S) (w : B) :
    _root_.GlobalTheory.DiscrJacobian.mu R S B (s ⊗ₜ w) = algebraMap S B s * w := by
  simp [_root_.GlobalTheory.DiscrJacobian.mu]

open scoped TensorProduct in
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B] in

theorem _root_.GlobalTheory.DiscrJacobian.mem_span_of_mu_eq_zero {ι : Type} [Fintype ι] [Module.Finite R B]
    [Module.FinitePresentation S B] (x : ι → S)
    (hx : ∀ j, x j ∈ (⊥ : Ideal S).jacobson)
    (hgen : ∀ s : S, ∃ (c : R) (u : ι → S), s = algebraMap R S c + ∑ j, x j * u j)
    (z : S ⊗[R] B) (hz : _root_.GlobalTheory.DiscrJacobian.mu R S B z = 0) :
    z ∈ Ideal.span (Set.range fun j => x j ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B (x j)) := by
  classical
  set J := Ideal.span (Set.range fun j => x j ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B (x j))
    with hJ
  set K : Ideal (S ⊗[R] B) := RingHom.ker (_root_.GlobalTheory.DiscrJacobian.mu R S B) with hK
  set I : Ideal (S ⊗[R] B) := Ideal.map (algebraMap S (S ⊗[R] B)) (Ideal.span (Set.range x))
    with hI
  let δ : S → S ⊗[R] B := fun s => s ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B s
  have hδK : ∀ s, δ s ∈ K := by
    intro s; simp [K, δ, RingHom.mem_ker]
  have hδJ : ∀ j, δ (x j) ∈ J := fun j => Ideal.subset_span ⟨j, rfl⟩
  have hxI : ∀ j, x j ⊗ₜ[R] (1 : B) ∈ I := fun j =>
    Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)
  have hadd : ∀ a b, δ (a + b) = δ a + δ b := by
    intro a b; simp only [δ, map_add, TensorProduct.add_tmul, TensorProduct.tmul_add]; abel
  have hmul : ∀ a b, δ (a * b) =
      δ a * (b ⊗ₜ[R] (1 : B)) + (a ⊗ₜ[R] (1 : B)) * δ b - δ a * δ b := by
    intro a b
    simp only [δ, map_mul, sub_mul, mul_sub, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    abel
  have hδ : ∀ s, δ s ∈ J ⊔ I * K := by
    intro s
    obtain ⟨c, u, rfl⟩ := hgen s
    have hc : δ (algebraMap R S c) = 0 := by
      show _ - _ = 0
      rw [sub_eq_zero, ← IsScalarTower.algebraMap_apply R S B, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    have hsum : ∀ t : Finset ι, δ (∑ j ∈ t, x j * u j) = ∑ j ∈ t, δ (x j * u j) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp [δ]
      | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
    rw [hadd, hc, zero_add, hsum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [hmul]
    refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (hδJ j))
    · exact Ideal.mem_sup_right (Ideal.mul_mem_mul (hxI j) (hδK (u j)))
    · exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (hδJ j))
  have hle : K ≤ J ⊔ I * K := by
    intro z hz
    have key : ∀ t : S ⊗[R] B, t - (1 : S) ⊗ₜ[R] _root_.GlobalTheory.DiscrJacobian.mu R S B t ∈ J ⊔ I * K := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb =>
        rw [map_add, TensorProduct.tmul_add]
        convert Ideal.add_mem _ ha hb using 1
        abel
      | tmul s w =>
        have : s ⊗ₜ[R] w - (1 : S) ⊗ₜ[R] _root_.GlobalTheory.DiscrJacobian.mu R S B (s ⊗ₜ[R] w) = δ s * ((1 : S) ⊗ₜ[R] w) := by
          simp [δ, sub_mul, Algebra.TensorProduct.tmul_mul_tmul]
        rw [this]
        exact Ideal.mul_mem_right _ _ (hδ s)
    have := key z
    rwa [show _root_.GlobalTheory.DiscrJacobian.mu R S B z = 0 from hz, TensorProduct.tmul_zero, sub_zero] at this
  have hKfg : K.FG := by
    obtain ⟨t, ht⟩ := Module.FinitePresentation.fg_ker (_root_.GlobalTheory.DiscrJacobian.mu R S B).toLinearMap
      (fun w => ⟨1 ⊗ₜ w, by simp⟩)
    refine ⟨t, le_antisymm ?_ ?_⟩
    · rw [Ideal.span_le]
      intro a ha
      have := ht ▸ Submodule.subset_span ha
      simpa [K, RingHom.mem_ker] using this
    · intro a ha
      have : a ∈ Submodule.span S (t : Set (S ⊗[R] B)) := by
        rw [ht]; simpa [K, RingHom.mem_ker] using ha
      exact Submodule.span_le_restrictScalars S (S ⊗[R] B) _ this
  have hIjac : I ≤ (⊥ : Ideal (S ⊗[R] B)).jacobson := by
    rw [hI, Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    haveI : Algebra.IsIntegral S (S ⊗[R] B) := Algebra.IsIntegral.of_finite _ _
    unfold Ideal.jacobson
    rw [Ideal.mem_sInf]
    intro M hM
    haveI : M.IsMaximal := hM.2
    have hMc : (M.comap (algebraMap S (S ⊗[R] B))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    have h2 := hx j
    unfold Ideal.jacobson at h2
    exact Ideal.mem_sInf.mp h2 ⟨bot_le, hMc⟩
  exact Submodule.le_of_le_smul_of_le_jacobson_bot hKfg hIjac (by simpa [smul_eq_mul] using hle) hz

noncomputable def der (D : Derivation R S S) : S ⊗[R] B →ₗ[R] B :=
  ((mu R S B).toLinearMap.restrictScalars R) ∘ₗ D.toLinearMap.rTensor B

open scoped TensorProduct in
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B] in
@[simp] theorem _root_.GlobalTheory.DiscrJacobian.der_tmul (D : Derivation R S S) (s : S) (w : B) :
    _root_.GlobalTheory.DiscrJacobian.der D (s ⊗ₜ[R] w) = algebraMap S B (D s) * w := by
  simp [_root_.GlobalTheory.DiscrJacobian.der]

open scoped TensorProduct in
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B] in
theorem _root_.GlobalTheory.DiscrJacobian.der_mul (D : Derivation R S S) (y z : S ⊗[R] B) :
    _root_.GlobalTheory.DiscrJacobian.der D (y * z) =
      _root_.GlobalTheory.DiscrJacobian.mu R S B y * _root_.GlobalTheory.DiscrJacobian.der D z +
        _root_.GlobalTheory.DiscrJacobian.mu R S B z * _root_.GlobalTheory.DiscrJacobian.der D y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' hy hy' => rw [add_mul, map_add, hy, hy', map_add, map_add]; ring
  | tmul s w =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => rw [mul_add, map_add, hz, hz', map_add, map_add]; ring
    | tmul t v =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp only [_root_.GlobalTheory.DiscrJacobian.der_tmul, _root_.GlobalTheory.DiscrJacobian.mu_tmul,
        Derivation.leibniz, smul_eq_mul, map_add, map_mul]
      ring

end Diagonal

section Socle

variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

noncomputable def pairing (ρ : B →ₐ[R] C) (ψ : B →ₗ[R] C) : B ⊗[R] B →ₗ[R] C :=
  LinearMap.mul' R C ∘ₗ TensorProduct.map ρ.toLinearMap ψ

open scoped TensorProduct in
variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] in
@[simp] theorem _root_.GlobalTheory.DiscrJacobian.pairing_tmul (ρ : B →ₐ[R] C) (ψ : B →ₗ[R] C) (u w : B) :
    _root_.GlobalTheory.DiscrJacobian.pairing ρ ψ (u ⊗ₜ w) = ρ u * ψ w := by
  simp [_root_.GlobalTheory.DiscrJacobian.pairing]

theorem exists_socle {V : Type} [AddCommGroup V] [Module R V] (n : Ideal B) (φ : B →ₗ[R] V)
    (hφ : φ ≠ 0) (N : ℕ) (hN : ∀ w ∈ n ^ N, φ w = 0) :
    ∃ y, φ y ≠ 0 ∧ ∀ w ∈ n, φ (w * y) = 0 := by
  induction N with
  | zero => exact absurd (LinearMap.ext fun w => hN w (by simp)) hφ
  | succ N ih =>
    by_cases h : ∀ w ∈ n ^ N, φ w = 0
    · exact ih h
    · push Not at h
      obtain ⟨y, hy, hy'⟩ := h
      exact ⟨y, hy', fun w hw => hN _ (by rw [pow_succ']; exact Ideal.mul_mem_mul hw hy)⟩

open scoped TensorProduct in
variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] in
open IsLocalRing in

theorem _root_.GlobalTheory.DiscrJacobian.isUnit_det_of_productMap_ne_zero [IsLocalRing R]
    [Algebra (ResidueField R) C]
    [IsScalarTower R (ResidueField R) C] {d : ℕ} (b : Module.Basis (Fin d) R B)
    (n : Ideal B) (N : ℕ) (hN : n ^ N ≤ (maximalIdeal R).map (algebraMap R B))
    (ev : B →ₐ[R] ResidueField R) (hev : ∀ w ∈ n, ev w = 0)
    (hgen : ∀ w : B, ∃ c : R, w - algebraMap R B c ∈ n) (ρ : B →ₐ[R] C)
    (De : B ⊗[R] B) (M : Matrix (Fin d) (Fin d) R)
    (hDe : De = ∑ i, ∑ j, M i j • TensorProduct.tmul R (b i) (b j))
    (h : ∀ x : B, De * (TensorProduct.tmul R x 1 - TensorProduct.tmul R 1 x) = 0)
    (H : Algebra.TensorProduct.productMap ρ
      ((IsScalarTower.toAlgHom R (ResidueField R) C).comp ev) De ≠ 0) :
    IsUnit M.det := by
  classical
  subst hDe
  haveI : Module.Finite R B := Module.Finite.of_basis b
  haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  obtain ⟨i0, hi0⟩ : ∃ i, ev (∑ j, M i j • b j) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply H
    have hrow : ∀ i, ∑ j, M i j • (ρ (b i) *
        (IsScalarTower.toAlgHom R (ResidueField R) C) (ev (b j))) =
        ρ (b i) * (IsScalarTower.toAlgHom R (ResidueField R) C) (ev (∑ j, M i j • b j)) := by
      intro i
      simp [map_sum, Finset.mul_sum, mul_smul_comm]
    simp only [map_sum, map_smul, Algebra.TensorProduct.productMap_apply_tmul, AlgHom.comp_apply,
      hrow, hcon, map_zero, mul_zero, Finset.sum_const_zero]
  set w := ∑ j, M i0 j • b j with hw
  have hwunit : IsUnit w := by
    obtain ⟨c, hc⟩ := hgen w
    have hevc : ev (algebraMap R B c) ≠ 0 := by
      have := hev _ hc
      rw [map_sub, sub_eq_zero] at this
      rwa [← this]
    have hcu : IsUnit c := by
      rw [AlgHom.commutes] at hevc
      by_contra hnu
      exact hevc ((IsLocalRing.residue_eq_zero_iff c).mpr ((IsLocalRing.mem_maximalIdeal c).mpr hnu))
    by_contra hnw
    obtain ⟨P, hP, hwP⟩ := Ideal.exists_le_maximal (Ideal.span {w})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have hPc : P.comap (algebraMap R B) = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)
    have hmP : (maximalIdeal R).map (algebraMap R B) ≤ P := by
      rw [Ideal.map_le_iff_le_comap, hPc]
    have hν : w - algebraMap R B c ∈ P :=
      hP.isPrime.mem_of_pow_mem N (hmP (hN (Ideal.pow_mem_pow hc N)))
    have hcP : algebraMap R B c ∈ P := by
      have := P.sub_mem (hwP (Ideal.mem_span_singleton_self w)) hν
      simpa using this
    have : c ∈ maximalIdeal R := by rw [← hPc]; exact hcP
    exact (IsLocalRing.mem_maximalIdeal c).mp this hcu
  obtain ⟨w', hw'⟩ := hwunit.exists_right_inv
  have hsurj : Function.Surjective (fun v : Fin d → R => Matrix.vecMul v M) := by
    intro t
    set u := w' * ∑ j, t j • b j with hu
    refine ⟨fun i => b.coord i0 (b i * u), ?_⟩
    have hs := _root_.GlobalTheory.annihilator_diagonal_form_swap (⇑b) M h (b.coord i0) u
    have hr : ∑ i, ∑ j, (M i j * b.coord i0 (b i)) • (b j * u) = ∑ j, t j • b j := by
      have : w * u = ∑ j, t j • b j := by rw [hu, ← mul_assoc, hw', one_mul]
      rw [← this, hw, Finset.sum_mul]
      simp [Module.Basis.coord_apply, Finsupp.single_apply, smul_mul_assoc]
    apply b.equivFun.symm.injective
    simp only [Module.Basis.equivFun_symm_apply]
    rw [← hr, ← hs]
    simp only [Matrix.vecMul, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp [mul_comm]
  exact (Matrix.isUnit_iff_isUnit_det M).mp (Matrix.vecMul_surjective_iff_isUnit.mp hsurj)

end Socle

section Series

open MvPowerSeries IsLocalRing

open MvPowerSeries IsLocalRing in
open scoped TensorProduct in
theorem _root_.GlobalTheory.DiscrJacobian.exists_eq_C_add_sum {R : Type} [CommRing R] {g : ℕ}
    (s : MvPowerSeries (Fin g) R) :
    ∃ u : Fin g → MvPowerSeries (Fin g) R, s = C (constantCoeff s) + ∑ j, X j * u j := by
  have hmem : s - C (constantCoeff s) ∈
      Ideal.span ((fun i => (X i : MvPowerSeries (Fin g) R)) '' ↑(Finset.univ : Finset (Fin g))) := by
    apply _root_.GlobalTheory.SocleDet.mem_span_X_of_coeff
    intro m hm
    have : m = 0 := by ext j; simpa using hm j (Finset.mem_univ j)
    subst this
    simp
  rw [Finset.coe_univ, Set.image_univ, Ideal.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, ?_⟩
  rw [← sub_eq_iff_eq_add', ← hc]
  simp [mul_comm]

open MvPowerSeries IsLocalRing in
open scoped TensorProduct in
theorem _root_.GlobalTheory.DiscrJacobian.X_mem_jacobson {R : Type} [CommRing R] {σ : Type} (j : σ) :
    (X j : MvPowerSeries σ R) ∈ (⊥ : Ideal (MvPowerSeries σ R)).jacobson := by
  rw [Ideal.mem_jacobson_bot]
  intro y
  rw [MvPowerSeries.isUnit_iff_constantCoeff]
  simp

open MvPowerSeries IsLocalRing in
open scoped TensorProduct in

theorem _root_.GlobalTheory.DiscrJacobian.map_mem_radical {R S B : Type} [CommRing R]
    [IsLocalRing R] [CommRing S] [CommRing B]
    [Algebra R B] [Algebra S B] [Module.Finite R B] (hsurj : Function.Surjective (algebraMap S B))
    {x : S} (hx : x ∈ (⊥ : Ideal S).jacobson) :
    algebraMap S B x ∈ ((maximalIdeal R).map (algebraMap R B)).radical := by
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  intro P hPmem
  have hP : Ideal.map (algebraMap R B) (maximalIdeal R) ≤ P := hPmem.1
  haveI hPprime : P.IsPrime := hPmem.2
  have hle : maximalIdeal R ≤ P.comap (algebraMap R B) := Ideal.map_le_iff_le_comap.mp hP
  haveI : (P.comap (algebraMap R B)).IsPrime := Ideal.IsPrime.comap (algebraMap R B)
  have hcomap : P.comap (algebraMap R B) = maximalIdeal R :=
    le_antisymm (IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top') hle
  have hm : (P.comap (algebraMap R B)).IsMaximal := by
    rw [hcomap]; exact maximalIdeal.isMaximal R
  haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  haveI hPmax : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hm
  have hmax : (P.comap (algebraMap S B)).IsMaximal := Ideal.comap_isMaximal_of_surjective _ hsurj
  unfold Ideal.jacobson at hx
  exact Ideal.mem_sInf.mp hx ⟨bot_le, hmax⟩

open scoped TensorProduct in
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B] in
private theorem tensorMap_det_mul_tmul_sub_eq_zero {g : ℕ} [Module.Finite R B] [Module.FinitePresentation S B]
    (x f : Fin g → S) (hx : ∀ j, x j ∈ (⊥ : Ideal S).jacobson)
    (hgen : ∀ s : S, ∃ (c : R) (u : Fin g → S), s = algebraMap R S c + ∑ j, x j * u j)
    (hf : ∀ i, algebraMap S B (f i) = 0)
    (a : Matrix (Fin g) (Fin g) (S ⊗[R] B))
    (ha : ∀ i, f i ⊗ₜ[R] (1 : B) =
      ∑ j, a i j * (x j ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B (x j)))
    (s : S) :
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S B) (AlgHom.id R B) a.det *
      (algebraMap S B s ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] algebraMap S B s) = 0 := by
  classical
  set π := Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S B) (AlgHom.id R B) with hπ
  have hker : ∀ l, a.det * (x l ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B (x l)) ∈
      RingHom.ker π := by
    intro l
    refine _root_.GlobalTheory.SocleDet.det_mul_mem (RingHom.ker π) a
      (fun j => x j ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B (x j)) l fun r => ?_
    rw [Matrix.mulVec, dotProduct, ← ha r, RingHom.mem_ker]
    simp [π, hf]
  have hmem := _root_.GlobalTheory.DiscrJacobian.mem_span_of_mu_eq_zero x hx hgen (s ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B s)
    (by simp)
  rw [Ideal.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hπs : π (s ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B s) =
      algebraMap S B s ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] algebraMap S B s := by
    simp [π]
  rw [← hπs, ← map_mul, ← hc, Finset.mul_sum]
  rw [map_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [mul_left_comm, map_mul, RingHom.mem_ker.mp (hker l), mul_zero]

open scoped TensorProduct in
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B] in
private theorem algebraMap_derivation_eq_sum_mu_mul {g : ℕ} (D : Derivation R S S) (x f : Fin g → S)
    (a : Matrix (Fin g) (Fin g) (S ⊗[R] B))
    (ha : ∀ i, f i ⊗ₜ[R] (1 : B) =
      ∑ j, a i j * (x j ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B (x j))) (i : Fin g) :
    algebraMap S B (D (f i)) = ∑ j, _root_.GlobalTheory.DiscrJacobian.mu R S B (a i j) * algebraMap S B (D (x j)) := by
  have := congrArg (_root_.GlobalTheory.DiscrJacobian.der D) (ha i)
  rw [_root_.GlobalTheory.DiscrJacobian.der_tmul, mul_one, map_sum] at this
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [_root_.GlobalTheory.DiscrJacobian.der_mul, map_sub, map_sub]
  simp

open scoped TensorProduct in
private theorem norm_sum_mul_eq_discr_mul_det {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    {d : ℕ} (b : Module.Basis (Fin d) R B) (M : Matrix (Fin d) (Fin d) R)
    (h : ∀ x : B, (∑ i, ∑ j, M i j • TensorProduct.tmul R (b i) (b j)) *
      (TensorProduct.tmul R x 1 - TensorProduct.tmul R 1 x) = 0) :
    Algebra.norm R (∑ i, ∑ j, M i j • (b i * b j)) = Algebra.discr R b * M.det := by
  classical
  have hmul : ∀ l, (∑ i, ∑ j, M i j • (b i * b j)) * b l =
      ∑ j, (∑ i, M i j * Algebra.trace R B (b i * b l)) • b j := by
    intro l
    have hs := _root_.GlobalTheory.annihilator_diagonal_form_swap (⇑b) M h (Algebra.trace R B) (b l)
    rw [← _root_.GlobalTheory.annihilator_diagonal_trace b M h, Finset.sum_mul]
    simp only [Finset.sum_mul, smul_mul_assoc]
    rw [← hs, Finset.sum_comm]
    simp only [Finset.sum_smul]
  have hmat : Algebra.leftMulMatrix b (∑ i, ∑ j, M i j • (b i * b j)) =
      M.transpose * Algebra.traceMatrix R b := by
    ext j l
    rw [Algebra.leftMulMatrix_eq_repr_mul, hmul]
    simp [Matrix.mul_apply, Algebra.traceMatrix_apply, Module.Basis.repr_sum_self,
      Finsupp.single_apply]
  rw [Algebra.norm_eq_matrix_det b, hmat, Matrix.det_mul, Matrix.det_transpose,
    Algebra.discr_def, mul_comm]

open MvPowerSeries IsLocalRing in
open scoped TensorProduct in
set_option maxHeartbeats 800000 in

theorem _root_.GlobalTheory.DiscrJacobian.associated_discr_norm_jacobian (R : Type) [CommRing R] [IsLocalRing R]
    (g d : ℕ) (f : Fin g → MvPowerSeries (Fin g) R)
    (b : Module.Basis (Fin d) R (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)))
    (hf : ∀ i, constantCoeff (f i) ∈ maximalIdeal R) :
    Associated (Algebra.discr R b) (Algebra.norm R (Ideal.Quotient.mk (Ideal.span (Set.range f))
      (Matrix.of fun i j => pderiv R j (f i)).det)) := by
  classical
  haveI : Module.Finite R (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) :=
    Module.Finite.of_basis b
  haveI : Module.FinitePresentation (MvPowerSeries (Fin g) R)
      (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) :=
    Module.finitePresentation_of_surjective (Submodule.mkQ (Ideal.span (Set.range f)))
      (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ]; exact ⟨Finset.univ.image f, by simp⟩)
  have hx : ∀ j, (X j : MvPowerSeries (Fin g) R) ∈ (⊥ : Ideal (MvPowerSeries (Fin g) R)).jacobson :=
    fun j => _root_.GlobalTheory.DiscrJacobian.X_mem_jacobson j
  have hgen : ∀ s : MvPowerSeries (Fin g) R, ∃ (c : R) (u : Fin g → MvPowerSeries (Fin g) R),
      s = algebraMap R (MvPowerSeries (Fin g) R) c + ∑ j, X j * u j := by
    intro s
    obtain ⟨u, hu⟩ := _root_.GlobalTheory.DiscrJacobian.exists_eq_C_add_sum s
    exact ⟨constantCoeff s, u, hu⟩
  have hf0 : ∀ i, algebraMap (MvPowerSeries (Fin g) R)
      (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) (f i) = 0 := fun i =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  have hrow : ∀ i, ∃ r : Fin g → MvPowerSeries (Fin g) R ⊗[R]
      (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)),
      f i ⊗ₜ[R] (1 : MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) = ∑ j, r j *
        (X j ⊗ₜ[R] 1 - (1 : MvPowerSeries (Fin g) R) ⊗ₜ[R] algebraMap (MvPowerSeries (Fin g) R)
          (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) (X j)) := by
    intro i
    have := _root_.GlobalTheory.DiscrJacobian.mem_span_of_mu_eq_zero X hx hgen
      (f i ⊗ₜ[R] (1 : MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)))
      (by simp [hf0])
    rw [Ideal.mem_span_range_iff_exists_fun] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc.symm⟩
  choose a ha using hrow
  set De := Algebra.TensorProduct.map (IsScalarTower.toAlgHom R (MvPowerSeries (Fin g) R)
    (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f))) (AlgHom.id R _) (Matrix.of a).det
    with hDe_def
  have hann : ∀ y, De * (y ⊗ₜ[R] 1 - 1 ⊗ₜ[R] y) = 0 := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact tensorMap_det_mul_tmul_sub_eq_zero X f hx hgen hf0 (Matrix.of a) ha s
  set M : Matrix (Fin d) (Fin d) R := fun i j => (b.tensorProduct b).repr De (i, j) with hM
  have hDe : De = ∑ i, ∑ j, M i j • TensorProduct.tmul R (b i) (b j) := by
    conv_lhs => rw [← (b.tensorProduct b).sum_repr De]
    rw [Fintype.sum_prod_type]
    simp [M, Module.Basis.tensorProduct_apply]
  have h : ∀ x, (∑ i, ∑ j, M i j • TensorProduct.tmul R (b i) (b j)) *
      (TensorProduct.tmul R x 1 - TensorProduct.tmul R 1 x) = 0 := by
    intro x; rw [← hDe]; exact hann x
  have hJ : ∑ i, ∑ j, M i j • (b i * b j) = Ideal.Quotient.mk (Ideal.span (Set.range f))
      (Matrix.of fun i j => pderiv R j (f i)).det := by
    have hlm : ∀ t, Algebra.TensorProduct.lmul' R (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R (MvPowerSeries (Fin g) R)
          (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f))) (AlgHom.id R _) t) =
        _root_.GlobalTheory.DiscrJacobian.mu R (MvPowerSeries (Fin g) R)
          (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) t := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => rw [map_add, map_add, hy, hz, map_add]
      | tmul s w => simp
    have hentry : ∀ i j, Ideal.Quotient.mk (Ideal.span (Set.range f)) (pderiv R j (f i)) =
        _root_.GlobalTheory.DiscrJacobian.mu R (MvPowerSeries (Fin g) R)
          (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) (a i j) := by
      intro i j
      have := algebraMap_derivation_eq_sum_mu_mul (pderiv R j) X f (Matrix.of a) ha i
      rw [← Ideal.Quotient.algebraMap_eq, this]
      simp only [Matrix.of_apply]
      rw [Finset.sum_eq_single j (fun k _ hk => by rw [pderiv_X_of_ne hk, map_zero, mul_zero])
        (by simp), pderiv_X_self, map_one, mul_one]
    calc ∑ i, ∑ j, M i j • (b i * b j) = Algebra.TensorProduct.lmul' R De := by
          rw [hDe]; simp [map_sum, Algebra.TensorProduct.lmul'_apply_tmul]
      _ = _root_.GlobalTheory.DiscrJacobian.mu R (MvPowerSeries (Fin g) R)
          (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) (Matrix.of a).det := hlm _
      _ = _ := by
          rw [← AlgHom.coe_toRingHom, RingHom.map_det, RingHom.map_det]
          congr 1
          ext i j
          simp [RingHom.mapMatrix_apply, hentry]
  have hMunit : IsUnit M.det := by
    let J : Ideal (MvPowerSeries (Fin g) (ResidueField R)) :=
      Ideal.span (Set.range fun i => MvPowerSeries.map (residue R) (f i))
    let red : MvPowerSeries (Fin g) R →ₐ[R] MvPowerSeries (Fin g) (ResidueField R) :=
      MvPowerSeries.mapAlgHom (Algebra.ofId R (ResidueField R))
    have hred : ∀ s, red s = MvPowerSeries.map (residue R) s := fun s => rfl
    let ev0 : MvPowerSeries (Fin g) R →ₐ[R] ResidueField R :=
      { toRingHom := (residue R).comp constantCoeff,
        commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }
    have hIev : Ideal.span (Set.range f) ≤ RingHom.ker ev0 := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr (hf i)
    have hIred : Ideal.span (Set.range f) ≤ RingHom.ker ((Ideal.Quotient.mkₐ R J).comp red) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      show Ideal.Quotient.mkₐ R J (red (f i)) = 0
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hred]
      exact Ideal.subset_span ⟨i, rfl⟩
    let ev : (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) →ₐ[R] ResidueField R :=
      Ideal.Quotient.liftₐ _ ev0 (fun a ha => hIev ha)
    let ρ : (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) →ₐ[R]
        (MvPowerSeries (Fin g) (ResidueField R) ⧸ J) :=
      Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R J).comp red) (fun a ha => hIred ha)
    let n : Ideal (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) :=
      Ideal.span (Set.range fun j => Ideal.Quotient.mk (Ideal.span (Set.range f)) (X j))
    have hnrad : n ≤ ((maximalIdeal R).map
        (algebraMap R (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)))).radical := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have := _root_.GlobalTheory.DiscrJacobian.map_mem_radical (R := R)
        (S := MvPowerSeries (Fin g) R)
        (Ideal.Quotient.mk_surjective : Function.Surjective (algebraMap (MvPowerSeries (Fin g) R)
          (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)))) (hx j)
      simpa [Ideal.Quotient.algebraMap_eq] using this
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hnrad
      ⟨Finset.univ.image fun j => Ideal.Quotient.mk (Ideal.span (Set.range f)) (X j),
        by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
    have hev : ∀ w ∈ n, ev w = 0 := by
      intro w hw
      have hle : n ≤ RingHom.ker ev := by
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker]
        show residue R (constantCoeff (X j : MvPowerSeries (Fin g) R)) = 0
        simp
      exact hle hw
    have hgenB : ∀ w : MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f),
        ∃ c : R, w - algebraMap R _ c ∈ n := by
      intro w
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective w
      obtain ⟨c, u, hu⟩ := hgen s
      refine ⟨c, ?_⟩
      rw [hu, map_add, Ideal.Quotient.mk_algebraMap, add_sub_cancel_left, map_sum]
      exact Ideal.sum_mem _ fun j _ => by
        rw [map_mul]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have hmB : ∀ w ∈ (maximalIdeal R).map
        (algebraMap R (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f))), ρ w = 0 := by
      intro w hw
      have hle : (maximalIdeal R).map
          (algebraMap R (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f))) ≤ RingHom.ker ρ := by
        rw [Ideal.map_le_iff_le_comap]
        intro c hc
        rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes,
          IsScalarTower.algebraMap_apply R (ResidueField R),
          show algebraMap R (ResidueField R) c = 0 from (IsLocalRing.residue_eq_zero_iff c).mpr hc,
          map_zero]
      exact hle hw
    have hpow : ∀ i, (X i : MvPowerSeries (Fin g) (ResidueField R)) ^ N ∈ J := by
      intro i
      have h1 : (Ideal.Quotient.mk (Ideal.span (Set.range f)) (X i)) ^ N ∈ n ^ N :=
        Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self
          (f := fun j => Ideal.Quotient.mk (Ideal.span (Set.range f)) (X j)) i)) N
      have h2 := hmB _ (hN h1)
      have h3 : ρ (Ideal.Quotient.mk (Ideal.span (Set.range f)) (X i)) =
          Ideal.Quotient.mk J (X i) := by
        show Ideal.Quotient.mk J (red (X i)) = _
        rw [hred, MvPowerSeries.map_X]
      rw [map_pow, h3, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at h2
      exact h2
    let ιk := Algebra.ofId (ResidueField R) (MvPowerSeries (Fin g) (ResidueField R))
    let Φ : MvPowerSeries (Fin g) R ⊗[R] (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) →ₐ[R]
        MvPowerSeries (Fin g) (ResidueField R) :=
      Algebra.TensorProduct.productMap red ((ιk.restrictScalars R).comp ev)
    have hcomp : ∀ t, Algebra.TensorProduct.productMap ρ
        ((IsScalarTower.toAlgHom R (ResidueField R) _).comp ev)
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R (MvPowerSeries (Fin g) R)
          (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f))) (AlgHom.id R _) t) =
        Ideal.Quotient.mk J (Φ t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => simp only [map_add, hy, hz]
      | tmul s w =>
        simp [Φ, ρ, ιk, Ideal.Quotient.algebraMap_eq, Algebra.ofId_apply]
        rfl
    have hrel : ∀ i, MvPowerSeries.map (residue R) (f i) = ∑ j, Φ (a i j) * X j := by
      intro i
      have hevX : ∀ j, ev (Ideal.Quotient.mk (Ideal.span (Set.range f)) (X j)) = 0 := fun j =>
        hev _ (Ideal.subset_span (Set.mem_range_self
          (f := fun j => Ideal.Quotient.mk (Ideal.span (Set.range f)) (X j)) j))
      have := congrArg Φ (ha i)
      simp only [Φ, map_sum, map_mul, map_sub, Algebra.TensorProduct.productMap_apply_tmul,
        map_one, mul_one, one_mul] at this
      rw [← hred, this]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      simp [hevX j, hred, MvPowerSeries.map_X, Ideal.Quotient.algebraMap_eq]
    have hdet := _root_.GlobalTheory.SocleDet.det_notMem_span (ResidueField R) g N
      (fun i => MvPowerSeries.map (residue R) (f i)) (Φ.toRingHom.mapMatrix (Matrix.of a))
      hrel hpow
    refine _root_.GlobalTheory.DiscrJacobian.isUnit_det_of_productMap_ne_zero b n N hN ev hev hgenB ρ De M hDe
      hann ?_
    intro h0
    apply hdet
    rw [hDe_def, hcomp, Ideal.Quotient.eq_zero_iff_mem, ← AlgHom.coe_toRingHom,
      RingHom.map_det] at h0
    exact h0
  refine ⟨hMunit.unit, ?_⟩
  rw [← hJ, norm_sum_mul_eq_discr_mul_det b M h, IsUnit.unit_spec]

end Series

end GlobalTheory.DiscrJacobian

namespace GlobalTheory

end GlobalTheory

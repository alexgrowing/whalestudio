import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.FrobStep

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

theorem im_mul_conj_lattice (L : PeriodPair) {z w : ℂ} (hz : z ∈ L.lattice) (hw : w ∈ L.lattice) :
    ∃ k : ℤ, (z * conj w).im = k * (L.ω₁ * conj L.ω₂).im := by
  have hz' : z ∈ Submodule.span ℤ {L.ω₁, L.ω₂} := hz
  have hw' : w ∈ Submodule.span ℤ {L.ω₁, L.ω₂} := hw
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz'
  obtain ⟨c, e, rfl⟩ := Submodule.mem_span_pair.mp hw'
  refine ⟨a * e - b * c, ?_⟩
  simp only [zsmul_eq_mul, map_add, map_mul, map_intCast, Complex.add_im, Complex.mul_im,
    Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]
  push_cast
  ring

theorem im_div_area (L : PeriodPair) : ∃ e : ℤ, (L.ω₁ * conj L.ω₂).im / area L = e := by
  have h : (L.ω₁ * conj L.ω₂).im = -(conj L.ω₁ * L.ω₂).im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [h]
  unfold area
  rcases lt_trichotomy (conj L.ω₁ * L.ω₂).im 0 with ht | ht | ht
  · refine ⟨1, ?_⟩
    rw [abs_of_neg ht, div_self (neg_ne_zero.mpr ht.ne)]
    simp
  · exact ⟨0, by simp [ht]⟩
  · refine ⟨-1, ?_⟩
    rw [abs_of_pos ht, neg_div, div_self ht.ne']
    simp

theorem stdH_apply (L : PeriodPair) {N : Type*} [Fintype N] [DecidableEq N] (z w : N → ℂ) :
    stdH L N z w = ∑ i, z i * ((area L : ℝ) : ℂ)⁻¹ * conj (w i) := by
  simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem stdLat_int (L : PeriodPair) {N : Type*} [Fintype N] [DecidableEq N] {z w : N → ℂ}
    (hz : z ∈ stdLat L N) (hw : w ∈ stdLat L N) : ∃ k : ℤ, altE (stdH L N) z w = k := by
  have hzi : ∀ i, z i ∈ L.lattice := fun i =>
    (show ∀ i ∈ (Set.univ : Set N), z i ∈ L.lattice.toAddSubgroup from hz) i (Set.mem_univ i)
  have hwi : ∀ i, w i ∈ L.lattice := fun i =>
    (show ∀ i ∈ (Set.univ : Set N), w i ∈ L.lattice.toAddSubgroup from hw) i (Set.mem_univ i)
  choose k hk using fun i => im_mul_conj_lattice L (hzi i) (hwi i)
  obtain ⟨e, he⟩ := im_div_area L
  refine ⟨(∑ i, k i) * e, ?_⟩
  have hterm : ∀ i, (z i * ((area L : ℝ) : ℂ)⁻¹ * conj (w i)).im =
      (k i : ℝ) * ((L.ω₁ * conj L.ω₂).im / area L) := by
    intro i
    rw [show z i * ((area L : ℝ) : ℂ)⁻¹ * conj (w i) = (((area L)⁻¹ : ℝ) : ℂ) * (z i * conj (w i)) by
      push_cast; ring, Complex.im_ofReal_mul, hk i]
    ring
  unfold altE
  rw [stdH_apply, Complex.im_sum, Finset.sum_congr rfl (fun i _ => hterm i), he, ← Finset.sum_mul]
  push_cast
  ring

theorem idx_smul_mem {n : Type} [Fintype n] [DecidableEq n] (L : PeriodPair) (Λ : AddSubgroup (n → ℂ))
    (g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) {y : Fin 4 × n → ℂ} (hy : y ∈ pow4 Λ) :
    relIdx (stdLat L (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) • g₁ y
      ∈ stdLat L (Fin 4 × n) := by
  have hmem : g₁ y ∈ imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) :=
    AddSubgroup.mem_map.mpr ⟨y, hy, rfl⟩
  have h1 := AddSubgroup.nsmul_index_mem ((stdLat L (Fin 4 × n)).addSubgroupOf
    (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) ⟨g₁ y, hmem⟩
  rw [AddSubgroup.mem_addSubgroupOf] at h1
  simpa [relIdx, AddSubgroup.relIndex] using h1

def emb {n : Type} (a : Fin 4) (v : n → ℂ) : Fin 4 × n → ℂ := fun x => if x.1 = a then v x.2 else 0

theorem emb_mem {n : Type} {Λ : AddSubgroup (n → ℂ)} (a : Fin 4) {v : n → ℂ} (hv : v ∈ Λ) :
    emb a v ∈ pow4 Λ := by
  intro b
  by_cases h : b = a
  · subst h
    convert hv using 1
    funext i
    simp [slice, emb]
  · convert Λ.zero_mem using 1
    funext i
    simp [slice, emb, h]

theorem matrixForm_diagBlocks_blockEmbed {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (x : Fin 4 × n → ℂ) (a : Fin 4)
    (v : n → ℂ) : matH (blk4 h) x (emb a v) = matH h (slice a x) v := by
  simp only [matH, LinearMap.mk₂'ₛₗ_apply]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
    · simp [blk4, emb, slice]
    · intro c _ hc
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [emb, hc]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hc : c = a
    · subst hc
      simp [blk4, hb]
    · simp [emb, hc]
  · simp

theorem mem_latticeFourfold_of_mem_dualLattice {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (hΛ : IsSelfDual (matH h) Λ) {x : Fin 4 × n → ℂ} (hx : x ∈ dualLat (matH (blk4 h)) (pow4 Λ)) :
    x ∈ pow4 Λ := by
  have hx' : ∀ y ∈ pow4 Λ, ∃ m : ℤ, altE (matH (blk4 h)) x y = (m : ℝ) := hx
  intro a
  rw [← hΛ]
  show ∀ y ∈ Λ, ∃ m : ℤ, altE (matH h) (slice a x) y = (m : ℝ)
  intro v hv
  obtain ⟨m, hm⟩ := hx' (emb a v) (emb_mem a hv)
  refine ⟨m, ?_⟩
  unfold altE at hm ⊢
  rw [matrixForm_diagBlocks_blockEmbed] at hm
  exact hm

theorem idx_smul_symm_mem {n : Type} [Fintype n] [DecidableEq n] (L : PeriodPair) (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (hΛ : IsSelfDual (matH h) Λ) (g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hIso : IsIsom (matH (blk4 h)) (stdH L (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
    {z : Fin 4 × n → ℂ} (hz : z ∈ stdLat L (Fin 4 × n)) :
    g₁.symm (relIdx (stdLat L (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) • z)
      ∈ pow4 Λ := by
  apply mem_latticeFourfold_of_mem_dualLattice h Λ hΛ
  show ∀ y ∈ pow4 Λ, ∃ m : ℤ, altE (matH (blk4 h)) (g₁.symm (relIdx (stdLat L (Fin 4 × n))
    (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) • z)) y = (m : ℝ)
  intro y hy
  obtain ⟨k, hk⟩ := stdLat_int L hz (idx_smul_mem L Λ g₁ hy)
  refine ⟨k, ?_⟩
  unfold altE at hk ⊢
  rw [← hIso]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, map_nsmul, LinearMap.smul_apply] at hk ⊢
  exact hk

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame

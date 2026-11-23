import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.RelIndexNeZeroAndLeOfNsmulMem

set_option linter.unusedSectionVars false

noncomputable section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Matrix TensorProduct NumberField IsDedekindDomain GroundTheory.Automorphic
open scoped Pointwise

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Span

variable {κ : Type*} [Fintype κ] (b : Basis κ F E) (v : Basis ι E W)

def coordSpan (c : F) : (ι × κ → 𝓞 F) →ₗ[ℤ] W :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun z => ∑ a : ι × κ, (algebraMap F E (c⁻¹ * algebraMap (𝓞 F) F (z a)) * b a.2) • v a.1
      map_zero' := by simp
      map_add' := fun z z' => by
        simp only [Pi.add_apply, map_add, mul_add, add_mul, add_smul, Finset.sum_add_distrib] }

theorem mem_range_coordSpan {c : F} (hc : c ≠ 0) {x : W}
    (hx : ∀ i k, IsIntegral ℤ (c * b.repr (v.repr x i) k)) :
    x ∈ LinearMap.range (coordSpan b v c) := by
  choose z hz using fun a : ι × κ =>
    (⟨⟨_, hx a.1 a.2⟩, rfl⟩ : ∃ z : 𝓞 F, algebraMap (𝓞 F) F z = c * b.repr (v.repr x a.1) a.2)
  refine ⟨z, ?_⟩
  show ∑ a : ι × κ, (algebraMap F E (c⁻¹ * algebraMap (𝓞 F) F (z a)) * b a.2) • v a.1 = x
  simp only [hz, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [← v.sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [← Finset.sum_smul]
  congr 1
  conv_rhs => rw [← b.sum_repr (v.repr x i)]
  simp only [Algebra.smul_def]

end Span

theorem isTorsionFree_int_of_module (K' V' : Type*) [Field K'] [CharZero K'] [AddCommGroup V']
    [Module K' V'] : Module.IsTorsionFree ℤ V' :=
  Module.IsTorsionFree.comap (S := K') (fun n : ℤ => (n : K'))
    (fun r hr => isRegular_iff_ne_zero.2 (Int.cast_ne_zero.2 (isRegular_iff_ne_zero.1 hr)))
    (fun r m => Int.cast_smul_eq_zsmul K' r m)

section DIntegral

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ F E) (h : HermitianForm F E W)
  (v : Basis ι E W)

theorem repr_repr_smul_inv_int (d : ℤ) (x : W) (i : ι) (k : κ) :
    b.repr (v.repr ((d : E)⁻¹ • x) i) k = (d : F)⁻¹ * b.repr (v.repr x i) k := by
  have : (d : E)⁻¹ = algebraMap F E (d : F)⁻¹ := by rw [map_inv₀, map_intCast]
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, this, ← Algebra.smul_def, map_smul,
    Finsupp.smul_apply, smul_eq_mul]

theorem repr_repr_nsmul (n : ℕ) (x : W) (i : ι) (k : κ) :
    b.repr (v.repr (n • x) i) k = n * b.repr (v.repr x i) k := by
  rw [map_nsmul, Finsupp.smul_apply, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

theorem isDIntegral_dictLattice {d : ℤ} (hd0 : d ≠ 0)
    (hd : ∀ (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) (x y : ι → F ⊗[F] E),
      x ∈ coreLattice b (gram h.toSesq v) g → y ∈ coreLattice b (gram h.toSesq v) g →
        IsIntegral ℤ ((d : E) * pairE (gram h.toSesq v) x y))
    {m : ℤ} (hm0 : m ≠ 0)
    (hm : ∀ (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) (y : ι → F ⊗[F] E),
      (∀ x ∈ coreLattice b (gram h.toSesq v) g, IsIntegral ℤ (pairE (gram h.toSesq v) y x)) →
        (m : F) • y ∈ coreLattice b (gram h.toSesq v) g)
    (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) :
    IsDIntegral h ((m * d * d).natAbs ^ finrank ℤ (ι × κ → 𝓞 F)) (dictLattice b h v d g) := by
  classical
  haveI : Module.IsTorsionFree ℤ W := isTorsionFree_int_of_module E W
  have hdE : (d : E) ≠ 0 := by exact_mod_cast hd0
  have hdF : (d : F) ≠ 0 := by exact_mod_cast hd0
  have hsmulL : ∀ (c : E) (x y : W), h.toSesq (c • x) y = conj F E c * h.toSesq x y := by
    intro c x y
    rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]
    rfl
  have hsmulR : ∀ (c : E) (x y : W), h.toSesq x (c • y) = c * h.toSesq x y := by
    intro c x y
    rw [map_smul, smul_eq_mul]
  have hconjd : conj F E (d : E) = d := map_intCast _ _
  have hdI : IsIntegral ℤ (d : E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := d))

  have hint : ∀ x ∈ dictLattice b h v d g, ∀ y ∈ dictLattice b h v d g, IsIntegral ℤ (h.toSesq x y) := by
    intro x hx y hy
    have e : h.toSesq x y = (d : E) * ((d : E) * pairE (gram h.toSesq v) (coordEquiv F v ((d : E)⁻¹ • x))
        (coordEquiv F v ((d : E)⁻¹ • y))) := by
      rw [pairE_coordEquiv, hsmulL, hsmulR, map_inv₀, hconjd]
      field_simp
    rw [e]
    exact hdI.mul (hd g _ _ hx hy)

  obtain ⟨m', hm'0, hm'⟩ := exists_int_isIntegral_coords b (isUnit_det_gram h v) g
  set c : F := (m' : F) * (d : F)⁻¹ with hcdef
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hm'0) (inv_ne_zero hdF)
  have hcoordL : ∀ x ∈ dictLattice b h v d g, ∀ i k, IsIntegral ℤ (c * b.repr (v.repr x i) k) := by
    intro x hx i k
    have hx' : coordEquiv F v ((d : E)⁻¹ • x) ∈ coreLattice b (gram h.toSesq v) g := hx
    have := hm' _ (coreLattice_le_adelicLattice b g hx') (i, k)
    rw [vecCoords_coordEquiv, repr_repr_smul_inv_int] at this
    rw [hcdef, mul_assoc]
    exact this
  have hLQ : (dictLattice b h v d g).toIntSubmodule ≤ LinearMap.range (coordSpan b v c) :=
    fun x hx => mem_range_coordSpan b v hc (hcoordL x hx)

  set M : ℤ := m * d * d with hMdef
  have hM0 : M.natAbs ≠ 0 := Int.natAbs_ne_zero.2 (mul_ne_zero (mul_ne_zero hm0 hd0) hd0)
  have hLP : dictLattice b h v d g ≤ dualLattice h (dictLattice b h v d g) := fun x hx y hy => (mem_integralClosure_iff ℤ E).2 (hint x hx y hy)
  have hnL : ∀ y ∈ dualLattice h (dictLattice b h v d g), M.natAbs • y ∈ dictLattice b h v d g := by
    intro y hy
    have h1 : (m : F) • coordEquiv F v ((d : E) • y) ∈ coreLattice b (gram h.toSesq v) g := by
      refine hm g _ fun X hX => ?_
      set x0 := (coordEquiv F v).symm X
      have hx0 : (d : E) • x0 ∈ dictLattice b h v d g := by
        rw [mem_dictLattice, inv_smul_smul₀ hdE, AddEquiv.apply_symm_apply]
        exact hX
      have h2 := (mem_integralClosure_iff ℤ E).1 (hy _ hx0)
      rw [show X = coordEquiv F v x0 from (AddEquiv.apply_symm_apply _ X).symm, pairE_coordEquiv,
        hsmulL, hconjd, ← hsmulR]
      exact h2
    have hMy : M • y ∈ dictLattice b h v d g := by
      rw [mem_dictLattice]
      have e : (d : E)⁻¹ • (M • y) = m • ((d : E) • y) := by
        rw [← Int.cast_smul_eq_zsmul E M, ← Int.cast_smul_eq_zsmul E m, smul_smul, smul_smul, hMdef]
        congr 1
        push_cast
        field_simp
      rw [e, map_zsmul, ← Int.cast_smul_eq_zsmul F]
      exact h1
    have : (M.natAbs : ℤ) • y ∈ dictLattice b h v d g := by
      rcases Int.natAbs_eq M with hM | hM
      · rwa [← hM]
      · rw [show (M.natAbs : ℤ) = -M by omega, neg_smul]
        exact neg_mem hMy
    rwa [natCast_zsmul] at this
  have hcn : c * (M.natAbs : F) ≠ 0 := mul_ne_zero hc (by exact_mod_cast hM0)
  have hPQ : (dualLattice h (dictLattice b h v d g)).toIntSubmodule ≤ LinearMap.range (coordSpan b v (c * M.natAbs)) := by
    intro y hy
    refine mem_range_coordSpan b v hcn fun i k => ?_
    have := hcoordL _ (hnL y hy) i k
    rw [repr_repr_nsmul] at this
    rw [mul_assoc]
    exact this
  obtain ⟨hne, hle⟩ := relIndex_ne_zero_and_le_of_nsmul_mem hLP hPQ hM0 hnL
  refine ⟨⟨fun a x hx => ?_, ?_, ?_⟩, fun x hx y hy => (mem_integralClosure_iff ℤ E).2 (hint x hx y hy),
    hne, hle.trans (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hM0)
      (LinearMap.finrank_range_le (coordSpan b v (c * M.natAbs))))⟩
  ·
    rw [mem_dictLattice, smul_comm, coordEquiv_smul]
    exact smul_mem_coreLattice b hx a
  ·
    haveI : Module.Finite ℤ (dictLattice b h v d g).toIntSubmodule :=
      Module.Finite.of_injective (Submodule.inclusion hLQ) (Submodule.inclusion_injective hLQ)
    have := Module.Finite.iff_fg.1 (inferInstance : Module.Finite ℤ (dictLattice b h v d g).toIntSubmodule)
    exact (Submodule.fg_iff_addSubgroup_fg _).1 this
  ·
    rw [eq_top_iff, ← v.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨n, hn0, hn⟩ := exists_int_smul_single_mem_coreLattice b g i
    have hmem : (d * n) • v i ∈ dictLattice b h v d g := by
      rw [mem_dictLattice]
      have e1 : (d : E)⁻¹ • ((d * n) • v i) = n • v i := by
        rw [← Int.cast_smul_eq_zsmul E (d * n), ← Int.cast_smul_eq_zsmul E n, smul_smul]
        congr 1
        push_cast
        field_simp
      have e2 : coordEquiv F v (v i) = Pi.single i (1 : F ⊗[F] E) := by
        funext j
        rw [coordEquiv_apply, Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
        by_cases hij : i = j
        · subst hij
          simp [Algebra.TensorProduct.one_def]
        · rw [if_neg hij, if_neg (Ne.symm hij), TensorProduct.tmul_zero]
      rw [e1, map_zsmul, e2, ← Int.cast_smul_eq_zsmul F]
      exact hn
    have hvi : v i = ((d * n : ℤ) : E)⁻¹ • ((d * n) • v i) := by
      rw [← Int.cast_smul_eq_zsmul E (d * n), inv_smul_smul₀ (by exact_mod_cast mul_ne_zero hd0 hn0)]
    rw [SetLike.mem_coe, hvi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end DIntegral

variable [IsTotallyReal F] [IsTotallyComplex E]

theorem AdelicLatticeDictionary.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    AdelicLatticeDictionary.Statement h v := by
  classical
  obtain ⟨d, hd0, hd⟩ := exists_int_isIntegral_pairE (Module.finBasis F E) (gram h.toSesq v)
  obtain ⟨m, hm0, hm⟩ := exists_int_smul_mem_coreLattice_of_dual (Module.finBasis F E)
    (isUnit_det_gram h v)
  exact ⟨coreStabilizer (Module.finBasis F E) (gram h.toSesq v), _,
    dictLattice (Module.finBasis F E) h v d,
    isCompact_coreStabilizer (Module.finBasis F E) _ (isUnit_det_gram h v),
    isOpen_coreStabilizer (Module.finBasis F E) _,
    fun g => isDIntegral_dictLattice (Module.finBasis F E) h v hd0 hd hm0 hm g,
    fun γ g => dictLattice_diagonal_mul d γ g,
    fun g g' => dictLattice_eq_iff hd0⟩

end GroundTheory.Heights₂.Heights.FiniteCovolume

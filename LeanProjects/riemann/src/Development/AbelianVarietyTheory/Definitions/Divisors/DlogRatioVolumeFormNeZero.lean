import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR

namespace GlobalTheory.PD

section Proj

variable (k : Type) [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} (x : Fin (d + 1) → F)

structure IsPd : Prop where
  ne : ∀ i, x i ≠ 0
  indep : AlgebraicIndependent k fun j : Fin d => x j.succ / x 0
  gen : IntermediateField.adjoin k (Set.range fun j : Fin d => x j.succ / x 0) = ⊤

def rA (I : Finset (Fin (d + 1))) : Subalgebra k F := Algebra.adjoin k {y | ∃ i ∈ I, ∃ j, y = x j / x i}

def tw (m : ℤ) (I : Finset (Fin (d + 1))) : Submodule k F :=
  ⨅ i ∈ I, (Subalgebra.toSubmodule (rA k x I)).comap (LinearMap.mulLeft k ((x 0 / x i) ^ m))

def omA (I : Finset (Fin (d + 1))) : Submodule k F :=
  ⨅ i ∈ I, (Subalgebra.toSubmodule (rA k x I)).comap (LinearMap.mulLeft k (∏ j, x i / x j))

def IsRes (ρ : F →ₗ[k] k) : Prop := ρ 1 = 1 ∧ ∀ m : Fin (d + 1) → ℤ, ∑ j, m j = 0 → m ≠ 0 → ρ (∏ j, x j ^ m j) = 0

variable {W W' : Type} [AddCommGroup W] [Module F W] [Module k W] [IsScalarTower k F W]
  [AddCommGroup W'] [Module F W'] [Module k W'] [IsScalarTower k F W']

structure IsBundle (L : Finset (Fin (d + 1)) → Submodule k W) : Prop where
  fg : ∀ i, ∃ s : Finset W, L {i} = (Submodule.span (rA k x {i}) (s : Set W)).restrictScalars k ∧ Submodule.span F (s : Set W) = ⊤
  proj : ∀ i, Module.Projective (rA k x {i}) (Submodule.span (rA k x {i}) (L {i} : Set W))
  loc : ∀ I, ∀ i ∈ I, L I = (Submodule.span (rA k x I) (L {i} : Set W)).restrictScalars k

def dualFam (β : W →ₗ[F] W' →ₗ[F] F) (L : Finset (Fin (d + 1)) → Submodule k W) (I : Finset (Fin (d + 1))) : Submodule k W' :=
  ⨅ w ∈ L I, (omA k x I).comap ((β w).restrictScalars k)

def kpair (ρ : F →ₗ[k] k) (β : W →ₗ[F] W' →ₗ[F] F) : W →ₗ[k] W' →ₗ[k] k := (β.restrictScalars₁₂ k k).compr₂ ρ

def SD (ρ : F →ₗ[k] k) (β : W →ₗ[F] W' →ₗ[F] F) (L : Finset (Fin (d + 1)) → Submodule k W) : Prop :=
  Perf (cech L) (cech (dualFam k x β L)) (cupPair (kpair k ρ β)) d

end Proj

section Forms

variable (k : Type) [Field k] (K : Type) [Field K] [Algebra k K]

def omB (B : Subalgebra k K) (q : ℕ) : Submodule k (DR k K) :=
  Submodule.span k {y | ∃ b ∈ B, ∃ v : Fin q → K, (∀ j, v j ∈ B) ∧ y = b • ExteriorAlgebra.ιMulti K q fun j => D k K (v j)}

def trunc (b : ℕ) : DR k K →ₗ[k] DR k K :=
  ∑ q ∈ Finset.range b, (GradedAlgebra.proj (fun i : ℕ => ⋀[K]^i Ω[K⁄k]) q).restrictScalars k

def sg : DR k K →ₐ[k] DR k K := (sgn (R := k) (B := K)).restrictScalars k

variable {K} {ι : Type} [LinearOrder ι]

def tot (B : Finset ι → Subalgebra k K) (a b : ℕ) : Cx k (Finset ι → DR k K) :=
  ⟨totC (fun q s => omB k K (B s) q) a b, totD (trunc k K b ∘ₗ dDR k K)⟩

def formPair [Fintype ι] (t : DR k K →ₗ[k] k) : (Finset ι → DR k K) →ₗ[k] (Finset ι → DR k K) →ₗ[k] k :=
  ∑ j : ι, ((LinearMap.mul k (DR k K)).compr₂ t).compl₁₂
    ((sg k K ^ ((Finset.univ.filter (j ≤ ·)).card - 1)).toLinearMap ∘ₗ LinearMap.proj (Finset.univ.filter (· ≤ j)))
    (LinearMap.proj (Finset.univ.filter (j ≤ ·)))

variable (K) {F : Type} [Field F] [Algebra k F] [Algebra F K] [IsScalarTower k F K] {d : ℕ} (x : Fin (d + 1) → F)

def rB (I : Finset (Fin (d + 1))) : Subalgebra k K := (integralClosure (rA k x I) K).restrictScalars k

structure IsFinCover : Prop where
  pd : IsPd k x
  fin : FiniteDimensional F K
  smooth : ∀ i, Algebra.Smooth k (rB k K x {i})

  [sep : Algebra.IsSeparable F K]

def vol0 : DR k K :=
  ExteriorAlgebra.ιMulti K d fun j => (algebraMap F K (x j.succ / x 0))⁻¹ • D k K (algebraMap F K (x j.succ / x 0))

def IsTop (τ : DR k K →ₗ[K] K) : Prop := τ (vol0 k K x) = 1 ∧ ∀ q, q ≠ d → ∀ y ∈ ⋀[K]^q Ω[K⁄k], τ y = 0

variable {K} in

def trF (τ : DR k K →ₗ[K] K) (ρ : F →ₗ[k] k) : DR k K →ₗ[k] k :=
  ρ ∘ₗ (Algebra.trace F K).restrictScalars k ∘ₗ τ.restrictScalars k

def hyp : Finset (Fin (d + 1)) → DR k K := fun s =>
  ∑ i ∈ s, ∑ j ∈ s, if s.card = 2 ∧ i < j then (algebraMap F K (x j / x i))⁻¹ • ι1 (D k K (algebraMap F K (x j / x i))) else 0

end Forms

section API

variable {k : Type} [Field k] {K : Type} [Field K] [Algebra k K] {F : Type} [Field F] [Algebra k F] [Algebra F K]
  [IsScalarTower k F K] {d : ℕ} {x : Fin (d + 1) → F}

theorem IsFinCover.of_charZero [CharZero F] (pd : IsPd k x) (fin : FiniteDimensional F K)
    (smooth : ∀ i, Algebra.Smooth k (rB k K x {i})) : IsFinCover k K x := by
  have := fin
  have : Algebra.IsSeparable F K := inferInstance
  exact ⟨pd, fin, smooth⟩

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem IsFinCover.exists_basis (h : IsFinCover k K x) :
    ∃ b : Module.Basis (Fin d) K Ω[K⁄k], ∀ j, b j = D k K (algebraMap F K (x j.succ / x 0)) := by
  have := h.fin
  have := h.sep
  let t : Fin d → F := fun j => x j.succ / x 0
  let A := MvPolynomial (Fin d) k
  let : Algebra A F := (MvPolynomial.aeval t).toRingHom.toAlgebra
  have : IsScalarTower k A F := IsScalarTower.of_algebraMap_eq fun r =>
    ((MvPolynomial.aeval t).commutes r).symm
  have hinj : Function.Injective (algebraMap A F) := h.pd.indep
  have : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective A F).mpr hinj
  have : IsFractionRing A F := IsFractionRing.of_field A F fun z => by
    have hz : z ∈ IntermediateField.adjoin k (Set.range t) := by
      rw [h.pd.gen]; exact IntermediateField.mem_top
    obtain ⟨r, hr, s, hs, rfl⟩ := (IntermediateField.mem_adjoin_iff_div (F := k) (S := Set.range t)).mp hz
    rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.mem_range] at hr hs
    obtain ⟨p, rfl⟩ := hr
    obtain ⟨q, rfl⟩ := hs
    exact ⟨p, q, rfl⟩
  have : Algebra.FormallyEtale A F := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  have : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  let : Algebra A K := ((algebraMap F K).comp (algebraMap A F)).toAlgebra
  have : IsScalarTower A F K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k A K := IsScalarTower.of_algebraMap_eq fun r => by
    change _ = algebraMap F K (algebraMap A F (algebraMap k A r))
    rw [← IsScalarTower.algebraMap_apply k A F, ← IsScalarTower.algebraMap_apply k F K]
  have : Algebra.FormallyEtale A K := Algebra.FormallyEtale.comp A F K
  refine ⟨((KaehlerDifferential.mvPolynomialBasis k (Fin d)).baseChange K).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A K), fun j => ?_⟩
  have hb0 : KaehlerDifferential.mvPolynomialBasis k (Fin d) j = D k A (MvPolynomial.X j) :=
    (KaehlerDifferential.mvPolynomialBasis k (Fin d)).repr.injective (by
      rw [Module.Basis.repr_self, KaehlerDifferential.mvPolynomialBasis_repr_D_X])
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, hb0,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply, KaehlerDifferential.mapBaseChange_tmul,
    one_smul, KaehlerDifferential.map_D]
  change D k K (algebraMap F K (MvPolynomial.aeval t (MvPolynomial.X j))) = _
  rw [MvPolynomial.aeval_X]

theorem IsFinCover.exists_isTop (h : IsFinCover k K x) : ∃ τ : DR k K →ₗ[K] K, IsTop k K x τ := by
  obtain ⟨b, hb⟩ := h.exists_basis
  have hne : ∀ j : Fin d, algebraMap F K (x j.succ / x 0) ≠ 0 := fun j =>
    (map_ne_zero _).mpr (div_ne_zero (h.pd.ne _) (h.pd.ne _))
  let b' := b.unitsSMul fun j => (Units.mk0 _ (hne j))⁻¹
  have hb' : ∀ j, b' j =
      (algebraMap F K (x j.succ / x 0))⁻¹ • D k K (algebraMap F K (x j.succ / x 0)) := by
    intro j
    simp [b', Module.Basis.unitsSMul_apply, Units.smul_def, hb]
  let φ : ⋀[K]^d Ω[K⁄k] →ₗ[K] K := exteriorPower.alternatingMapLinearEquiv b'.det
  let τ : DR k K →ₗ[K] K := φ ∘ₗ DirectSum.component K ℕ (fun i => ⋀[K]^i Ω[K⁄k]) d ∘ₗ
    (DirectSum.decomposeLinearEquiv (fun i : ℕ => ⋀[K]^i Ω[K⁄k])).toLinearMap
  have key : ∀ y : DR k K, τ y = φ (DirectSum.decompose (fun i : ℕ => ⋀[K]^i Ω[K⁄k]) y d) :=
    fun y => rfl
  refine ⟨τ, ?_⟩
  unfold IsTop
  constructor
  · have hv : vol0 k K x = ExteriorAlgebra.ιMulti K d b' := by
      unfold vol0
      congr 1
      funext j
      exact (hb' j).symm
    rw [key, hv, ← exteriorPower.ιMulti_apply_coe, DirectSum.decompose_coe, DirectSum.of_eq_same,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, Module.Basis.det_self]
  · intro q hq y hy
    have hz : DirectSum.decompose (fun i : ℕ => ⋀[K]^i Ω[K⁄k]) y d = 0 := by
      ext1
      exact DirectSum.decompose_of_mem_ne _ hy hq
    rw [key, hz, map_zero]

theorem IsFinCover.dlogRatioVolumeForm_ne_zero (h : IsFinCover k K x) : vol0 k K x ≠ 0 := by
  obtain ⟨τ, hτ⟩ := h.exists_isTop
  unfold IsTop at hτ
  intro h0
  have h1 := hτ.1
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

example (h : IsFinCover k K x) : Algebra.IsSeparable F K ∧ vol0 k K x ≠ 0 := ⟨h.sep, h.dlogRatioVolumeForm_ne_zero⟩

end API

end GlobalTheory.PD

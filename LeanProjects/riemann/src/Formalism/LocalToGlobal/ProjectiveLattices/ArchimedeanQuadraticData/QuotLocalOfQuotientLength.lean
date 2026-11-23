import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotSt
import Formalism.FilteredPoleLength.LocalDescentLevels.MemSpanBasisFun

namespace Formalism.L2.Pj.QAt

namespace TieQL

open Module

variable {O Q : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [AddCommGroup Q] [Module O Q] {ρ : ℕ}

noncomputable def coordK (b : Basis (Fin ρ) O Q) : Q →ₗ[O] (Fin ρ → FractionRing O) where
  toFun q k := algebraMap O (FractionRing O) (b.repr q k)
  map_add' x y := by ext k; simp
  map_smul' r x := by ext k; simp [Algebra.smul_def]

theorem coordK_injective (b : Basis (Fin ρ) O Q) : Function.Injective (coordK b) := by
  intro x y h
  apply b.repr.injective
  ext k
  have hk := congrFun h k
  simp only [coordK, LinearMap.coe_mk, AddHom.coe_mk] at hk
  exact IsFractionRing.injective O (FractionRing O) hk

noncomputable def matA (b : Basis (Fin ρ) O Q) (c : Fin ρ → (Q →ₗ[O] O)) :
    Matrix (Fin ρ) (Fin ρ) O :=
  Matrix.of fun i k => c i (b k)

theorem c_eq_sum (b : Basis (Fin ρ) O Q) (c : Fin ρ → (Q →ₗ[O] O)) (i : Fin ρ) (q : Q) :
    c i q = ∑ k, matA b c i k * b.repr q k := by
  conv_lhs => rw [← b.sum_repr q]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

noncomputable def cK (b : Basis (Fin ρ) O Q) (c : Fin ρ → (Q →ₗ[O] O)) :
    (Fin ρ → FractionRing O) →ₗ[FractionRing O] (Fin ρ → FractionRing O) :=
  Matrix.toLin' ((matA b c).map (algebraMap O (FractionRing O)))

theorem cK_coordK (b : Basis (Fin ρ) O Q) (c : Fin ρ → (Q →ₗ[O] O)) (q : Q) (i : Fin ρ) :
    cK b c (coordK b q) i = algebraMap O (FractionRing O) (c i q) := by
  rw [c_eq_sum b c i q, map_sum]
  simp only [cK, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, coordK,
    LinearMap.coe_mk, AddHom.coe_mk, map_mul]

theorem det_mul_eq (b : Basis (Fin ρ) O Q) (c : Fin ρ → (Q →ₗ[O] O)) (th : Fin ρ → Q) :
    (Matrix.of fun i j => c i (th j)) = matA b c * Matrix.of fun k j => b.repr (th j) k := by
  ext i j
  rw [Matrix.of_apply, Matrix.mul_apply, c_eq_sum b c i (th j)]
  rfl

theorem inf_ker_eq_bot (b : Basis (Fin ρ) O Q) (c : Fin ρ → (Q →ₗ[O] O)) (th : Fin ρ → Q)
    (hdet : (Matrix.of fun i j => c i (th j)).det ≠ 0) :
    LinearMap.range (coordK b) ⊓ (LinearMap.ker (cK b c)).restrictScalars O = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf, LinearMap.mem_range] at hv
  obtain ⟨⟨q, rfl⟩, hv⟩ := hv
  rw [Submodule.restrictScalars_mem, LinearMap.mem_ker] at hv
  have hA : (matA b c).det ≠ 0 := by
    intro h0
    apply hdet
    rw [det_mul_eq b c th, Matrix.det_mul, h0, zero_mul]
  have hc : ∀ i, c i q = 0 := by
    intro i
    have h1 : cK b c (coordK b q) i = 0 := by rw [hv]; rfl
    rw [cK_coordK] at h1
    exact IsFractionRing.injective O (FractionRing O) (by rw [h1, map_zero])
  have hvec : (matA b c).mulVec (fun k => b.repr q k) = 0 := by
    funext i
    rw [Pi.zero_apply, ← hc i, c_eq_sum b c i q]
    rfl
  have hr := Matrix.eq_zero_of_mulVec_eq_zero hA hvec
  have hq : q = 0 := by
    apply b.repr.injective
    ext k
    simpa using congrFun hr k
  rw [hq, map_zero]

end TieQL

open TieQL in
theorem quotLocal_of_quotientLength (h : Formalism.LatticeBaseChangeAlt.QuotientLength) :
    ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotLocalStatement := by
  intro O Q _ _ _ _ _ ρ hb c th hdet
  obtain ⟨b⟩ := hb
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmat : (Matrix.of fun i j => cK b c (coordK b (th j)) i) =
      (Matrix.of fun i j => c i (th j)).map (algebraMap O (FractionRing O)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.map_apply, cK_coordK]
  have hdetK : algebraMap O (FractionRing O) (Matrix.of fun i j => c i (th j)).det =
      (Matrix.of fun i j => cK b c (coordK b (th j)) i).det * algebraMap O (FractionRing O) 1 := by
    rw [map_one, mul_one, hmat, RingHom.map_det]
    rfl
  obtain ⟨m, hm, hle⟩ := h O (FractionRing O) (Fin ρ → FractionRing O) ϖ hϖ ρ (cK b c)
    (LinearMap.ker (cK b c)) le_rfl (LinearMap.range (coordK b)) 0 0 (fun j => coordK b (th j))
    (by
      rintro x ⟨q, rfl⟩ i
      exact ⟨c i q, by simp [cK_coordK]⟩)
    (by intro j; simp)
    _ 1 hdet one_ne_zero hdetK
  let eQ : Q ≃ₗ[O] LinearMap.range (coordK b) := LinearEquiv.ofInjective (coordK b) (coordK_injective b)
  have hT : ((LinearMap.range (coordK b) ⊓ (LinearMap.ker (cK b c)).restrictScalars O) ⊔
      Submodule.span O (Set.range fun j => (algebraMap O (FractionRing O) ϖ) ^ (0 : ℕ) • coordK b (th j))).comap
        (LinearMap.range (coordK b)).subtype =
      (Submodule.span O (Set.range th)).map (eQ : Q →ₗ[O] LinearMap.range (coordK b)) := by
    rw [inf_ker_eq_bot b c th hdet, bot_sup_eq]
    simp only [pow_zero, one_smul]
    ext ⟨v, hv⟩
    obtain ⟨q, rfl⟩ := LinearMap.mem_range.mp hv
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map]
    constructor
    · intro hq
      have h1 : coordK b q ∈ (Submodule.span O (Set.range th)).map (coordK b) := by
        rw [Submodule.map_span, ← Set.range_comp]
        exact hq
      obtain ⟨y, hy, hyq⟩ := h1
      refine ⟨y, hy, Subtype.ext ?_⟩
      rw [LinearEquiv.coe_coe, LinearEquiv.ofInjective_apply]
      exact hyq
    · rintro ⟨y, hy, hyq⟩
      have h2 : coordK b y = coordK b q := by
        have h3 := congrArg Subtype.val hyq
        rwa [LinearEquiv.coe_coe, LinearEquiv.ofInjective_apply] at h3
      rw [← h2]
      have h4 := Submodule.mem_map_of_mem (f := coordK b) hy
      rw [Submodule.map_span, ← Set.range_comp] at h4
      exact h4
  have e := Submodule.Quotient.equiv (Submodule.span O (Set.range th)) _ eQ hT.symm
  have hm' : m ≤ (IsDiscreteValuationRing.addVal O (Matrix.of fun i j => c i (th j)).det).toNat := by
    simp at hle
    exact_mod_cast hle
  calc Module.length O (Q ⧸ Submodule.span O (Set.range th)) = (m : ℕ∞) := e.length_eq.trans hm
    _ ≤ _ := (Nat.cast_le.mpr hm').trans (ENat.coe_toNat_le_self _)

theorem quotLocal_holds : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotLocalStatement := by
  exact quotLocal_of_quotientLength Formalism.LatticeBaseChangeAlt.quotientLength

end Formalism.L2.Pj.QAt

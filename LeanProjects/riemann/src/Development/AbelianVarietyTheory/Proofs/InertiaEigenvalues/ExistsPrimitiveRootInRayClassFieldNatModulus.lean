import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityMemRayClassFieldOfMultiple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsNormModEqOneOfPrincipalRayClass
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisSubfieldConjStable
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsBaseTwoWords

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT

namespace GlobalTheory.RayRootOfUnity

theorem norm_pos_of_pos_real {K : Type} [Field K] [NumberField K] {x : K} (hx : x ≠ 0)
    (h : ∀ τ : K →+* ℝ, 0 < τ x) : 0 < Algebra.norm ℚ x := by
  classical
  let c : (K →ₐ[ℚ] ℂ) → (K →ₐ[ℚ] ℂ) := fun φ =>
    { (starRingEnd ℂ).comp φ.toRingHom with
      commutes' := fun a => by
        change starRingEnd ℂ (φ (algebraMap ℚ K a)) = _
        rw [φ.commutes]; simp }
  have hc : ∀ φ e, c φ e = starRingEnd ℂ (φ e) := fun _ _ => rfl
  have hφ : ∀ φ : K →ₐ[ℚ] ℂ, φ x ≠ 0 := fun φ => (map_ne_zero _).2 hx
  have hn : ∀ φ : K →ₐ[ℚ] ℂ, (‖φ x‖ : ℂ) ≠ 0 := fun φ => by
    exact_mod_cast (norm_ne_zero_iff.2 (hφ φ))
  have h1 : ∏ φ : K →ₐ[ℚ] ℂ, (φ x / (‖φ x‖ : ℂ)) = 1 := by
    refine Finset.prod_involution (fun φ _ => c φ) (fun φ _ => ?_) (fun φ _ hne he => ?_)
      (fun _ _ => Finset.mem_univ _) (fun φ _ => ?_)
    · rw [hc, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have := hn φ
      push_cast
      field_simp
    · apply hne
      have hr : ∀ e, ((φ e).re : ℂ) = φ e := fun e =>
        Complex.conj_eq_iff_re.1 (by rw [← hc, he])
      let τ : K →+* ℝ :=
        { toFun := fun e => (φ e).re, map_one' := by simp, map_zero' := by simp,
          map_add' := by simp, map_mul' := fun a b => by
            apply Complex.ofReal_injective
            rw [Complex.ofReal_mul, hr, hr, hr, map_mul] }
      have hτ : 0 < (φ x).re := h τ
      rw [← hr x, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
      exact div_self (by exact_mod_cast hτ.ne')
    · ext e; simp [hc]
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun φ _ => hn φ),
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ x] at h1
  have h2 : ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ φ : K →ₐ[ℚ] ℂ, ‖φ x‖ := by
    apply Complex.ofReal_injective
    push_cast
    rw [← h1]
    rfl
  have : (0 : ℝ) < ((Algebra.norm ℚ x : ℚ) : ℝ) := by
    rw [h2]; exact Finset.prod_pos fun φ _ => norm_pos_iff.2 (hφ φ)
  exact_mod_cast this

theorem absNorm_modEq_one {K : Type} [Field K] [NumberField K] {𝔮 : Ideal (𝓞 K)} {p : ℕ}
    (hq : 𝔮 ≤ Ideal.span {(p : 𝓞 K)}) {I : Ideal (𝓞 K)} {α β : 𝓞 K} (hαβ : RayPair 𝔮 α β)
    (hI : I * Ideal.span {β} = Ideal.span {α}) : Ideal.absNorm I ≡ 1 [MOD p] := by
  obtain ⟨hα, hβ, _, hcβ, hd, hpos⟩ := hαβ
  have hpos' : 0 < Algebra.norm ℤ α * Algebra.norm ℤ β := by
    have hx : ((α * β : 𝓞 K) : K) ≠ 0 := by simpa using mul_ne_zero hα hβ
    have := norm_pos_of_pos_real hx fun τ => by
      have := hpos τ
      simpa [map_mul] using this
    rw [← Algebra.coe_norm_int, map_mul] at this
    exact_mod_cast this
  have h1 := congrArg Ideal.absNorm hI
  rw [map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at h1
  have h2 : (Ideal.absNorm I : ℤ) * Algebra.norm ℤ β * Algebra.norm ℤ β = Algebra.norm ℤ α * Algebra.norm ℤ β := by
    have e := congrArg (Nat.cast : ℕ → ℤ) h1
    rw [Nat.cast_mul, Int.natCast_natAbs, Int.natCast_natAbs] at e
    have e2 : (Ideal.absNorm I : ℤ) * |Algebra.norm ℤ β| * |Algebra.norm ℤ β| =
        |Algebra.norm ℤ α| * |Algebra.norm ℤ β| := by rw [e]
    rw [mul_assoc, abs_mul_abs_self, ← abs_mul, abs_of_pos hpos'] at e2
    rw [mul_assoc]; exact e2
  have h3 := GlobalTheory.Mem.RayNorm.norm_cast_eq K p (hq hd)
  obtain ⟨u, hu, v, hv, huv⟩ := Ideal.isCoprime_iff_exists.1 hcβ
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have h4 := GlobalTheory.Mem.RayNorm.norm_cast_eq K p (x := b * β) (y := 1) (by
    have : b * β - 1 = -v := by linear_combination huv
    rw [this]; exact neg_mem (hq hv))
  rw [map_mul, map_one] at h4
  have h5 := congrArg (Int.cast : ℤ → ZMod p) h2
  push_cast at h4 h5
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  linear_combination ((Algebra.norm ℤ b : ℤ) : ZMod p) ^ 2 * h5 +
    ((Algebra.norm ℤ b : ℤ) : ZMod p) ^ 2 * ((Algebra.norm ℤ β : ℤ) : ZMod p) * h3 +
    (((Algebra.norm ℤ b : ℤ) : ZMod p) * ((Algebra.norm ℤ β : ℤ) : ZMod p) + 1) * (1 - (Ideal.absNorm I : ZMod p)) * h4

end GlobalTheory.RayRootOfUnity

namespace GlobalTheory.RayRootOfUnity

theorem exists_isPrimitiveRoot_of_isRay : ∀ {K H : Type} [Field K] [NumberField K] [Field H] [NumberField H]
    [Algebra K H] [IsAbelianGalois K H] {n : ℕ}, n ≠ 0 → GlobalTheory.FieldSize.IsRay H (Ideal.span {(n : 𝓞 K)}) →
    ∃ ζ : H, IsPrimitiveRoot ζ n := by
  intro K H _ _ _ _ _ _ n hn hR
  classical
  have hRF : GlobalTheory.Mem.Fld.IsRayField K H (Ideal.span {(n : 𝓞 K)}) := ⟨inferInstance, hR⟩
  have h𝔮 : Ideal.span {(n : 𝓞 K)} ≠ ⊥ := by simpa using hn
  let ψ : H →+* ℂ := (IsAlgClosed.lift : H →ₐ[ℚ] ℂ).toRingHom
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n hn
  obtain ⟨S, hSa, hS⟩ := GlobalTheory.Mem.BaseField.exists_gens H
  obtain ⟨L, hfd, hgal, hSL, -, -⟩ := GlobalTheory.exists_galois_subfield_conj_stable (insert z S) (by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    exacts [GlobalTheory.Mem.BaseField.isAlgebraic_exp n, hSa w hw])
  have hψL : ∀ x, ψ x ∈ L := hS L (fun w hw => hSL w (Finset.mem_insert_of_mem hw)) ψ
  have hzL : z ∈ L := hSL z (Finset.mem_insert_self _ _)
  have : NumberField L := {}
  letI : Algebra H L := (ψ.codRestrict L hψL).toAlgebra
  letI : Algebra K L := ((ψ.codRestrict L hψL).comp (algebraMap K H)).toAlgebra
  have : IsScalarTower K H L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  obtain ⟨x, hx⟩ := GlobalTheory.Mem.RayZeta.root_mem_rayField K H L _ n hn le_rfl hRF
    (GlobalTheory.RayMaximal.closure_isFrob_eq_top L h𝔮)
    (fun I α β hαβ hI => absNorm_modEq_one le_rfl hαβ hI) ⟨z, hzL⟩
    (Subtype.ext (by simpa using hz.pow_eq_one))
  have e : ψ x = z := congrArg Subtype.val hx
  exact ⟨x, IsPrimitiveRoot.of_map_of_injective (f := ψ) (by rw [e]; exact hz) ψ.injective⟩

end GlobalTheory.RayRootOfUnity

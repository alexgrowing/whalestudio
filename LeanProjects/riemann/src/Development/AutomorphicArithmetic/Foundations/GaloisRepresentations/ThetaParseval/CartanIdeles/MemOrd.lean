import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf
open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

private theorem le_one_of_count {E : Type} [Field E] [NumberField E] (J : FractionalIdeal (𝓞 E)⁰ E) (hJ : J ≠ 0)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), 0 ≤ FractionalIdeal.count E w J) : J ≤ 1 := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' E hJ]
  refine finprod_induction (p := fun X : FractionalIdeal (𝓞 E)⁰ E => X ≤ 1) le_rfl ?_ ?_
  · intro a b ha hb
    calc a * b ≤ 1 * b := mul_le_mul_left ha b
      _ ≤ 1 * 1 := mul_le_mul_right hb 1
      _ = 1 := one_mul 1
  · intro v
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h v)
    rw [hn, zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.coeIdeal_le_one

private theorem mem_iff {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0)
    (y : E) (hy : y ≠ 0) : y ∈ I ↔ ∀ w, FractionalIdeal.count E w I ≤ ordE w y := by
  have hs : FractionalIdeal.spanSingleton (𝓞 E)⁰ y ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy
  constructor
  · intro h w
    exact FractionalIdeal.count_mono E w hs ((FractionalIdeal.spanSingleton_le_iff_mem).mpr h)
  · intro h
    have hJ : FractionalIdeal.spanSingleton (𝓞 E)⁰ y * I⁻¹ ≠ 0 := mul_ne_zero hs (inv_ne_zero hI)
    have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ y * I⁻¹ ≤ 1 := by
      refine le_one_of_count _ hJ fun w => ?_
      rw [FractionalIdeal.count_mul E w hs (inv_ne_zero hI), FractionalIdeal.count_inv]
      have := h w
      unfold ordE at this
      omega
    have h2 : FractionalIdeal.spanSingleton (𝓞 E)⁰ y ≤ I := by
      calc FractionalIdeal.spanSingleton (𝓞 E)⁰ y
          = (FractionalIdeal.spanSingleton (𝓞 E)⁰ y * I⁻¹) * I := by
            rw [mul_assoc, inv_mul_cancel₀ hI, mul_one]
        _ ≤ 1 * I := mul_le_mul_left hle I
        _ = I := one_mul I
    exact (FractionalIdeal.spanSingleton_le_iff_mem).mp h2

private theorem attained {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0)
    (w : HeightOneSpectrum (𝓞 E)) : ∃ x ∈ I, x ≠ 0 ∧ ordE w x = FractionalIdeal.count E w I := by
  by_contra hcon
  push_neg at hcon
  have hP : ((w.asIdeal : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact w.ne_bot
  have hPI := mul_ne_zero hP hI
  have hle : I ≤ ((w.asIdeal : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) * I := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact FractionalIdeal.mem_coe.mp (Submodule.zero_mem _)
    refine (mem_iff _ hPI x hx0).mpr fun v => ?_
    rw [FractionalIdeal.count_mul E v hP hI]
    have h1 := (mem_iff I hI x hx0).mp hx v
    by_cases hv : v = w
    · subst hv
      rw [FractionalIdeal.count_self]
      have := hcon x hx hx0
      omega
    · rw [FractionalIdeal.count_maximal_coprime E v (Ne.symm hv)]
      omega
  have h3 := FractionalIdeal.count_mono E w hI hle
  rw [FractionalIdeal.count_mul E w hP hI, FractionalIdeal.count_self] at h3
  omega

private theorem lattice {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0) :
    (I : Submodule (𝓞 E) E).IsLattice E := by
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ I, x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hI
    ext y
    rw [FractionalIdeal.mem_zero_iff]
    exact ⟨hcon y, fun h => h ▸ FractionalIdeal.mem_coe.mp (Submodule.zero_mem _)⟩
  refine ⟨FractionalIdeal.fg_of_isUnit I (IsUnit.mk0 I hI), ?_⟩
  rw [eq_top_iff]
  intro y _
  have : y = (y / x) • x := by rw [smul_eq_mul, div_mul_cancel₀ y hx0]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

theorem UpperTheory.Gal.TP.Skew.memOrd :
    UpperTheory.Gal.TP.Skew.MemOrd := by
  intro E _ _ I hI
  exact ⟨mem_iff I hI, attained I hI, lattice I hI⟩

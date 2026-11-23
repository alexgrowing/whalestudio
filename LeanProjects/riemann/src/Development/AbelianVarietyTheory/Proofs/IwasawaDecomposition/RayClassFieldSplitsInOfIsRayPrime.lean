import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotDvdDiscrIffRamificationIdx
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ParRay

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem not_isUnit_natCast {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) : ¬ IsUnit (p : 𝓞 K) := by
  intro h
  have : IsLocalHom (algebraMap ℤ (𝓞 K)) := Algebra.IsIntegral.isLocalHom _ _
  rw [← map_natCast (algebraMap ℤ (𝓞 K))] at h
  exact (Nat.prime_iff_prime_int.1 hp).not_unit (isUnit_of_map_unit _ _ h)

theorem rayField_splitsIn_of_isRayPrime (D : D7) (jE : D.host.E →+* Qb) (M : Fld) (h : KQbar D jE ≤ M)
    (hf : FiniteDimensional ℚ M) :
    letI := GlobalTheory.ParRay.algK D jE h
    haveI := GlobalTheory.ParRay.nfOf hf
    GlobalTheory.Mem.Fld.IsRayField D.host.K M (GlobalTheory.Mem.RaySplit.condIdeal D.host) →
      ∀ p, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) p → SplitsIn M p := by
  letI := GlobalTheory.ParRay.algK D jE h
  haveI := GlobalTheory.ParRay.nfOf hf
  intro hM p hp
  obtain ⟨hpp, π, hπK, hπi, hπc, σ, hσ⟩ := hp
  have hc0 : ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) ≠ 0 := by
    exact_mod_cast GlobalTheory.Mem.RaySplit.cond_ne_zero D.host
  let φ : D.host.K →+* Qb := jE.comp (D.host.K.val : D.host.K →+* D.host.E)
  have hφ : Function.Injective φ := jE.injective.comp Subtype.val_injective
  have hint : ∀ z : D.host.K, IsIntegral ℤ (φ z) → IsIntegral ℤ z := fun z hz =>
    (isIntegral_algHom_iff φ.toIntAlgHom hφ).1 hz
  have hmem : ∀ w : Qb, w ∈ KQbar D jE → ∃ z : D.host.K, φ z = w := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := (IntermediateField.mem_map _).1 hw
    exact ⟨⟨z, hz⟩, rfl⟩
  have hp0 : (p : Qb) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hπ0 : π ≠ 0 := left_ne_zero_of_mul (hσ ▸ hp0)
  have hσπ : σ π = p / π := by rw [← hσ, mul_div_cancel_left₀ _ hπ0]
  have hσK : σ π ∈ KQbar D jE := hσπ ▸ div_mem (natCast_mem _ p) hπK
  obtain ⟨x, hx⟩ := hmem π hπK
  obtain ⟨y, hy⟩ := hmem (σ π) hσK
  let σZ : Qb →ₐ[ℤ] Qb := σ.toRingHom.toIntAlgHom
  let a : 𝓞 D.host.K := ⟨x, hint x (hx ▸ hπi)⟩
  let b : 𝓞 D.host.K := ⟨y, hint y (hy ▸ hπi.map σZ)⟩

  have hab : a * b = p := by
    apply RingOfIntegers.coe_injective
    apply hφ
    rw [map_mul, map_natCast, map_mul, map_natCast]
    show φ x * φ y = _
    rw [hx, hy, hσ]

  have hdvd : ∀ z : 𝓞 D.host.K,
      IsIntegral ℤ ((φ z - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb)) →
      ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.K) ∣ z - 1 := by
    intro z hz
    set c : ℕ := D.host.QS * D.host.q * D.host.d
    have hcK : (c : D.host.K) ≠ 0 := by exact_mod_cast GlobalTheory.Mem.RaySplit.cond_ne_zero D.host
    have hφw : φ (((z : D.host.K) - 1) / c) = (φ z - 1) / c := by
      rw [map_div₀, map_sub, map_one, map_natCast]
    let w : 𝓞 D.host.K := ⟨((z : D.host.K) - 1) / c, hint _ (hφw ▸ hz)⟩
    refine ⟨w, RingOfIntegers.coe_injective ?_⟩
    show (z : D.host.K) - 1 = (c : D.host.K) * (((z : D.host.K) - 1) / c)
    rw [mul_div_cancel₀ _ hcK]
  have hca := hdvd a (by show IsIntegral ℤ ((φ x - 1) / _); rw [hx]; exact hπc)
  have hcb := hdvd b (by
    show IsIntegral ℤ ((φ y - 1) / _)
    have e : σZ ((π - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb)) =
        (σ π - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) := by
      show σ _ = _
      rw [map_div₀, map_sub, map_one, map_natCast]
    rw [hy, ← e]
    exact hπc.map σZ)

  have hpu : ¬ IsUnit (p : 𝓞 D.host.K) := not_isUnit_natCast hpp
  have hunit : ∀ (z : 𝓞 D.host.K), (z : D.host.K) ≠ 0 → IsIntegral ℤ (φ z)⁻¹ → IsUnit z := by
    intro z hz0 hz
    have hi : IsIntegral ℤ ((z : D.host.K)⁻¹) := hint _ (by rw [map_inv₀]; exact hz)
    refine IsUnit.of_mul_eq_one (⟨_, hi⟩ : 𝓞 D.host.K) (RingOfIntegers.coe_injective ?_)
    show (z : D.host.K) * (z : D.host.K)⁻¹ = 1
    exact mul_inv_cancel₀ hz0
  have hinv : ∀ (z : 𝓞 D.host.K), IsUnit z → IsIntegral ℤ (φ z)⁻¹ := by
    intro z hz
    obtain ⟨u, rfl⟩ := hz
    have h1 : (algebraMap (𝓞 D.host.K) D.host.K) ((u⁻¹ : (𝓞 D.host.K)ˣ) : 𝓞 D.host.K) =
        ((algebraMap (𝓞 D.host.K) D.host.K) (u : 𝓞 D.host.K))⁻¹ :=
      map_units_inv (algebraMap (𝓞 D.host.K) D.host.K) u
    have h2 : φ ((algebraMap (𝓞 D.host.K) D.host.K) ((u⁻¹ : (𝓞 D.host.K)ˣ) : 𝓞 D.host.K)) =
        (φ ((u : 𝓞 D.host.K) : D.host.K))⁻¹ := by
      rw [h1, map_inv₀]
    rw [← h2]
    exact (RingOfIntegers.isIntegral_coe _).map φ.toIntAlgHom
  have hx0 : (x : D.host.K) ≠ 0 := fun h0 => hπ0 (by rw [← hx, h0, map_zero])
  have hy0 : (y : D.host.K) ≠ 0 := fun h0 => hp0 (by rw [← hσ, ← hy, h0, map_zero, mul_zero])
  have hu : ¬ IsUnit a := fun ha => hpu (by
    have h1 := (hinv a ha).map σZ
    have h2 : σZ (φ x)⁻¹ = (φ y)⁻¹ := by
      show σ (φ x)⁻¹ = _
      rw [map_inv₀, hx, hy]
    rw [← hab]
    exact ha.mul (hunit b hy0 (h2 ▸ h1)))
  have hu' : ¬ IsUnit b := fun hb => hpu (by
    haveI : Algebra.IsAlgebraic ℚ Qb := by
      unfold Qb; convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
    let τ : Qb ≃ₐ[ℚ] Qb := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
    let τZ : Qb →ₐ[ℤ] Qb := τ.symm.toRingEquiv.toRingHom.toIntAlgHom
    have h1 := (hinv b hb).map τZ
    have h2 : τZ (φ y)⁻¹ = (φ x)⁻¹ := by
      show τ.symm (φ y)⁻¹ = _
      rw [map_inv₀, hy, hx]
      congr 1
      exact τ.symm_apply_apply π
    rw [← hab]
    exact (hunit a hx0 (h2 ▸ h1)).mul hb)

  have hpc : ¬ p ∣ D.host.QS * D.host.q * D.host.d := fun hd => hpu (by
    have h1 : (p : 𝓞 D.host.K) ∣ a - 1 := (Nat.cast_dvd_cast hd).trans hca
    have h2 : (p : 𝓞 D.host.K) ∣ b - 1 := (Nat.cast_dvd_cast hd).trans hcb
    have h3 : (1 : 𝓞 D.host.K) = p - (a * (b - 1) + (a - 1)) := by rw [← hab]; ring
    exact isUnit_of_dvd_one (h3 ▸ dvd_sub dvd_rfl (dvd_add (h2.mul_left _) h1)))
  have hd : ¬ (p : ℤ) ∣ discr M := fun hd => hpc (GlobalTheory.Mem.RaySplit.unr_of_ray hM p hpp hd)
  exact (GlobalTheory.HostSplit.ncard_placesOver M hpp).trans
    (GlobalTheory.Mem.RaySplit.ncard_primesOver_eq hM (GlobalTheory.Mem.RaySplit.isEmpty_real D.host)
      (GlobalTheory.Mem.RaySplit.finrank_K D.host) hpp hd hab hu hu' hca hcb)

end GlobalTheory.ParRay

end

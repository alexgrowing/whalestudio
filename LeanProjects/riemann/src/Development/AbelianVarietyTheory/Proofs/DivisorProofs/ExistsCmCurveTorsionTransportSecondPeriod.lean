import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LatVal.CurveTransport

open GlobalTheory.EllipticCM GlobalTheory.ConjPoint WeierstrassCurve
open GlobalTheory.Idele
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsLatOf IsInvIdealOf)

variable {K : Type} [Field K] [NumberField K]

theorem isLatOf_iff {ι : K →+* ℂ} {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {Λ : PeriodPair} :
    IsLatOf ι 𝔞 Λ ↔ ∀ z, z ∈ Λ.lattice ↔ ∃ x ∈ 𝔞, ι x = z := by
  rw [IsLatOf, Set.ext_iff]
  rfl

theorem isInvIdealOf_inv_smul_one (t : (Af K)ˣ) :
    IsInvIdealOf t (t⁻¹ • (1 : FractionalIdeal (𝓞 K)⁰ K)) := by
  intro x
  rw [← algebraMap_mem_adelicIdeal (GlobalTheory.Idele.smul_ne_zero _ (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0)), ← mem_adelicIdeal_one_iff,
    ← mul_mem_adelicIdeal_smul t⁻¹ 1 ((t : Af K) * algebraMap K _ x), Units.inv_mul_cancel_left]

theorem mulEquiv_inv_mk (t : (Af K)ˣ) {x x' : K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) v) ≤ 1) :
    mulEquiv t⁻¹ (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) rfl
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk x' := by
  rw [mulEquiv_mk_eq_mk_iff_adelic]
  have e : ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x - algebraMap K (Af K) x' =
      ((t⁻¹ : (Af K)ˣ) : Af K) * -((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) := by
    rw [mul_neg, mul_sub, Units.inv_mul_cancel_left]
    ring
  rw [e, mul_mem_adelicIdeal_smul]
  exact neg_mem (mem_adelicIdeal_one_iff.2 h)

theorem exists_curve_torsTransport : ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K],
    Module.finrank ℚ K = 2 → ∀ (ι : K →+* ℂ) (Λ₀ : PeriodPair) (Ω₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ₀ →
    Ω₀ ≠ 0 → letI : Algebra K ℂ := ι.toAlgebra;
    ∃ (X : WeierstrassCurve ℂ) (_ : X.IsElliptic)
      (ξ : (ℂ ⧸ GlobalTheory.EllipticCM.idealSub (1 : FractionalIdeal (𝓞 K)⁰ K)) ≃+ X.toAffine.Point),
      GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (t : (Af K)ˣ),
        GlobalTheory.EllipticCM.Transports σ t one_ne_zero ξ →
        ∃ (Λ₁ : PeriodPair) (Ω₁ : ℂ), TorsTransport ι σ.toRingEquiv t Λ₀ Λ₁ Ω₀ Ω₁ := by
  intro K _ _ _ _ ι Λ₀ Ω₀ hΛ₀ hΩ₀
  letI : Algebra K ℂ := ι.toAlgebra
  have hAlg : ∀ y : K, algebraMap K ℂ y = ι y := fun _ => rfl
  have hsubIff : ∀ {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {Λ : PeriodPair},
      (IsLatOf ι 𝔞 Λ ↔ ∀ z, z ∈ idealSub 𝔞 ↔ z ∈ Λ.lattice) := fun {𝔞 Λ} => by
    rw [isLatOf_iff]
    exact forall_congr' fun z => by rw [mem_idealSub]; exact Iff.comm
  let M := GlobalTheory.scalePeriods Λ₀ Ω₀ hΩ₀
  have hM : GlobalTheory.IsHomothetic Ω₀ Λ₀ M := GlobalTheory.isHomothetic_scalePeriods Λ₀ Ω₀ hΩ₀
  have hsub : ∀ z, z ∈ idealSub (1 : FractionalIdeal (𝓞 K)⁰ K) ↔ Ω₀ * z ∈ M.lattice := fun z => by
    rw [hM z]; exact hsubIff.1 hΛ₀ z
  obtain ⟨ξ, hξ, hξz⟩ := exists_isAnalyticIso (X := latticeCurve M) (C := 1) (one_smul _ _) hΩ₀ hsub
  refine ⟨latticeCurve M, inferInstance, ξ, hξ, fun σ t ht => ?_⟩
  obtain ⟨η, ⟨hη, hηx⟩, -⟩ := ht
  obtain ⟨L', g2, g3⟩ := GlobalTheory.CMRam.exists_conj_lattice σ.toRingEquiv M
  have h' : (1 : VariableChange ℂ) • (latticeCurve M).map (σ : ℂ →+* ℂ) = latticeCurve L' := by
    rw [one_smul]
    simp [latticeCurve, WeierstrassCurve.map, g2, g3, map_ofNat]
  obtain ⟨α, hα0, hα, hηα⟩ := hη.exists_mul h'
  let Λ₁ := GlobalTheory.scalePeriods L' α⁻¹ (inv_ne_zero hα0)
  have hΛ₁ : GlobalTheory.IsHomothetic α⁻¹ L' Λ₁ := GlobalTheory.isHomothetic_scalePeriods L' α⁻¹ (inv_ne_zero hα0)
  have hΛ₁' : GlobalTheory.IsHomothetic α Λ₁ L' := fun z => by
    rw [← hΛ₁ (α * z), ← mul_assoc, inv_mul_cancel₀ hα0, one_mul]
  have hlat1 : IsLatOf ι (t⁻¹ • 1) Λ₁ := hsubIff.2 fun z => by rw [hα, hΛ₁' z]
  refine ⟨Λ₁, α, hΩ₀, hα0, fun x => σ.commutes x, hΛ₀, ⟨_, isInvIdealOf_inv_smul_one t, hlat1⟩, ?_, ?_, ?_⟩
  · rw [div_eq_inv_mul, ← hM.g₂_eq, ← g2, hΛ₁'.g₂_eq, div_eq_inv_mul]
  · rw [div_eq_inv_mul, ← hM.g₃_eq, ← g3, hΛ₁'.g₃_eq, div_eq_inv_mul]
  · intro x x' hx hint
    have e := hηx (Submodule.Quotient.mk x)
    rw [mulEquiv_inv_mk t hint, torsionIncl_mk, torsionIncl_mk, hξz, hηα, hAlg, hAlg] at e
    have hxM : Ω₀ * ι x ∉ M.lattice := fun h => hx ((hM _).1 h)
    rw [latticePoint_of_notMem M hxM] at e
    have hx' : α * ι x' ∉ L'.lattice := by
      intro h
      rw [latticePoint_of_mem L' h, map_zero, variableChangePoint_some] at e
      exact Affine.Point.some_ne_zero _ e
    rw [latticePoint_of_notMem L' hx', variableChangePoint_some, variableChangePoint_some] at e
    change Affine.Point.some _ _ _ = _ at e
    rw [Affine.Point.some.injEq] at e
    simp [VariableChange.one_def] at e
    obtain ⟨e1, e2⟩ := e
    refine ⟨?_, ?_⟩
    · rw [div_eq_inv_mul, ← hM.weierstrassP_mul, div_eq_inv_mul, ← hΛ₁'.weierstrassP_mul]
      exact e1
    · rw [div_eq_inv_mul, ← hM.derivWeierstrassP_mul, div_eq_inv_mul, ← hΛ₁'.derivWeierstrassP_mul]
      rw [map_ofNat σ 2, div_left_inj' two_ne_zero] at e2
      exact e2

end GlobalTheory.LatVal.CurveTransport

import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMulVBFilCris

noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

open Formalism.BasicNotions

section Dec

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

private lemma mem_DcrisL_iff' (T : LocLat G Qp LL O) (σ : K₀ →ₐ[Qp] LL) (x : T.V ⊗[Qp] B) :
    x ∈ DcrisL PD T.ρ σ ↔ x ∈ Dcris PD T.ρ ∧
      ∀ c : K₀, mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) c x = σ c • x := by
  simp only [DcrisL, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

private lemma mem_DdRE_iff' (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (y : T.V ⊗[Qp] BdR) :
    y ∈ DdRE PD T.ρ τ ↔ y ∈ DdR PD T.ρ ∧
      ∀ c : K, mulVdR (K := K) (BdR := BdR) (V := T.V) (LL := LL) c y = τ c • y := by
  simp only [DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

private lemma iotaV_injective (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ x, ιV PD (LL := LL) (V := T.V) x =
      LinearMap.lTensor T.V (PD.ι.toLinearMap.restrictScalars Qp) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => first | rfl | simp [ιV]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  intro x y hxy
  rw [h, h] at hxy
  exact Module.Flat.lTensor_preserves_injective_linearMap _ (by exact PD.ι_inj) hxy

private lemma iotaV_mulVB_comm (T : LocLat G Qp LL O) (c : K₀) (x : T.V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := T.V) (mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) c x) =
      mulVdR (K := K) (BdR := BdR) (V := T.V) (LL := LL) (algebraMap K₀ K c)
        (ιV PD (LL := LL) (V := T.V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [ιV, mulVB, mulVdR, ← IsScalarTower.algebraMap_apply]
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]

theorem rk_lift (hK : Function.Bijective (algebraMap K₀ K)) (σ : K₀ →ₐ[Qp] LL) :
    ∃ τ : K →ₐ[Qp] LL, τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = σ := by
  let e : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hK
  refine ⟨σ.comp (e.symm : K →ₐ[Qp] K₀), ?_⟩
  ext x
  have hx : (IsScalarTower.toAlgHom Qp K₀ K) x = e x := rfl
  simp only [AlgHom.comp_apply, hx, AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply]

variable [NeZero n] (W : LocWach PD LL O v n)

include W in
theorem rk_DcrisL_map (hK : Function.Bijective (algebraMap K₀ K)) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (τ : K →ₐ[Qp] LL) :
    (DcrisL PD T.ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))).map (ιV PD (LL := LL) (V := T.V)) =
      DdRE PD T.ρ τ := by
  have hD := (hQ hK T.V T.ρ hT).1
  ext y
  rw [Submodule.mem_map, mem_DdRE_iff']
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_DcrisL_iff'] at hx
    refine ⟨?_, fun c => ?_⟩
    · rw [← hD]; exact Submodule.mem_map_of_mem hx.1
    · obtain ⟨c₀, rfl⟩ := hK.2 c
      rw [← iotaV_mulVB_comm, hx.2 c₀, map_smul]
      first | rfl | simp
  · rintro ⟨hyD, hyc⟩
    rw [← hD, Submodule.mem_map] at hyD
    obtain ⟨x, hxD, rfl⟩ := hyD
    refine ⟨x, (mem_DcrisL_iff' T _ x).mpr ⟨hxD, fun c₀ => ?_⟩, rfl⟩
    apply iotaV_injective (PD := PD) T
    rw [iotaV_mulVB_comm, hyc, map_smul]
    first | rfl | simp

include W in
theorem rk_finrank_DcrisL (hK : Function.Bijective (algebraMap K₀ K)) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (σ : K₀ →ₐ[Qp] LL) :
    finrank LL ↥(DcrisL PD T.ρ σ) = finrank LL T.V := by
  obtain ⟨τ, hτ⟩ := rk_lift hK σ
  rw [← hτ]
  have hmap := rk_DcrisL_map W hK hQ T hT τ
  have hE := (hQ hK T.V T.ρ hT).2 τ
  rw [← hE.2.1, ← hmap]
  exact (Submodule.equivMapOfInjective _ (iotaV_injective (PD := PD) T) _).finrank_eq

end Dec

end Formalism.MainNotions.N.Pv.LocalLengthBound

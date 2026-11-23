import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisStrictHodgeFiltrationUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OfShortExact

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.Per.DcrisExact

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]

theorem mapVB_eq_rTensor (f : V →ₗ[LL] W) (x : V ⊗[Qp] B) :
    Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x = (f.restrictScalars Qp).rTensor B x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [Formalism.MainNotions.RamifiedCoefficientChains.mapVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_Dcris' (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem mapVB_act (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (g : G) (x : V ⊗[Qp] B) :
    Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f (actVB PD ρ g x) =
      actVB PD σ g (Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, Formalism.MainNotions.RamifiedCoefficientChains.mapVB, hf]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mapVB_mem_Dcris (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x ∈ Dcris PD σ := by
  rw [mem_Dcris'] at hx ⊢
  intro g
  rw [← mapVB_act PD ρ σ f hf, hx]

theorem ιV_mapVB (f : V →ₗ[LL] W) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := W) (Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x) =
      AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [ιV, Formalism.MainNotions.RamifiedCoefficientChains.mapVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_mem_FilV (f : V →ₗ[LL] W) (a : ℤ) {y : V ⊗[Qp] BdR}
    (hy : y ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y ∈ FilV PD (LL := LL) (V := W) a := by
  obtain ⟨z, rfl⟩ := hy
  refine ⟨AlgebraTensorModule.map f (LinearMap.id : ↥((PD.Fil a).restrictScalars Qp) →ₗ[Qp] ↥((PD.Fil a).restrictScalars Qp)) z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mapVB_mem_FilCris (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (a : ℤ) {x : V ⊗[Qp] B} (hx : x ∈ FilCris PD ρ a) :
    Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x ∈ FilCris PD σ a := by
  refine ⟨mapVB_mem_Dcris PD ρ σ f hf hx.1, ?_⟩
  show ιV PD (LL := LL) (V := W) (Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x) ∈ FilV PD (LL := LL) (V := W) a
  rw [ιV_mapVB]
  exact map_mem_FilV PD f a hx.2

end Abstract

end GlobalTheory.Per.DcrisExact

namespace GlobalTheory.Per.DcrisExact

open GlobalTheory.Per.DcrisExact

theorem exactStrict (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K LL : FinExt l) : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict (P.PD K) ↥LL.1 := by
  intro hb V₀ _ _ _ _ _ ρ₀ V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ ι π hι hπ hinj hsurj hex hc₀ hc₁ hc₂
  have hE : Function.Exact (ι.restrictScalars ℚ_[l]) (π.restrictScalars ℚ_[l]) := by
    rw [LinearMap.exact_iff]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range, LinearMap.restrictScalars_apply]
    have := congrArg (fun S : Submodule ↥LL.1 V₁ => x ∈ S) hex
    simpa using this
  have hexT := rTensor_exact P.R.B (f := ι.restrictScalars ℚ_[l]) (g := π.restrictScalars ℚ_[l]) hE hsurj
  have hinjT : Function.Injective ((ι.restrictScalars ℚ_[l]).rTensor P.R.B) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hinj
  have hS := GlobalTheory.T.dcris_strict_hodgeFiltration_unramified l P AI hT K LL hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _ hx
    apply hinjT
    rw [← mapVB_eq_rTensor, hx, map_zero]
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨mapVB_mem_Dcris _ ρ₀ ρ₁ ι hι hx, ?_⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, mapVB_eq_rTensor, mapVB_eq_rTensor,
        ← LinearMap.rTensor_comp_apply]
      have : (π.restrictScalars ℚ_[l]).comp (ι.restrictScalars ℚ_[l]) = 0 := by
        ext v
        exact hE.apply_apply_eq_zero v
      rw [this, LinearMap.rTensor_zero, LinearMap.zero_apply]
    · rintro y ⟨hy, hk⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, mapVB_eq_rTensor] at hk
      obtain ⟨x, hx⟩ := (hexT y).mp hk
      rw [← mapVB_eq_rTensor] at hx
      refine ⟨x, ?_, hx⟩
      have hy' := (mem_Dcris' _ ρ₁ y).1 hy
      rw [SetLike.mem_coe, mem_Dcris']
      intro g
      apply hinjT
      rw [← mapVB_eq_rTensor, ← mapVB_eq_rTensor, mapVB_act _ ρ₀ ρ₁ ι hι, hx, hy' g]
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact mapVB_mem_Dcris _ ρ₁ ρ₂ π hπ hx
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI hT K LL V₁ ρ₁ V₂ ρ₂ π hπ).2
        hsurj hc₁).2 y hy
      exact ⟨x, hx, hxy⟩
  · intro a
    refine ⟨(hS V₁ ρ₁ V₂ ρ₂ π hπ).1 hsurj hc₁ a, ?_⟩
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, mapVB_mem_FilCris _ ρ₀ ρ₁ ι hι a hx⟩
    · rintro x ⟨hx, hf⟩
      exact (hS V₀ ρ₀ V₁ ρ₁ ι hι).2 hinj a x hx hf

end GlobalTheory.Per.DcrisExact

namespace GlobalTheory.Per.DcrisExact

theorem fontaine_dcris : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm11 D := by
  intro D l _ K LL
  refine ⟨exactStrict l (D.loc l) (D.locA l) (D.locT l) K LL, ?_, ?_⟩
  · intro V₀ _ _ _ _ _ ρ₀ V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ ι π hι hπ hinj hsurj _ hc₁
    exact ⟨(GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) (D.locT l) K LL V₀ ρ₀ V₁ ρ₁ ι hι).1
        hinj hc₁,
      ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) (D.locT l) K LL V₁ ρ₁ V₂ ρ₂ π hπ).2
        hsurj hc₁).1⟩
  · intro hb V _ _ _ _ _ ρ hc
    exact GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc

end GlobalTheory.Per.DcrisExact

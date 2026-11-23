import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OfShortExact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamSubrepQuotientAndStrictness

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.Per.CrisStrict

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem ιV_map (f : V →ₗ[LL] V') (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V') (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) =
      AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v b => simp [ιV]

theorem map_mem_Dcris (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x ∈ Dcris PD ρ' := by
  have key : ∀ (g : G) (z : V ⊗[Qp] B), actVB PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) z) =
      AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (actVB PD ρ g z) := by
    intro g z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul v b => simp [actVB, hf]
  rw [GlobalTheory.Per.CrisDR.mem_Dcris_iff] at hx ⊢
  intro g
  rw [key, hx g]

theorem map_mem_FilV (f : V →ₗ[LL] V') {a : ℤ} {x : V ⊗[Qp] BdR} (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈ FilV PD (LL := LL) (V := V') a := by
  obtain ⟨z, rfl⟩ := hx
  refine ⟨AlgebraTensorModule.map f (LinearMap.id) z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v b => simp

theorem map_map_id {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
    (f : V →ₗ[LL] V') (g : V' →ₗ[LL] V'') (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.map g (LinearMap.id : BdR →ₗ[Qp] BdR)
      (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x) =
      AlgebraTensorModule.map (g ∘ₗ f) (LinearMap.id : BdR →ₗ[Qp] BdR) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v b => simp

theorem mem_FilV_of_injective (f : V →ₗ[LL] V') (hi : Function.Injective f) {a : ℤ} {x : V ⊗[Qp] BdR}
    (hx : AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈ FilV PD (LL := LL) (V := V') a) :
    x ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.2 hi)
  have := map_mem_FilV PD g hx
  rwa [map_map_id, hg, AlgebraTensorModule.map_id, LinearMap.id_apply] at this

end Abstract

theorem dcris_strict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), Function.Bijective (algebraMap ↥(K0 K) ↥K.1) → ∀ (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (π : V₁ →ₗ[↥LL.1] V₂), (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) → (Function.Surjective π → IsCrys (P.PD K) ρ₁ → ∀ a : ℤ, (FilCris (P.PD K) ρ₁ a).map (AlgebraTensorModule.map π (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B)) = FilCris (P.PD K) ρ₂ a) ∧ (Function.Injective π → ∀ a : ℤ, ∀ y ∈ Dcris (P.PD K) ρ₁, AlgebraTensorModule.map π (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) y ∈ FilCris (P.PD K) ρ₂ a → y ∈ FilCris (P.PD K) ρ₁ a) := by
  intro l _ P AI T K LL hb V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ π hπ
  refine ⟨fun hs hc a => le_antisymm ?_ ?_, fun hi a y hy hF => ?_⟩
  · rintro _ ⟨x, ⟨hxD, hxF⟩, rfl⟩
    refine ⟨map_mem_Dcris (P.PD K) ρ₁ ρ₂ π hπ hxD, Submodule.mem_comap.2 ?_⟩
    rw [ιV_map]
    exact map_mem_FilV (P.PD K) π (Submodule.mem_comap.1 hxF)
  · rintro y ⟨hyD, hyF⟩
    have hc2 := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI T K LL V₁ ρ₁ V₂ ρ₂ π hπ).2 hs hc).1
    have hyR : ιV (P.PD K) (LL := ↥LL.1) (V := V₂) y ∈ DdR (P.PD K) ρ₂ := by
      rw [← (GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l P AI T K LL hb V₂ ρ₂ hc2).1]
      exact Submodule.mem_map_of_mem hyD
    have hdr1 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K LL V₁ ρ₁ hc).1
    obtain ⟨x', ⟨hx'D, hx'F⟩, hx'⟩ :=
      ((GlobalTheory.DRSubQuot.deRham_sub_quot l P AI T K LL V₁ ρ₁ V₂ ρ₂ π hπ).2 hs hdr1).2 a _ ⟨hyR, hyF⟩
    rw [← (GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l P AI T K LL hb V₁ ρ₁ hc).1] at hx'D
    obtain ⟨x, hx, rfl⟩ := hx'D
    refine ⟨x, ⟨hx, hx'F⟩, ?_⟩
    apply GlobalTheory.Per.DdREqDcris.ιV_injective (P.PD K) (LL := ↥LL.1)
    rw [ιV_map, hx']
  · refine ⟨hy, ?_⟩
    have h2 := Submodule.mem_comap.1 hF.2
    rw [ιV_map] at h2
    exact Submodule.mem_comap.2 (mem_FilV_of_injective (P.PD K) π hi h2)

end GlobalTheory.Per.CrisStrict

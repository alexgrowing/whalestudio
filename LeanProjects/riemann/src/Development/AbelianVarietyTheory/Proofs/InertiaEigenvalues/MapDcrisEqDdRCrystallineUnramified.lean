import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrankStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.Per.DdREqDcris

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem ιV_mulVB (c : K₀) (d : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d) =
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K c)
        (ιV PD (LL := LL) (V := V) d) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v b => simp [mulVdR, ιV, mulVB, ← IsScalarTower.algebraMap_apply]

theorem act_mulVB (g : G) (c : K₀) (d : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (actVB PD ρ g d) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v b => simp [actVB, mulVB]

theorem mulVB_mem (c : K₀) {d : V ⊗[Qp] B} (hd : d ∈ Dcris PD ρ) :
    mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d ∈ Dcris PD ρ := by
  rw [CrisDR.mem_Dcris_iff] at hd ⊢
  intro g
  rw [act_mulVB, hd g]

theorem mulVdR_one (y : V ⊗[Qp] BdR) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) 1 y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v b => simp [mulVdR]

theorem ιV_injective : Function.Injective (ιV PD (LL := LL) (V := V)) := by
  rw [injective_iff_map_eq_zero]
  intro d hd
  refine CrisDR.eq_zero_of_sum PD (LL := LL) (m := 1) (fun _ => (1 : K)) ?_ (fun _ => d) ?_ 0
  · intro b hb i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    apply PD.ι_inj
    simpa using hb
  · simp [hd]

theorem map_Dcris_eq (hb : Function.Surjective (algebraMap K₀ K))
    (h : ∀ y ∈ DdR PD ρ, ∃ (m : ℕ) (c : Fin m → K) (d : Fin m → V ⊗[Qp] B), (∀ i, d i ∈ Dcris PD ρ) ∧
        y = ∑ i, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (c i) (ιV PD (LL := LL) (V := V) (d i))) :
    (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) = DdR PD ρ := by
  apply le_antisymm
  · rintro _ ⟨d, hd, rfl⟩
    have := CrisDR.mul_ι_mem PD ρ (1 : K) hd
    rwa [mulVdR_one] at this
  · intro y hy
    obtain ⟨m, c, d, hd, rfl⟩ := h y hy
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c₀, hc₀⟩ := hb (c i)
    rw [← hc₀, ← ιV_mulVB]
    exact Submodule.mem_map_of_mem (mulVB_mem PD ρ c₀ (hd i))

theorem FildR_eq (hb : Function.Surjective (algebraMap K₀ K))
    (h : (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) = DdR PD ρ) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ a = (FilCris PD ρ a ⊓ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))).map
      (ιV PD (LL := LL) (V := V)) := by
  apply le_antisymm
  · rintro y ⟨⟨hy, hτ⟩, hF⟩
    rw [← h] at hy
    obtain ⟨d, hd, rfl⟩ := hy
    refine Submodule.mem_map_of_mem ⟨⟨hd, hF⟩, hd, ?_⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hτ ⊢
    intro c
    apply ιV_injective PD (LL := LL)
    rw [ιV_mulVB, hτ, map_smul]
    rfl
  · rintro _ ⟨d, ⟨⟨hd, hF⟩, -, hτ⟩, rfl⟩
    refine ⟨⟨h ▸ Submodule.mem_map_of_mem hd, ?_⟩, hF⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hτ ⊢
    intro c
    obtain ⟨c₀, rfl⟩ := hb c
    rw [← ιV_mulVB, hτ, map_smul]
    rfl

end Abstract

theorem map_Dcris_eq_DdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), Function.Bijective (algebraMap ↥(K0 K) ↥K.1) → ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → (Dcris (P.PD K) ρ).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) = DdR (P.PD K) ρ ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = finrank ↥LL.1 V ∧ ∀ a : ℤ, FildR (P.PD K) ρ τ a = (FilCris (P.PD K) ρ a ⊓ DcrisL (P.PD K) ρ (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) := by
  intro l _ P AI T K LL hb V _ _ _ _ _ ρ hc
  obtain ⟨hdr, hspan⟩ := CrisDR.isDR_of_isCrys l P AI T K LL V ρ hc
  have h := map_Dcris_eq (P.PD K) ρ hb.2 hspan
  refine ⟨h, fun τ => ?_⟩
  obtain ⟨h1, -, h2⟩ := (GlobalTheory.T.deRhamComponents_crystallineLetters_finrank l P AI T K LL V ρ).1 τ
  exact ⟨h1, h2 hdr, FildR_eq (P.PD K) ρ hb.2 h τ⟩

end GlobalTheory.Per.DdREqDcris

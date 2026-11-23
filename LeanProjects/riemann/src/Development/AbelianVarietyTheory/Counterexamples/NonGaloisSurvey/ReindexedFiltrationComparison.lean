import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DualExactSequence
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKsOfFinExt
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq

noncomputable section

namespace GlobalTheory.Survey.SlowDecayFunctions

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence

def slow (a : ℤ) : ℤ := if 0 ≤ a then a else (a + 1) / 2

theorem slow_add (a b : ℤ) : slow (a + b) ≤ slow a + slow b := by
  unfold slow; split_ifs <;> omega

theorem slow_mono (a : ℤ) : slow a ≤ slow (a + 1) := by
  unfold slow; split_ifs <;> omega

theorem slow_surj (a : ℤ) : ∃ b, slow b = a := by
  by_cases h : 0 ≤ a
  · exact ⟨a, by simp [slow, h]⟩
  · exact ⟨2 * a, by unfold slow; split_ifs <;> omega⟩

section Datum

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

theorem fil_antitone (PD : PeriodData G Qp K₀ K B BdR) : Antitone PD.Fil :=
  antitone_int_of_succ_le PD.Fil_anti

def slowPD (PD : PeriodData G Qp K₀ K B BdR) : PeriodData G Qp K₀ K B BdR :=
  { PD with
    Fil := fun a => PD.Fil (slow a)
    Fil_anti := fun a => fil_antitone PD (slow_mono a)
    one_mem := PD.one_mem
    Fil_mul := fun a b x y hx hy => fil_antitone PD (slow_add a b) (PD.Fil_mul _ _ x y hx hy)
    Fil_exh := fun x => by
      obtain ⟨a, ha⟩ := PD.Fil_exh x
      obtain ⟨b, rfl⟩ := slow_surj a
      exact ⟨b, ha⟩
    Fil_sep := fun x hx => PD.Fil_sep x fun a => by
      obtain ⟨b, rfl⟩ := slow_surj a
      exact hx b
    Fil_G := fun g a x hx => PD.Fil_G g _ x hx
    mem_filtration_one := PD.mem_filtration_one
    not_mem_filtration_two := PD.not_mem_filtration_two
    fund := PD.fund }

end Datum

variable {l : ℕ} [Fact l.Prime]

def slowly (P : LocPrime l) : LocPrime l :=
  { P with
    PD := fun K => slowPD (P.PD K)
    PD_p := P.PD_p
    PD_actB := P.PD_actB
    PD_actdR := P.PD_actdR
    PD_φ := P.PD_φ
    PD_ι := P.PD_ι
    period_datum_t_eq := P.period_datum_t_eq
    PD_χ := P.PD_χ
    PD_Fil := fun K K' a => P.PD_Fil K K' (slow a)
    PD_σ := P.PD_σ }

def slowA {P : LocPrime l} (AI : LocAinf l P) : LocAinf l (slowly P) :=
  { actC := AI.actC, actC_ext := AI.actC_ext, actC_norm := AI.actC_norm, actT := AI.actT
    actT_coeff := AI.actT_coeff, ζ := AI.ζ, ζ_zero := AI.ζ_zero, ζ_succ := AI.ζ_succ, ζ_one := AI.ζ_one
    ε := AI.ε, ε_coeff := AI.ε_coeff, ιA := AI.ιA, ιA_inj := AI.ιA_inj, ιA_act := AI.ιA_act
    ιA_φ := AI.ιA_φ, ζ_eq := AI.ζ_eq, ainf_image_mem_filtration_zero := AI.ainf_image_mem_filtration_zero, ainf_image_mem_filtration_one_iff := AI.ainf_image_mem_filtration_one_iff
    ιA_teich := AI.ιA_teich }

theorem not_jump_neg_one (P : LocPrime l) {K LL : FinExt l} (T : Lat K LL) (τ : Emb K LL) :
    ¬ IsJumpV ((slowly P).PD K) T.ρ τ (-1) := fun h => h rfl

theorem not_twistJumps (P : LocPrime l) {K LL : FinExt l} {s : ℕ} (h : Good K s LL) (T T' : Lat K LL)
    (e : IsTwistRep (cycLL (P.PD K) ↥LL.1) T.ρ T'.ρ) (hT : IsDR (P.PD K) T.ρ) (τ : Emb K LL)
    (h0 : IsJumpV (P.PD K) T.ρ τ 0) : ¬ TwistJumps l (slowly P) := fun H =>
  not_jump_neg_one P T' τ (((H K s LL h T T' e hT).2 τ 0).1.2 h0)

theorem not_deRhamComparison (P : LocPrime l) {K LL : FinExt l} {s : ℕ} (h : Good K s LL)
    (T T' : Lat K LL) (e : IsTwistRep (cycLL (P.PD K) ↥LL.1) T.ρ T'.ρ) (hT : IsDR (P.PD K) T.ρ)
    (τ : Emb K LL) (h0 : IsJumpV (P.PD K) T.ρ τ 0) : ¬ DeRhamComparison l (slowly P) := fun H =>
  not_twistJumps P h T T' e hT τ h0 H.2.2.2.2.2.2.2.2.1

def lineLat (K LL : FinExt l) (ψ : ↥(GK K) →* (↥LL.1)ˣ)
    (hψ : ∀ g, ((ψ g : (↥LL.1)ˣ) : ↥LL.1) ∈ OL LL)
    (hc : Continuous fun g => ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) : Lat K LL where
  V := ↥LL.1
  ρ := charRep ψ
  cont := fun _ => hc.mul continuous_const
  L := GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.charLat Subtype.val_injective ψ fun g => ⟨⟨_, hψ g⟩, rfl⟩

def trivLat (K LL : FinExt l) : Lat K LL :=
  lineLat K LL 1 (fun _ => (OL LL).one_mem) continuous_const

theorem continuous_cyc (P : LocPrime l) (K LL : FinExt l) :
    Continuous fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) := by
  have h := (GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.1
  have e : (fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1)) =
      fun g : ↥(GK K) => algebraMap ℚ_[l] ↥LL.1 (P.χQ (g : GQ l) : ℚ_[l]) := by
    funext g
    change algebraMap ℚ_[l] ↥LL.1 (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = _
    rw [P.PD_χ]
  rw [e]
  refine Continuous.subtype_mk (f := fun g : ↥(GK K) =>
    algebraMap ℚ_[l] (Om l) (P.χQ (g : GQ l) : ℚ_[l])) ?_ _
  exact (continuous_algebraMap ℚ_[l] (Om l)).comp (h.comp continuous_subtype_val)

def tateLat (P : LocPrime l) (K LL : FinExt l) : Lat K LL :=
  lineLat K LL (cycLL (P.PD K) ↥LL.1) (GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.cyc_mem P K LL) (continuous_cyc P K LL)

theorem twist_triv (P : LocPrime l) (K LL : FinExt l) :
    IsTwistRep (cycLL (P.PD K) ↥LL.1) (trivLat K LL).ρ (tateLat P K LL).ρ :=
  ⟨LinearEquiv.refl _ _, fun g x => by
    change ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) * (show ↥LL.1 from x) =
      ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) * (1 * (show ↥LL.1 from x))
    rw [one_mul]⟩

section Triv

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    (LL : Type) [Field LL] [Algebra Qp LL]

theorem one_notMem : (1 : BdR) ∉ PD.Fil 1 := fun h =>
  PD.not_mem_filtration_two (by simpa using PD.Fil_mul 1 1 _ _ h PD.mem_filtration_one)

def incK : LL ⊗[Qp] K →ₗ[LL] LL ⊗[Qp] BdR :=
  AlgebraTensorModule.map LinearMap.id (IsScalarTower.toAlgHom Qp K BdR).toLinearMap

theorem ddR_triv : DdR PD (charRep (1 : G →* LLˣ)) =
    LinearMap.range (incK (Qp := Qp) (K := K) (BdR := BdR) LL) := by
  classical
  apply le_antisymm
  · intro x hx
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx
    let b := Module.Basis.ofVectorSpace Qp LL
    let e := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) b
    have he : ∀ g y i, e (actVdR PD (charRep (1 : G →* LLˣ)) g y) i = PD.actdR g (e y i) := by
      intro g y i
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v c =>
        have : ∀ (q : Qp) (z : BdR), PD.actdR g (q • z) = q • PD.actdR g z := fun q z =>
          ((PD.actdR g).toLinearMap.restrictScalars Qp).map_smul q z
        simp [e, actVdR, charRep, this]
      | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb]
    have hx' : x = (e x).sum fun i c => b i ⊗ₜ[Qp] c := by
      rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
      exact (e.symm_apply_apply x).symm
    rw [hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := PD.invdR (e x i) fun g => by rw [← he, hx]
    exact ⟨b i ⊗ₜ c, by simp [incK, hc]⟩
  · rintro _ ⟨y, rfl⟩
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simp [incK, actVdR, charRep]
    | add a b ha hb => simp only [map_add, ha, hb]

theorem isDR_triv : IsDR PD (charRep (1 : G →* LLˣ)) := by
  have : Nontrivial BdR := ⟨⟨1, 0, fun h => one_notMem PD (h ▸ (PD.Fil 1).zero_mem)⟩⟩
  have hi : Function.Injective (incK (Qp := Qp) (K := K) (BdR := BdR) LL) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := LL)
      (IsScalarTower.toAlgHom Qp K BdR).toLinearMap (algebraMap K BdR).injective
  rw [IsDR, ddR_triv, LinearMap.finrank_range_of_inj hi, Module.finrank_baseChange,
    Module.finrank_self, mul_one]

theorem jump_triv (hK : Function.Surjective (algebraMap Qp K)) (τ : K →ₐ[Qp] LL) :
    IsJumpV PD (charRep (1 : G →* LLˣ)) τ 0 := by
  intro h
  have h0 : ((1 : LL) ⊗ₜ[Qp] (1 : BdR)) ∈ FildR PD (charRep (1 : G →* LLˣ)) τ 0 := by
    refine ⟨⟨?_, ?_⟩, ⟨1 ⊗ₜ ⟨1, PD.one_mem⟩, rfl⟩⟩
    · rw [ddR_triv]
      exact ⟨1 ⊗ₜ 1, by simp [incK]⟩
    · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
      intro c
      obtain ⟨q, rfl⟩ := hK c
      simp only [mulVdR, LinearMap.sub_apply, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
        LinearMap.mulLeft_apply, mul_one, LinearMap.smul_apply, AlgHom.commutes, sub_eq_zero,
        ← IsScalarTower.algebraMap_apply, algebraMap_smul]
      rw [Algebra.algebraMap_eq_smul_one, tmul_smul]
  rw [← h] at h0
  obtain ⟨y, hy⟩ := h0.2
  obtain ⟨φ, hφ⟩ : ∃ φ : LL →ₗ[Qp] Qp, φ 1 = 1 := by
    obtain ⟨φ, hφ⟩ := (Algebra.linearMap Qp LL).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.2 (algebraMap Qp LL).injective)
    exact ⟨φ, by simpa using LinearMap.congr_fun hφ 1⟩
  let m : LL ⊗[Qp] BdR →ₗ[Qp] BdR := (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ φ.rTensor BdR
  have hm : ∀ y, m (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL)
      ((PD.Fil (0 + 1)).restrictScalars Qp).subtype y) ∈ (PD.Fil (0 + 1)).restrictScalars Qp := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simpa [m] using ((PD.Fil (0 + 1)).restrictScalars Qp).smul_mem (φ v) c.2
    | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  have := hm y
  rw [hy] at this
  exact one_notMem PD (by simpa [m, hφ] using this)

end Triv

theorem not_comparison_of_surj (P : LocPrime l) {K LL : FinExt l} {s : ℕ} (h : Good K s LL)
    (hs : Function.Surjective (algebraMap ℚ_[l] ↥K.1)) (τ : Emb K LL) :
    ¬ DeRhamComparison l (slowly P) :=
  not_deRhamComparison P h (trivLat K LL) (tateLat P K LL) (twist_triv P K LL)
    (isDR_triv (P.PD K) ↥LL.1) τ (jump_triv (P.PD K) ↥LL.1 hs τ)

def botK (l : ℕ) [Fact l.Prime] : FinExt l := ⟨⊥, inferInstance⟩

theorem not_comparison_slow (P : LocPrime l) : ¬ DeRhamComparison l (slowly P) := by
  obtain ⟨LL, hL⟩ := GlobalTheory.MemLoc.exists_good_situation l (botK l) 2 (by norm_num) (fun _ => le_rfl) bot_le
  have hs : Function.Surjective (algebraMap ℚ_[l] ↥(botK l).1) := fun x =>
    ⟨IntermediateField.botEquiv ℚ_[l] (Om l) x, (IntermediateField.botEquiv ℚ_[l] (Om l)).injective (by exact (IntermediateField.botEquiv ℚ_[l] (Om l)).commutes _)⟩
  let τ : Emb (botK l) LL := (Algebra.ofId ℚ_[l] ↥LL.1).comp (IntermediateField.botEquiv ℚ_[l] (Om l)).toAlgHom
  exact not_comparison_of_surj P (hL LL le_rfl) hs τ

theorem not_forall (P : LocPrime l) (AI : LocAinf l P) :
    ¬ ∀ (P' : LocPrime l) (_ : LocAinf l P'), DeRhamComparison l P' := fun h =>
  not_comparison_slow P (h _ (slowA AI))

end GlobalTheory.Survey.SlowDecayFunctions

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleThetaKernelTameCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelVectorMovedByRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionEqZeroOfNoLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepVectorsAndAdjointVectorsAreTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebra
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BaseKernelType

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem actL_levelTrace (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (u : U)
    (hu : ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG u) κ) {F : GA D (Wc D i) → ℂ}
    (hF : HasType (Wc D i) (R.βW i) (flag1L (R.datWp i R.triv)) F) :
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG u) (levelTrace R i U ψ F) =
      D.what₂.embLL ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • levelTrace R i U ψ F := by
  have hmul : ∀ g : G, actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG u)
      (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) F) =
        actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G) * g)) F := by
    intro g
    have em : R.eG ((u : G) * g) = R.eG u * R.eG g := map_mul _ _ _
    rw [em]
    by_cases hg : ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ
    · exact GlobalTheory.ProjComm.levelGroupAction_mul_of_lifts hu hg hF
    · have hn : ¬ ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG u * R.eG g) κ := by
        rintro ⟨κ', hκ'⟩
        obtain ⟨κ, hκ⟩ := hu
        have := GlobalTheory.ProjComm.isLift_mul (GlobalTheory.ProjComm.isLift_inv hκ) hκ'
        have e : (R.eG (u : G))⁻¹ * (R.eG (u : G) * R.eG g) = R.eG g := inv_mul_cancel_left _ _
        exact hg ⟨κ⁻¹ * κ', e ▸ this⟩
      have h1 : actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) F = 0 := GlobalTheory.ProjComm.levelGroupAction_eq_zero_of_no_lift hg F
      rw [h1, map_zero]
      exact (GlobalTheory.ProjComm.levelGroupAction_eq_zero_of_no_lift hn F).symm
  unfold levelTrace gaL
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
  refine Fintype.sum_bijective (fun g => (u : G) * g) (Group.mulLeft_bijective (u : G)) _ _ fun g => ?_
  simp only [smul_smul]
  refine congrArg₂ (· • ·) ?_ (hmul g)
  split_ifs with h1 h2 h2
  · rw [← map_mul, ← Units.val_mul,
      show (⟨(u : G) * g, h2⟩ : U) = u * ⟨g, h1⟩ from rfl, map_mul, mul_inv, mul_inv_cancel_left]
  · exact absurd (U.mul_mem u.2 h1) h2
  · exact absurd ((U.mul_mem_cancel_left u.2).1 h2) h1
  · rw [mul_zero]

theorem singleSeries_hasType (hθ : IsInfFam R.θ) {χS χT : (AE D)ˣ →* Circle} {ω : WeilRep D i}
    {φ : WO (Vc D i) (Wc D i) → ℂ} (hω : IsWeilDatumO R.ψ (Vc D i) (Wc D i) χS χT ω)
    (hφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ)
    (hfix : ∀ k', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 k' → ω (1, k') φ = φ) (h : GA D (Vc D i))
    (w : (R.cV i).W) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    HasType (Wc D i) (R.βW i) (flag1L (R.datWp i R.triv)) (singleSeries R i ω φ h w v) := by
  intro κ hκ g
  have hl : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 κ := ⟨hκ.1, hκ.2.1, Subgroup.mem_bot.1 hκ.2.2⟩
  rw [GlobalTheory.CuspMult.EqCut.levChi_flag1 rfl rfl, one_mul]
  unfold singleSeries Datum.thetaKO
  have e : ((h, g * κ) : GA D (Vc D i) × GA D (Wc D i)) = (h, g) * (1, κ) := Prod.ext (mul_one h).symm rfl
  rw [e, map_mul, Module.End.mul_apply, GlobalTheory.OrientedHeis.om_fin_pureTensorO R.ψ _ _ _ _ ω hω R.θ hθ 1 (one_mem _) κ hκ.1,
    hfix κ hl]
  exact hφ

theorem adForm_sub (x y : Fin (R.nW i) → D.what₂.LL) : adForm R i (x - y) = adForm R i x - adForm R i y := by
  unfold adForm
  rw [map_sub, map_sub]

theorem thetaBase_hasType : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), R.LUnif → FormsDetermined R i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → (∀ u : F.P0, (R.FW i).chi u = 1) → ∀ x ∈ thetaBase R i F.P0 F.ψ0⁻¹ 1 v (ownAt D v), ∀ u : F.P0, (R.FW i).ρ u x = ((F.ψ0⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) • x := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hcore i hU hd v hv hmu hval hchi
  have hgen : ∀ u : F.P0, ∀ y ∈ {x | ∃ ω φ, IsKernel R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) (placesOver R (R.mu v) (ownAt D v)) ω φ ∧
      x ∈ seriesSet R i F.P0 F.ψ0⁻¹ 1 ω φ},
      (R.FW i).ρ u y = ((F.ψ0⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) • y := by
    rintro u y ⟨ω, φ, hk, h, -, w, -, hy⟩
    obtain ⟨χ, ξR, hker⟩ := GlobalTheory.T.baseTuple_thetaKernel_tameCharacter D G Pl0 T0 A Ks R F hcore i v hv hmu ω φ hk
    have hfix := (GlobalTheory.T.thetaKernel_vector_moved_by_rootsOfUnity D G Pl0 T0 A Ks R F hcore i _ χ ξR _ ω φ hker hval).2
    obtain ⟨cV, hcV⟩ := hcore.lev.βV i
    obtain ⟨cW, hcW⟩ := hcore.lev.βW i
    have hφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ :=
      (GlobalTheory.VecTheta.vecThetaSD D).2 _ _ _ _ _ _ (R.ΛV i) (R.ΛW i) _ _ _ _ _ _ _
        (GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hcore.lev.βV i)))
        (GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hcore.lev.βW i))) hcV.1 hcW.1 hker.vec
    have hT : ∀ v', HasType (Wc D i) (R.βW i) (flag1L (R.datWp i R.triv)) (singleSeries R i ω φ h w v') :=
      fun v' => GlobalTheory.BaseKernelType.singleSeries_hasType hcore.models.inf hker.weil hφ hfix h w v'
    have hρ : ∀ v' : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i ((R.FW i).ρ u y) (fun ρ => v' ρ) =
        actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG u) (adForm R i y (fun ρ => v' ρ)) := by
      intro v'
      have e := (hU i (sg0 D A)).2.2 u y
      rw [hchi u, Units.val_one, map_one, one_smul] at e
      exact congrArg (fun T => T (fun ρ => v' ρ)) e
    by_cases hu : ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG u) κ
    · refine sub_eq_zero.1 (hd _ fun v' => ?_)
      rw [GlobalTheory.BaseKernelType.adForm_sub, adForm_smul, MultilinearMap.sub_apply, MultilinearMap.smul_apply, hρ v', hy v',
        one_smul, GlobalTheory.BaseKernelType.actL_levelTrace F.P0 F.ψ0⁻¹ u hu (hT v'), sub_self]
    · have h0 : (R.FW i).ρ u y = 0 := hd _ fun v' => by
        rw [hρ v']
        exact GlobalTheory.ProjComm.levelGroupAction_eq_zero_of_no_lift hu _
      have hy0 : y = 0 := by
        have e := congrArg ((R.FW i).ρ (u : G)⁻¹) h0
        rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at e
      rw [hy0, map_zero, smul_zero]
  intro x hx u
  unfold thetaBase at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen u y hy
  | zero => rw [map_zero, smul_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb, smul_add]
  | smul a y _ hy => rw [LinearMap.map_smul_of_tower, hy, smul_comm]

end GlobalTheory.BaseKernelType

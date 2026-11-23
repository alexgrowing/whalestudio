import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeakStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdjoinSplitHeckeGeneratorsDualsSpherical
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
namespace GlobalTheory.SplitEigen

theorem adjoint_apply_of_eigen {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (A : Module.End ℂ H) (hA : Commute A (LinearMap.adjoint A)) (v : H) (μ : ℂ) (hv : A v = μ • v) :
    LinearMap.adjoint A v = starRingEnd ℂ μ • v := by
  set B : Module.End ℂ H := A - μ • 1 with hBdef
  have hBadj : LinearMap.adjoint B = LinearMap.adjoint A - starRingEnd ℂ μ • 1 := by
    rw [hBdef, map_sub, map_smulₛₗ]
    congr 2
    exact LinearMap.adjoint_id
  have hBv : B v = 0 := by
    rw [hBdef, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hv, sub_self]
  have hc : Commute B (LinearMap.adjoint B) := by
    rw [hBadj, hBdef]
    exact (hA.sub_right ((Commute.one_right A).smul_right _)).sub_left ((Commute.one_left _).smul_left _)
  have h0 : LinearMap.adjoint B v = 0 := by
    have e : inner ℂ (LinearMap.adjoint B v) (LinearMap.adjoint B v) = (0 : ℂ) := by
      rw [LinearMap.adjoint_inner_left]
      have : B (LinearMap.adjoint B v) = LinearMap.adjoint B (B v) := by
        rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply]
      rw [this, hBv, map_zero, inner_zero_right]
    exact inner_self_eq_zero.1 e
  rw [hBadj, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h0
  exact h0

theorem adjoin_scalar {M : Type} [AddCommGroup M] [Module ℂ M] (S : Set (Module.End ℂ M)) (X : Set M)
    (hS : ∀ b ∈ S, ∃ μ : ℂ, ∀ u ∈ X, b u = μ • u) : ∀ b ∈ Algebra.adjoin ℂ S, ∃ μ : ℂ, ∀ u ∈ X, b u = μ • u := by
  intro b hb
  induction hb using Algebra.adjoin_induction with
  | mem b hb => exact hS b hb
  | algebraMap r => exact ⟨r, fun u _ => Module.algebraMap_end_apply ℂ ℂ M r u⟩
  | add b b' _ _ ihb ihb' =>
    obtain ⟨μ, hμ⟩ := ihb
    obtain ⟨μ', hμ'⟩ := ihb'
    exact ⟨μ + μ', fun u hu => by rw [LinearMap.add_apply, hμ u hu, hμ' u hu, add_smul]⟩
  | mul b b' _ _ ihb ihb' =>
    obtain ⟨μ, hμ⟩ := ihb
    obtain ⟨μ', hμ'⟩ := ihb'
    exact ⟨μ * μ', fun u hu => by rw [Module.End.mul_apply, hμ' u hu, map_smul, hμ u hu, smul_smul, mul_comm]⟩

end GlobalTheory.SplitEigen

namespace GlobalTheory.SplitEigen

set_option maxHeartbeats 40000000 in

theorem label_scalar_split : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ (j : Fin D.R.m) (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j A3.A.fam.μ0).H), GlobalTheory.Hk3.IsOpsV R.toRealDat j A3.A.fam.μ0 h → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0) h → ∀ (P : Pl D.host.E), GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P → conjPl P ≠ P → ∀ d, GlobalTheory.Hk3.IsLab (Vc D j) P d → ∃ a : ℂ, ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c, h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) = a • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _hOk hC hEx _hH _hGE j c h hh hN P hP hconj d _hd
  obtain ⟨hCoreF, -, -, hOnto, -, -, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have hCore := hCoreF hEx
  have hM := hCore.models
  obtain ⟨P0, hP0, rfl⟩ := (hOnto _ hP).2 hconj
  have hsplit := (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hCore.lev hCore.fam hM).2 j A3.A.fam.μ0 h hh ⟨P0, hP0⟩
  have hK := RealDat3.kFormL_of (R := R) (F := F) hM

  have hop : ∀ k, k ≤ (Vc D j).rank → (R.toCx3 F).opLC j A3.A.fam.μ0 (Sum.inl (Sum.inl (⟨P0, hP0⟩, k))) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1)) := by
    intro k hk
    refine LinearMap.ext_on_range (hK j A3.A.fam.μ0).2 fun b => ?_
    rw [← CxData.jL_opL _ hK]
    exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) (hsplit k hk _)

  have hT : ∀ k, k ≤ (Vc D j).rank → ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
      h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) =
        cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k))) • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
    intro k hk x hx
    have e1 := (U2.mem_eigPart.1 hx) (Sum.inl (⟨P0, hP0⟩, k))
    have e2 : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (U2.liftHeckeOperators A3 (R.toCx3 F) j (Sum.inl (⟨P0, hP0⟩, k)) x) =
        h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) := by
      exact (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j A3.A.fam.μ0).H)) (LinearMap.congr_fun (hop k hk) x)).trans rfl
    rw [← e2, e1]
    exact Tw.out_smul (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j A3.A.fam.μ0).H) _ _

  have hD : ∀ k, k ≤ (Vc D j).rank → ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
      h (R.pl P0) (Finsupp.single (dualLab (splitLab (Vc D j).rank k)) 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) =
        starRingEnd ℂ (cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k)))) •
          (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
    intro k hk x hx
    have ha : LinearMap.adjoint (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1)) =
        h (R.pl P0) (Finsupp.single (dualLab (splitLab (Vc D j).rank k)) 1) := by
      rw [hN.2 _ hP]
      congr 1
      rw [Finsupp.mapRange_single, star_one, GlobalTheory.Hk3.dualC, Finsupp.mapDomain_single]
    have hc : Commute (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1))
        (LinearMap.adjoint (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1))) :=
      ha.symm ▸ hN.1 _ _ hP hP _ _
    exact (LinearMap.congr_fun ha _).symm.trans (adjoint_apply_of_eigen _ hc _ _ (hT k hk x hx))

  obtain ⟨a, ha, hae⟩ := GlobalTheory.SplitGen.gen_split (Vc D j) (R.pl P0) hconj _
    (GlobalTheory.DefiniteOps.rtr (GlobalTheory.SplitHeckeAdj.fin (Vc D j)) (R.cV j).W) d
  have key := adjoin_scalar _ {u | ∃ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
      u = (R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x)} (by
    rintro b ⟨k, hk, rfl | rfl⟩
    · refine ⟨cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k))), ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (GlobalTheory.DefiniteOps.hkF_eq (Vc D j) (R.pl P0) _ _).symm.trans ((hh _ hP _ _).symm.trans
        ((congrArg (R.HV j A3.A.fam.μ0).e (hT k hk x hx)).trans (map_smul _ _ _)))
    · refine ⟨starRingEnd ℂ (cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k)))), ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (GlobalTheory.DefiniteOps.hkF_eq (Vc D j) (R.pl P0) _ _).symm.trans ((hh _ hP _ _).symm.trans
        ((congrArg (R.HV j A3.A.fam.μ0).e (hD k hk x hx)).trans (map_smul _ _ _)))) a ha
  obtain ⟨μ, hμ⟩ := key
  refine ⟨μ, fun x hx => (hM.HV j A3.A.fam.μ0).1 ?_⟩
  have hfix : ∀ k ∈ GlobalTheory.Hk3.hyp (Vc D j) (R.pl P0), GlobalTheory.DefiniteOps.rtr (GlobalTheory.SplitHeckeAdj.fin (Vc D j)) (R.cV j).W k
      ((R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x)) =
        (R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) := by
    obtain ⟨n, hn⟩ := hCore.lev.βV j
    have hn' : IsBaseFrame (Vc D j) (R.βV j) (R.ΛV j) 1 := (one_pow n : (1 : ℕ) ^ n = 1) ▸ hn
    refine GlobalTheory.DefiniteOps.fixed_of_mem (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j A3.A.fam.μ0) hn' (R.pl P0) hP (R.cV j).coef.ρ _ ?_
    have hm := LinearMap.mem_range_self (R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x)
    rw [(hM.HV j A3.A.fam.μ0).2.1] at hm
    exact hm
  exact (hh _ hP _ _).trans ((GlobalTheory.DefiniteOps.hkF_eq _ _ _ _).trans ((hae _ hfix).symm.trans
    ((hμ _ ⟨x, hx, rfl⟩).trans (map_smul _ _ _).symm)))

end GlobalTheory.SplitEigen

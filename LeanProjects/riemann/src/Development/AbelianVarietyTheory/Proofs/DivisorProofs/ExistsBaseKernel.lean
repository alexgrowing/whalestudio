import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsResOfTameAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsConjPlOfIdemSum
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSumOfNoConj
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.OnCmp

open Classical in

theorem exists_baseKernel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → ∃ ω φ, IsBaseKernel R i v (ownAt D v) ω φ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i v hv hmu
  obtain ⟨ψw, Qw, hψ, hxi⟩ := hmu v hv
  have hL := hC.lev
  have hδ : R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v) = R.xiH (R.mu v) * ψw⁻¹ := by rw [hxi, mul_inv_cancel_right]
  have htame : ∀ P, (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).TameAt P := by
    intro P
    unfold Formalism.L2.Host.HChar.TameAt Formalism.L2.Host.HChar.LevelLe
    intro x hx hle
    rw [hδ, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, hL.xi_tame (R.mu v) P x hx hle, hψ.tame P x hx hle,
      inv_one, mul_one]
  have htriv : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).TrivOn D.host.F := by
    rw [hδ]; exact (hL.xi_triv (R.mu v)).mul hψ.triv.inv
  have hunit : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).IsUnitary := by
    obtain ⟨n, hn, hno⟩ := hL.xi_fin (R.mu v)
    obtain ⟨a, ha⟩ := hψ.ord
    refine Formalism.L2.Host.HChar.isUnitary_of_order (n := n * Formalism.EigenvalueLevelCeiling.plc v ^ a)
      (Nat.mul_pos hn (pow_pos (Formalism.EigenvalueLevelCeiling.plc_prime v).pos a)) ?_
    show _ ^ (n * _) = 1
    rw [hδ, mul_pow, inv_pow, pow_mul, hno, one_pow, one_mul, mul_comm n, pow_mul, ha, one_pow, inv_one]
  obtain ⟨χ, hχ⟩ := GlobalTheory.CharTransport.exists_chrEq D _ hunit
  have hF : ∀ a, χ (idF D a) = 1 := GlobalTheory.GridWeil.triv_base hχ htriv
  have hr0 : ResEta D χ 0 := ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun _ _ a => by rw [hF a, pow_zero]⟩
  have h0 := hC.thP.ωP i A.μ0
  obtain ⟨ω, hω, -⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D R.ψ h0.std _ _ _ _ χ χ _ h0 hχ.1 hχ.1 hr0 hr0
  have hx0 : R.xi A.μ0 = 1 :=
    MonoidHom.ext fun x => GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0) x
  have hω' : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ω := by
    convert hω using 2
    · simp only [Lift.chrTh, Lift.tup, LevCh.mu, hx0, mul_one]
    · simp only [Lift.chrTh, Lift.tup, LevCh.mu, hx0, mul_one]
      exact mul_right_comm _ _ _
  choose ξR hξR using fun PP => GlobalTheory.exists_isRes_of_tameAt D _ PP (htame PP)
  have hsub : placesOver R (R.mu v) (ownAt D v) ⊆ R.Q (R.mu v) := Finset.filter_subset _ _
  obtain ⟨e0, he0, -⟩ := (hC.thP.vP i (R.mu v)).2
  have hsub' : R.Pg ∪ placesOver R (R.mu v) (ownAt D v) ⊆ R.Pg ∪ R.Q (R.mu v) := Finset.union_subset_union le_rfl hsub
  have hnc : ∀ P ∈ R.Pg ∪ placesOver R (R.mu v) (ownAt D v), ∀ P' ∈ R.Pg ∪ placesOver R (R.mu v) (ownAt D v),
      ¬ Lev.IsConjPl P P' := fun P hP P' hP' =>
    GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he0 P (hsub' hP) P' (hsub' hP')
  obtain ⟨cV, hcV⟩ := hL.βV i
  obtain ⟨cW, hcW⟩ := hL.βW i
  obtain ⟨φ, hφ⟩ := GlobalTheory.PlaceVec.thPVecExists D R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i)
    (R.ΛW i) (R.βV i) (R.βW i) R.Pg (placesOver R (R.mu v) (ownAt D v)) ξR (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcV)
    (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcW) hcV.1 hcW.1 ((Formalism.IndefR.Fin.disjoint_Pg_Q R.toLevCh hL (R.mu v)).mono_right hsub)
    (Formalism.IndefR.Fin.idemSum_of_noConj _ hnc) (R.vacP i) (hC.thP.vP i (R.mu v)).1
  refine ⟨ω, φ, ?_⟩
  unfold IsBaseKernel IsKernel
  exact ⟨χ, ξR, hχ, fun PP _ => hξR PP, hω', hφ⟩

end GlobalTheory.OnCmp

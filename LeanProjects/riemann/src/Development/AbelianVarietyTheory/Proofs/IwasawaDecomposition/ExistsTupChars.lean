import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.TupChar

theorem chrEq_mul {D : D7} {c c' : IdC D} {χ χ' : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => (congrArg₂ (· * ·) (h.1.2 x) (h'.1.2 x)).trans (mul_one _)⟩,
    fun P e he k x hx => ?_⟩
  rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx, ← Units.val_mul]
  rfl

theorem unramEverywhere {D : D7} {c : IdC D} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) (hu : ∀ P, χ.UnrAt P) :
    UnramEverywhere D c := fun x hx h4 h5 => by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  apply Circle.ext
  rw [GlobalTheory.Mem.EtaTilde.val_finite D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc hu x hx, Circle.coe_one,
    Units.val_eq_one]
  refine finprod_eq_one_of_forall_eq_one fun P => ?_
  have e := GlobalTheory.Mem.EtaTilde.val_mul_inv (RingHom.id _) P (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := e
  have e1 : Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    refine le_antisymm ((h2 _).1 h4 P) ?_
    rw [← e']
    exact mul_le_of_le_one_right' ((h2 _).1 h5 P)
  rw [e1, WithZero.log_one, neg_zero, zpow_zero]

theorem exists_tupChars : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E), (∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n) → (∀ μ, (xi μ).TrivOn D.host.F) → ∃ (chr : D.what₂.Tup → ℕ → IdC D) (eta : IdC D), (∀ μ j, IsHC D (chr μ j)) ∧ (∀ μ (j : Fin D.R.m) τ, HasInfExp D (chr μ (j.1 + 1)) τ (-(D.hc τ).e j)) ∧ (∀ μ j, 1 ≤ j → j ≤ D.R.m → ResEta D (chr μ j) 0) ∧ IsHeckeChar D eta ∧ (∀ τ, HasInfExp D eta τ (1 / 2)) ∧ ResEta D eta 1 ∧ UnramEverywhere D eta ∧ (∀ μ (j : Fin D.R.m), Formalism.IndefR.Links.ChrEq (chr μ (j.1 + 1)) (C.mu0 j * xi μ)) ∧ Formalism.IndefR.Links.ChrEq eta C.eta := by
  intro D C xi hfin htriv
  classical
  choose n hn ho using hfin
  choose m hm using fun j => GlobalTheory.CharTransport.exists_chrEq D (C.mu0 j) (C.isMu0 j).unitary
  choose x hx using fun μ => GlobalTheory.CharTransport.exists_chrEq D (xi μ) (Formalism.L2.Host.HChar.isUnitary_of_order (hn μ) (ho μ))
  obtain ⟨η, hη⟩ := GlobalTheory.CharTransport.exists_chrEq D C.eta C.isEta.unitary
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D η C.eta hη C.isEta
  have hexp : ∀ μ (j : Fin D.R.m) τ, HasInfExp D (m j * x μ) τ (-(D.hc τ).e j) := fun μ j τ => by
    have := GlobalTheory.Chain.StepVac.hasInfExp_mul (GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hm j)
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (C.isMu0 j).inf) τ)
      (GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hx μ) (hn μ) (ho μ) τ)
    rwa [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this
  let chr : D.what₂.Tup → ℕ → IdC D := fun μ j =>
    if h : 1 ≤ j ∧ j ≤ D.R.m then m ⟨j - 1, by omega⟩ * x μ else 1
  have hchr : ∀ μ (j : Fin D.R.m), chr μ (j.1 + 1) = m j * x μ := fun μ j =>
    dif_pos (⟨Nat.le_add_left _ _, j.2⟩ : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ D.R.m)
  refine ⟨chr, η, fun μ j => ?_, fun μ j τ => hchr μ j ▸ hexp μ j τ, fun μ j h1 h2 => ?_, hη.1, fun τ => ?_,
    ⟨⟨_, hres⟩, fun η' h' a => ?_⟩, unramEverywhere hη C.isEta.unr, fun μ j => hchr μ j ▸ chrEq_mul (hm j) (hx μ), hη⟩
  · by_cases h : 1 ≤ j ∧ j ≤ D.R.m
    · rw [show chr μ j = _ from dif_pos h]
      exact ⟨(chrEq_mul (hm _) (hx μ)).1, fun τ => ⟨_, hexp μ _ τ⟩⟩
    · rw [show chr μ j = _ from dif_neg h]
      exact isHC_one D
  · rw [show chr μ j = _ from dif_pos ⟨h1, h2⟩]
    refine ⟨⟨_, hres⟩, fun η' _ a => ?_⟩
    rw [pow_zero, MonoidHom.mul_apply, GlobalTheory.GridWeil.triv_base (hm _) (C.isMu0 _).triv a,
      GlobalTheory.GridWeil.triv_base (hx μ) (htriv μ) a, mul_one]
  · exact GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hη
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, C.isEta.inf⟩) τ
  · rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique h' hres, pow_one, MonoidHom.comp_apply]

end GlobalTheory.Mem.TupChar
